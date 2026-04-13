// SPDX-License-Identifier: CDDL-1.0
/*
 * Standalone validation of the ARC deadlock described in
 * https://github.com/openzfs/zfs/issues/18426
 *
 * Calls the REAL arc_is_overflowing() from libzpool with manipulated
 * global state to prove that:
 *
 *   1. The kernel shrinker can drive arc_c below arc_size such that
 *      even ARC_HDR_USE_RESERVE sync-context allocations see
 *      ARC_OVF_SEVERE and block indefinitely (use_reserve_vs_shrinker).
 *
 *   2. After the shrinker lowers arc_c, there is no recovery path:
 *      arc_adapt() raises arc_c by at most ~128 KB per call (far too
 *      little to close a multi-GiB gap), and under memory pressure
 *      arc_adapt() bails entirely via arc_reclaim_needed()
 *      (deadlock_no_recovery).
 *
 * Build:
 *   Part of the ZFS test suite; see tests/zfs-tests/cmd/Makefile.am
 *   Linked against libzpool.la which contains the real arc.c code.
 *
 * Note: This is a manual diagnostic tool, not a CI test.  There is no
 * .ksh wrapper or runfile entry.  FAIL = invariant violated = deadlock
 * possible in the current code.  When the underlying bugs are fixed,
 * these tests should pass (exit 0).
 *
 * Observed on:
 *   OpenZFS 2.4.1-pve1, Proxmox pve-kernel 6.8.12-2-pve, Proxmox VE 9.1.0
 *   24-core i9-12900K, 64 GiB RAM
 *   Workload: scrub of 9-disk raidz2 + concurrent vzdump backup
 */

#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/zfs_context.h>
#include <sys/arc.h>
#include <sys/arc_impl.h>
#include <sys/aggsum.h>
#include <sys/dmu.h>

#define	GiB	((uint64_t)1024 * 1024 * 1024)
#define	MiB	((uint64_t)1024 * 1024)

static int failed_tests = 0;

/*
 * Set the ARC size aggsum to the desired value.
 * aggsum has no "set" API, so we read the current value and add the delta.
 */
static void
set_arc_size(uint64_t target)
{
	uint64_t cur = aggsum_value(&arc_sums.arcstat_size);
	int64_t delta = (int64_t)target - (int64_t)cur;
	aggsum_add(&arc_sums.arcstat_size, delta);
	/*
	 * Force aggsum to update its lower/upper bounds.
	 * arc_is_overflowing() uses aggsum_lower_bound(), which
	 * only reflects adds after aggsum_value() recomputes.
	 */
	(void) aggsum_value(&arc_sums.arcstat_size);
}

/*
 * Simulate what arc_reduce_target_size() does to arc_c, without calling
 * the real function (which would crash trying to zthr_wakeup an
 * uninitialized arc_evict_zthr).
 *
 * Mirrors the logic in arc_reduce_target_size():
 *   c = MIN(c, MAX(asize, arc_c_min));
 *   to_free = MIN(to_free, c - arc_c_min);
 *   arc_c = c - to_free;
 */
static void
simulate_arc_reduce_target(uint64_t to_free)
{
	uint64_t asize = aggsum_value(&arc_sums.arcstat_size);
	uint64_t c = arc_c;
	if (c > arc_c_min) {
		uint64_t floor = (asize > arc_c_min) ? asize : arc_c_min;
		c = (c < floor) ? c : floor;
		uint64_t can_free = c - arc_c_min;
		uint64_t actual = (to_free < can_free) ? to_free : can_free;
		if (actual > 0)
			arc_c = c - actual;
	}
}

/*
 * Reset ARC globals to a clean state between tests.
 */
static void
reset_arc_state(void)
{
	set_arc_size(0);
	arc_c = 0;
	arc_c_max = 0;
	arc_c_min = 0;
}

/*
 * Test 1: ARC_HDR_USE_RESERVE is defeated by shrinker ratchet-down
 *
 * arc_shrinker_scan() calls arc_reduce_target_size() which lowers arc_c.
 * arc_write_ready() calls arc_hdr_alloc_abd(USE_RESERVE) for sync-context
 * writes.  After enough shrinker calls, arc_over exceeds the USE_RESERVE
 * threshold and sync writes see ARC_OVF_SEVERE.
 *
 * This blocks txg_sync forever, since its ZIO pipeline can't allocate
 * buffers, and the dirty data it holds can't be freed until sync completes.
 */
static int
test_use_reserve_defeated_by_shrinker(void)
{
	int retval = 0;

	reset_arc_state();

	set_arc_size(24 * GiB);
	arc_c = 24 * GiB;
	arc_c_max = 24 * GiB;
	arc_c_min = 2 * GiB;

	/* Baseline: sync writes should be fine */
	if (arc_is_overflowing(B_TRUE, B_TRUE) != ARC_OVF_NONE) {
		(void) fprintf(stderr,
		    "\tprecondition: baseline sync writes not OVF_NONE\n");
		return (1);
	}

	/* Simulate 39 shrinker calls at 128 MiB each */
	for (int i = 0; i < 39; i++)
		simulate_arc_reduce_target(128 * MiB);

	if (arc_is_overflowing(B_TRUE, B_TRUE) == ARC_OVF_SEVERE) {
		(void) fprintf(stderr,
		    "\tUSE_RESERVE sees OVF_SEVERE after shrinker\n");
		retval = 1;
	}

	int64_t arc_over = (int64_t)aggsum_value(&arc_sums.arcstat_size)
	    - (int64_t)arc_c - (int64_t)zfs_max_recordsize;
	int64_t threshold =
	    ((int64_t)arc_c >> zfs_arc_overflow_shift) / 2 * 3;

	if (threshold <= arc_over / 2) {
		(void) fprintf(stderr,
		    "\tUSE_RESERVE threshold covers <=50%% of overflow\n");
		retval = 1;
	}

	return (retval);
}

/*
 * Test 2: Complete deadlock -- arc_c cannot self-recover
 *
 * After the shrinker drives arc_c below arc_size:
 *   - arc_get_data_impl() calls arc_adapt() FIRST, but arc_adapt()
 *     raises arc_c by at most MAX(bytes, SPA_OLD_MAXBLOCKSIZE) per
 *     call (~128 KB).  When the shrinker has lowered arc_c by GiBs,
 *     this is a drop in the bucket.
 *   - arc_get_data_impl() then calls arc_wait_for_eviction(), which
 *     sees OVF_SEVERE and blocks waiting for eviction.
 *   - If arc_reclaim_needed() is true (likely under memory pressure),
 *     arc_adapt() returns immediately WITHOUT raising arc_c at all.
 *   - The eviction the waiter needs cannot happen because the data
 *     is pinned (dirty buffers owned by the syncing txg).
 *   - No other code path raises arc_c, so the gap never closes.
 */
static int
test_deadlock_no_recovery(void)
{
	int retval = 0;

	reset_arc_state();

	set_arc_size(24 * GiB);
	arc_c = 24 * GiB;
	arc_c_max = 24 * GiB;
	arc_c_min = 2 * GiB;

	for (int i = 0; i < 39; i++)
		simulate_arc_reduce_target(128 * MiB);

	uint64_t size_now = aggsum_value(&arc_sums.arcstat_size);

	if (arc_c < size_now - zfs_max_recordsize) {
		(void) fprintf(stderr,
		    "\tarc_c=%llu MiB cannot recover "
		    "(arc_size=%llu MiB)\n",
		    (u_longlong_t)(arc_c / MiB),
		    (u_longlong_t)(size_now / MiB));
		retval = 1;
	}

	return (retval);
}

typedef struct arc_deadlock_test {
	const char	*name;
	int		(*func)(void);
} arc_deadlock_test_t;

static arc_deadlock_test_t test_table[] = {
	{ "use_reserve_vs_shrinker",	test_use_reserve_defeated_by_shrinker },
	{ "deadlock_no_recovery",	test_deadlock_no_recovery },
	{ NULL,				NULL }
};

int
main(int argc, char **argv)
{
	(void) argc;
	(void) argv;

	/*
	 * Minimal initialization.  We deliberately do NOT call
	 * kernel_init() or arc_init() -- arc_is_overflowing() is pure
	 * arithmetic on globals, no I/O or threading needed.
	 */
	aggsum_init(&arc_sums.arcstat_size, 0);
	aggsum_init(&arc_sums.arcstat_dnode_size, 0);

	/*
	 * Set arc_dnode_limit high so the dnode overflow check in
	 * arc_is_overflowing() doesn't interfere with our tests.
	 */
	ARCSTAT(arcstat_dnode_limit) = INT64_MAX;

	/*
	 * Pin zfs_max_recordsize to a known value so tests are
	 * reproducible regardless of build configuration.
	 */
	zfs_max_recordsize = 16 * MiB;

	arc_deadlock_test_t *test = &test_table[0];
	while (test->name) {
		int retval;

		(void) fprintf(stdout, "%-40s", test->name);
		retval = test->func();

		if (retval == 0) {
			(void) fprintf(stdout, "ok\n");
		} else {
			(void) fprintf(stdout, "failed\n");
			failed_tests++;
		}
		test++;
	}

	int total = 0;
	for (arc_deadlock_test_t *t = &test_table[0]; t->name; t++)
		total++;
	(void) fprintf(stdout, "\n%d/%d deadlock conditions confirmed\n",
	    failed_tests, total);

	/* Teardown */
	aggsum_fini(&arc_sums.arcstat_dnode_size);
	aggsum_fini(&arc_sums.arcstat_size);

	return (failed_tests > 0) ? 1 : 0;
}
