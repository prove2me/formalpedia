-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_3_9_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:10:39.602512+00:00
-- url     : https://prove2.me/submissions/80552f5a-c3d8-4721-be24-37221e8dc26e

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 10 3 9 (RowCompute.rows[2]!) =
    (3391221475395966827639505721680643127647982444694680371200000 : ℤ) := by
  decide +kernel
