-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_7_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:31:45.682286+00:00
-- url     : https://prove2.me/submissions/0572a0d4-9bbd-4063-b7a7-a2f4488ba06e

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 7 (RowCompute.rows[4]!) =
    (-43958059799889137149669216235198830382332728818345705472000000 : ℤ) := by
  decide +kernel
