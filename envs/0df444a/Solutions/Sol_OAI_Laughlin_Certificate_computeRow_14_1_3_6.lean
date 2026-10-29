-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_3_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:47:16.045448+00:00
-- url     : https://prove2.me/submissions/15706efa-cf78-4a2b-8c42-38f6b7fe464f

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 3 (RowCompute.rows[6]!) =
    (-147204279897090813917072123318852028777863839435701878784000000 : ℤ) := by
  decide +kernel
