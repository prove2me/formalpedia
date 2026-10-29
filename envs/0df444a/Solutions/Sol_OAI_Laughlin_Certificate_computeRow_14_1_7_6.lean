-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_7_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:44:07.303285+00:00
-- url     : https://prove2.me/submissions/8cb31083-3af4-4051-bd90-34c9e44cb40d

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 7 (RowCompute.rows[6]!) =
    (-378817273286232008851574115957177822871321865082365804544000000 : ℤ) := by
  decide +kernel
