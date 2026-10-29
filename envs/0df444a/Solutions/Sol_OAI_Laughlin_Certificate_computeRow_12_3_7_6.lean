-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_3_7_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:34:32.343824+00:00
-- url     : https://prove2.me/submissions/61aa3fbe-26e3-4908-862e-2b0e1c1efc6d

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 3 7 (RowCompute.rows[6]!) =
    (-811496389018042473908466019659981780491217491447513088000000 : ℤ) := by
  decide +kernel
