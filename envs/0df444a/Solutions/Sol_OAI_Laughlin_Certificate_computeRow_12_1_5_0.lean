-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_1_5_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:13:58.625565+00:00
-- url     : https://prove2.me/submissions/827b138c-7c26-4df4-915f-50ec163f4d8d

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 1 5 (RowCompute.rows[0]!) =
    (-111897463531216065347825725163310814981076151126278012928000000 : ℤ) := by
  decide +kernel
