-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_7_13_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:45:24.331857+00:00
-- url     : https://prove2.me/submissions/786bf91c-7ed1-4eae-ab20-27f0671b07d4

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 7 13 (RowCompute.rows[6]!) =
    (-38044737944059463839114252014535403535835224373884616704000000 : ℤ) := by
  decide +kernel
