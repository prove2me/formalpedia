-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_7_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:27:44.242573+00:00
-- url     : https://prove2.me/submissions/761f511c-3c97-474f-8874-53fd317d933e

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 7 (RowCompute.rows[1]!) =
    (14988968789586153053418185206852807303768287397715902464000000 : ℤ) := by
  decide +kernel
