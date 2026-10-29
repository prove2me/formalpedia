-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_5_7_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:36:25.090192+00:00
-- url     : https://prove2.me/submissions/ce18beeb-0e32-41dd-bf47-6e4f3d8618cf

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 5 7 (RowCompute.rows[3]!) =
    (50932529603893774815823364097813077314064220530776473600000 : ℤ) := by
  decide +kernel
