-- Prove2me | solution 2 for OAI.Laughlin.Certificate.computeRow_12_3_9_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:44:09.394361+00:00
-- url     : https://prove2.me/submissions/942d2b6f-71a2-48d1-89b7-8d7c92e4f560

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 3 9 (RowCompute.rows[3]!) =
    (-20883250032243841110909611672794518951974584419128180736000000 : ℤ) := by
  decide +kernel
