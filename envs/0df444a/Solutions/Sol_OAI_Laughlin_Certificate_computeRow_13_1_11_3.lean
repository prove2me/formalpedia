-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_11_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:46:22.423426+00:00
-- url     : https://prove2.me/submissions/669effdf-b804-49ce-b999-937d91aae4f3

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 11 (RowCompute.rows[3]!) =
    (-1084675520649604967426149027551737089991775260039605911552000000 : ℤ) := by
  decide +kernel
