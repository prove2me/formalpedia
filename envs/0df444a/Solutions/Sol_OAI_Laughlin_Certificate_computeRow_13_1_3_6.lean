-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_3_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:36:39.305336+00:00
-- url     : https://prove2.me/submissions/3506174b-77b5-4f4f-ab28-d2dd9e868fe9

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 3 (RowCompute.rows[6]!) =
    (5977856520682588867619184715007767160076979600808214528000000 : ℤ) := by
  decide +kernel
