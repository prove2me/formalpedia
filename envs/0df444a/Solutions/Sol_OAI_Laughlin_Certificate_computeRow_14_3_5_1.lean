-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:42:48.139376+00:00
-- url     : https://prove2.me/submissions/ef5514b5-330c-401a-986e-57b0f23a3127

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 5 (RowCompute.rows[1]!) =
    (-1586620086079371150459393176780909755774746960743890944000000 : ℤ) := by
  decide +kernel
