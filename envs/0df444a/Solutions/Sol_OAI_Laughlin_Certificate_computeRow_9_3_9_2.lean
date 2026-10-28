-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_3_9_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:10:36.507569+00:00
-- url     : https://prove2.me/submissions/6fdcbe4b-feef-4e9a-9d69-9335035d4b56

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 3 9 (RowCompute.rows[2]!) =
    (1656478785295646606208728126073973718799401447138210611200000 : ℤ) := by
  decide +kernel
