-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_7_11_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:42:43.567507+00:00
-- url     : https://prove2.me/submissions/acffaeab-dcee-432f-9c66-9b16bed37eed

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 7 11 (RowCompute.rows[5]!) =
    (-27832655299409032791538047642382013984417453359906160640000000 : ℤ) := by
  decide +kernel
