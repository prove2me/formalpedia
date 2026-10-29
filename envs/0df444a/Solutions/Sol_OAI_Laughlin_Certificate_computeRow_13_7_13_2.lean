-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_7_13_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:34:27.306589+00:00
-- url     : https://prove2.me/submissions/0b31f829-81cd-41ba-b308-f392afe71d2f

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 7 13 (RowCompute.rows[2]!) =
    (113111193926402080814156864030539788927851744784600268800000000 : ℤ) := by
  decide +kernel
