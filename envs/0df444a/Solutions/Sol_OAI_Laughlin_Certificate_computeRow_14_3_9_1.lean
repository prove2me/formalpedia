-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_9_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:27:37.51287+00:00
-- url     : https://prove2.me/submissions/f1dbd3bc-9f10-435d-b5f9-dd5f38f70449

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 9 (RowCompute.rows[1]!) =
    (-82320845073480523974025836290984134969852493920468992000000 : ℤ) := by
  decide +kernel
