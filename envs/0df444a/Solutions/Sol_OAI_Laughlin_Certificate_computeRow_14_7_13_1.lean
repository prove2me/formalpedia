-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_7_13_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:42:51.364182+00:00
-- url     : https://prove2.me/submissions/b451afd1-2344-40a5-a583-783260ebe5ff

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 7 13 (RowCompute.rows[1]!) =
    (-10883567678917448069430739951931047678669392684968312832000000 : ℤ) := by
  decide +kernel
