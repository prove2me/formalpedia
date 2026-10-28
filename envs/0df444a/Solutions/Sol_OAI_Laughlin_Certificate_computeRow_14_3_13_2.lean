-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_13_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:10:38.501023+00:00
-- url     : https://prove2.me/submissions/7f5350f8-be12-46cc-a6c3-26c28943bb57

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 13 (RowCompute.rows[2]!) =
    (13332788126813544673541181002151774515978622289511662485504000000 : ℤ) := by
  decide +kernel
