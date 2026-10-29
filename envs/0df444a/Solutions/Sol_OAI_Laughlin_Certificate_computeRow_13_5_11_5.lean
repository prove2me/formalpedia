-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_11_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:42:58.611037+00:00
-- url     : https://prove2.me/submissions/e8a04377-5bfc-41f3-b0d8-a8829b9862e7

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 11 (RowCompute.rows[5]!) =
    (71429140911551364725902464041857591832840461130158571520000000 : ℤ) := by
  decide +kernel
