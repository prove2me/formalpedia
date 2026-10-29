-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_5_11_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:38:50.840786+00:00
-- url     : https://prove2.me/submissions/453e7479-919a-4828-8d8d-a46804adc1c7

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 5 11 (RowCompute.rows[2]!) =
    (994927443321543886202703470953568392558191597923585753088000000 : ℤ) := by
  decide +kernel
