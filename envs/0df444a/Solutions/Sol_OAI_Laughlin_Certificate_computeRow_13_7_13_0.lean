-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_7_13_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:27:32.963249+00:00
-- url     : https://prove2.me/submissions/4f73563c-28de-4c1c-b865-37c3aafc5ad3

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 7 13 (RowCompute.rows[0]!) =
    (5031357860595228730543907274049083300563198551166426284032000000 : ℤ) := by
  decide +kernel
