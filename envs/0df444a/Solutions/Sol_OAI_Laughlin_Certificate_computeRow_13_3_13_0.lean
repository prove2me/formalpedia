-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_13_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:45:18.072873+00:00
-- url     : https://prove2.me/submissions/c71432f9-c13e-450a-9f1c-d2cbdd465ae1

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 13 (RowCompute.rows[0]!) =
    (6049581004052636834600815681523089206584294108828333506560000000 : ℤ) := by
  decide +kernel
