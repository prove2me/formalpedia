-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_9_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:37:26.039542+00:00
-- url     : https://prove2.me/submissions/18d41138-b6a2-4480-9678-7d5b6cecb506

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 9 (RowCompute.rows[2]!) =
    (85594378541898811334477905380138475275652832004038197248000000 : ℤ) := by
  decide +kernel
