-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_9_13_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:37:37.747365+00:00
-- url     : https://prove2.me/submissions/8e0ec8c2-ccf7-4c0f-a38b-40d19b554abd

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 9 13 (RowCompute.rows[2]!) =
    (4714015706022258486129058543284487090254013893838016348160000000 : ℤ) := by
  decide +kernel
