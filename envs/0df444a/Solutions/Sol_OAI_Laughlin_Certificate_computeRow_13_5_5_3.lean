-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:47:19.98799+00:00
-- url     : https://prove2.me/submissions/1757fc84-231a-4ac8-a8a9-8a0d03e08346

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 5 (RowCompute.rows[3]!) =
    (9742747934958518329928829132741852682516441982702714880000000 : ℤ) := by
  decide +kernel
