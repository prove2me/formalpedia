-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_9_9_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:46:16.009983+00:00
-- url     : https://prove2.me/submissions/4bd96b59-ba23-4fc5-b6f5-9b21cb6c66c9

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 9 9 (RowCompute.rows[5]!) =
    (-11295174488560837953180698700487742287207167886346315366400000 : ℤ) := by
  decide +kernel
