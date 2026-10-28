-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:24:54.581906+00:00
-- url     : https://prove2.me/submissions/f8726776-f1b8-48b2-8067-c957ae6fa7c4

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 3 (RowCompute.rows[1]!) =
    (462838969007592927454337764021095527422879249993826304000000 : ℤ) := by
  decide +kernel
