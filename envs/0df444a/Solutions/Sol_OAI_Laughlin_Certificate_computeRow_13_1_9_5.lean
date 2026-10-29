-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_9_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:41:19.203794+00:00
-- url     : https://prove2.me/submissions/7172e611-38e9-4e1c-8c1e-57bf47f16bcf

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 9 (RowCompute.rows[5]!) =
    (-392506032236338958015562624079019124560044770857016360960000000 : ℤ) := by
  decide +kernel
