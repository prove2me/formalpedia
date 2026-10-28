-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_7_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:10:42.174971+00:00
-- url     : https://prove2.me/submissions/6ef6d84a-0ec1-4771-a643-542c9aed4071

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 7 (RowCompute.rows[0]!) =
    (-89376275884972635920402370290601418362201631455260442624000000 : ℤ) := by
  decide +kernel
