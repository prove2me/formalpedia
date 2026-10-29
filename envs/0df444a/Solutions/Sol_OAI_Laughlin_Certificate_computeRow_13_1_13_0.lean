-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_13_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:41:16.436232+00:00
-- url     : https://prove2.me/submissions/2fb3188f-df46-4f52-a0e0-5365e73d71ec

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 13 (RowCompute.rows[0]!) =
    (44775841939111351400368799525590310278175073141256882225152000000 : ℤ) := by
  decide +kernel
