-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_3_7_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:13:50.504752+00:00
-- url     : https://prove2.me/submissions/a39b72f7-9cdf-4826-8324-6b0c4cbd5470

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 3 7 (RowCompute.rows[4]!) =
    (-50817246425512219058310865543940707662118039710597120000000 : ℤ) := by
  decide +kernel
