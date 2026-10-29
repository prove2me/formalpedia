-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_3_7_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:49:30.245979+00:00
-- url     : https://prove2.me/submissions/55887108-857d-489b-8cae-b74694261e29

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 3 7 (RowCompute.rows[6]!) =
    (-2461756486798666800368352547290042691268979922776883200000 : ℤ) := by
  decide +kernel
