-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_9_11_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:10:40.925806+00:00
-- url     : https://prove2.me/submissions/d49a4c55-68b5-40dc-8b8d-12c886165427

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 9 11 (RowCompute.rows[5]!) =
    (-27222578730352108757240895840240833696816620967861157888000000 : ℤ) := by
  decide +kernel
