-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_7_7_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:46:16.874985+00:00
-- url     : https://prove2.me/submissions/267f9d40-3635-486b-b63a-b1759b681ec3

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 7 7 (RowCompute.rows[3]!) =
    (-11476927042727677246306784306786489437444995167954141184000000 : ℤ) := by
  decide +kernel
