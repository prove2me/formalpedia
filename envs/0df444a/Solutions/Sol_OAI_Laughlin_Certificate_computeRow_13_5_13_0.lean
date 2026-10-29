-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_13_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:49:42.332989+00:00
-- url     : https://prove2.me/submissions/bc4d5784-805f-46ff-9672-fa80286f5421

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 13 (RowCompute.rows[0]!) =
    (-6908702291689663876653333072985400570368067177778763530240000000 : ℤ) := by
  decide +kernel
