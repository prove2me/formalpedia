-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_3_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:49:36.639703+00:00
-- url     : https://prove2.me/submissions/077af90a-7130-4bca-97bd-f0ca430fa0aa

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 3 5 (RowCompute.rows[5]!) =
    (28364736260211343827393001222742840528698889371385856000000 : ℤ) := by
  decide +kernel
