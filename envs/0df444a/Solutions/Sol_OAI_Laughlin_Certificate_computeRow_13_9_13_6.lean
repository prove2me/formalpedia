-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_9_13_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:38:51.81199+00:00
-- url     : https://prove2.me/submissions/38a01f8e-0074-43b1-b22a-3e08b272ad05

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 9 13 (RowCompute.rows[6]!) =
    (-46328235425697027018401344318579550719843788472876793856000000 : ℤ) := by
  decide +kernel
