-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_9_9_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:39:49.539981+00:00
-- url     : https://prove2.me/submissions/5e6080d8-ad4a-405f-9cc6-843d502708b0

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 9 9 (RowCompute.rows[1]!) =
    (187884073902381346938059480387210087984889135536013312000000 : ℤ) := by
  decide +kernel
