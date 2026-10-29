-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_9_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:48:18.608543+00:00
-- url     : https://prove2.me/submissions/ba872428-835f-41e3-a02c-1bfdcf13ee13

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 9 (RowCompute.rows[0]!) =
    (296877103528098506173024527827278206924613015728455417856000000 : ℤ) := by
  decide +kernel
