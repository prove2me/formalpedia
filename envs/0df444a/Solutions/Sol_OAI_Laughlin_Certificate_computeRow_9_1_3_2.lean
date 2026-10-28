-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_1_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:29:36.063927+00:00
-- url     : https://prove2.me/submissions/7fb6af02-a05a-4d3c-b92a-b6091dfb618c

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 1 3 (RowCompute.rows[2]!) =
    (216813933383140622295232522828123519722286834934140108800000 : ℤ) := by
  decide +kernel
