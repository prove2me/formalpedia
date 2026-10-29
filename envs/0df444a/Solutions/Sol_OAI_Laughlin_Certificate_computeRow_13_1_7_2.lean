-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_7_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:41:26.161478+00:00
-- url     : https://prove2.me/submissions/98bf84f9-286c-4ec1-bd50-d8e60d5332d0

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 7 (RowCompute.rows[2]!) =
    (-109350839555057728957640951081427153165435255208544305152000000 : ℤ) := by
  decide +kernel
