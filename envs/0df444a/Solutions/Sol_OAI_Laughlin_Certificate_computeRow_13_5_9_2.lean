-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_9_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:40:00.399332+00:00
-- url     : https://prove2.me/submissions/a5f95096-5bb6-4314-9678-1442eb264374

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 9 (RowCompute.rows[2]!) =
    (-42461613039344902779867406144462942761933174964645527552000000 : ℤ) := by
  decide +kernel
