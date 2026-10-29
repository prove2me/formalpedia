-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_7_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:46:13.695491+00:00
-- url     : https://prove2.me/submissions/24b3008d-3211-4f94-bd63-4b37662d633a

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 7 (RowCompute.rows[5]!) =
    (-4434379663399642481187820308794667139175938256881582080000000 : ℤ) := by
  decide +kernel
