-- Prove2me | solution 2 for OAI.Laughlin.Certificate.computeRow_12_3_7_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:41:28.915063+00:00
-- url     : https://prove2.me/submissions/3a8cc813-17c3-4dee-b9dd-87c490368855

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 3 7 (RowCompute.rows[2]!) =
    (7784022533757794511685165325925345472845446908288696320000000 : ℤ) := by
  decide +kernel
