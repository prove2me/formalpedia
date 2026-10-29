-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_5_5_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:41:17.718091+00:00
-- url     : https://prove2.me/submissions/77ad3a3b-b06e-4f42-a89f-a667ac2999b4

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 5 5 (RowCompute.rows[4]!) =
    (1391155319829399804369746418787070264529761054245257216000000 : ℤ) := by
  decide +kernel
