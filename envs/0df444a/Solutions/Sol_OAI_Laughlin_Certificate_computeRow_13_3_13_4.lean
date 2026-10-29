-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_13_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:45:26.685217+00:00
-- url     : https://prove2.me/submissions/26065f04-be8b-41c9-94fa-08d5e9f24a48

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 13 (RowCompute.rows[4]!) =
    (842324458996076616575597442769111788713219973653402222592000000 : ℤ) := by
  decide +kernel
