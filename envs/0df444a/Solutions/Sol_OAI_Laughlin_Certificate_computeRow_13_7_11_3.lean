-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_7_11_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:33:05.850984+00:00
-- url     : https://prove2.me/submissions/bb35d082-547c-4703-8087-6e2fab1b9760

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 7 11 (RowCompute.rows[3]!) =
    (-107450141066461239615345091855682711180756240766792105984000000 : ℤ) := by
  decide +kernel
