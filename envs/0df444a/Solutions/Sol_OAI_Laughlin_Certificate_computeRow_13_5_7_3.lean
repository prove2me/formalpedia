-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_7_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:49:28.740994+00:00
-- url     : https://prove2.me/submissions/63b9c2cc-0c46-461a-9331-ae9eaff2bc42

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 7 (RowCompute.rows[3]!) =
    (15082239044278091839268436593746000933409620125051518976000000 : ℤ) := by
  decide +kernel
