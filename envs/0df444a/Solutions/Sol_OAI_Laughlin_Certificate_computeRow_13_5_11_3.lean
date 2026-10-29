-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_11_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:38:54.951054+00:00
-- url     : https://prove2.me/submissions/1f682c99-898f-4331-854a-4b5996734982

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 11 (RowCompute.rows[3]!) =
    (254621415188964886471160878082330868529804192635364048896000000 : ℤ) := by
  decide +kernel
