-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_11_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:38:53.734041+00:00
-- url     : https://prove2.me/submissions/f4537f02-11b4-4224-8d02-2b055a465950

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 11 (RowCompute.rows[1]!) =
    (626529434928736569867895378731390055349710775012818944000000 : ℤ) := by
  decide +kernel
