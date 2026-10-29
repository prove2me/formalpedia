-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:41:24.454783+00:00
-- url     : https://prove2.me/submissions/47815cb5-7a8e-4c01-a829-4d1bb87ce4ca

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 5 (RowCompute.rows[5]!) =
    (370765569688602274782125136441149265168254894112749125632000000 : ℤ) := by
  decide +kernel
