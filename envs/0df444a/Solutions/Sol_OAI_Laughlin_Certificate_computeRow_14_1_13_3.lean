-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_13_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:29:43.285323+00:00
-- url     : https://prove2.me/submissions/da8afc2e-c401-4bac-bba4-74f643d23134

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 13 (RowCompute.rows[3]!) =
    (-71677061185714403409666379639092148671632669376013330808832000000 : ℤ) := by
  decide +kernel
