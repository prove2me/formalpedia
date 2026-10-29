-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_11_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:37:39.283348+00:00
-- url     : https://prove2.me/submissions/97390fb4-8059-4c1c-b730-d5f85475bb9f

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 11 (RowCompute.rows[0]!) =
    (-40884555484062264129701420965884946069051981914149014732800000000 : ℤ) := by
  decide +kernel
