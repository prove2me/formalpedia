-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_log_tail_allowance_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:54:52.027752+00:00
-- url     : https://prove2.me/submissions/ebd5a28a-e2dc-4d08-9dbb-c9972ab7b0eb

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    1 ≤ Real.exp (H * (Real.log 2 / (d.v0 : ℝ))) := by
  apply Real.one_le_exp_iff.mpr
  apply mul_nonneg (le_of_lt hH)
  apply div_nonneg
  · exact Real.log_nonneg (by norm_num)
  · exact le_of_lt d.v0_pos