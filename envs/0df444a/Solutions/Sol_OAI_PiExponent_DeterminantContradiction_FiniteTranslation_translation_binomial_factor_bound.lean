-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_binomial_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:44:10.54971+00:00
-- url     : https://prove2.me/submissions/73101c8c-fd1a-4fda-a079-89ea46f457f3

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_binomial_product_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_index_sum_bound

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖((∏ i : Fin d.m,
          (t.1.1 i).choose (r.2.1 i.succ) *
            (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ)‖ ≤
      Real.exp (H * (Real.log 4 / d.wstar)) := by
  have hprod :=
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_binomial_product_bound
      d hnu hH r t
  have hsum :=
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_index_sum_bound
      d hnu hH r t
  have hlog : 0 ≤ Real.log 4 := le_of_lt (Real.log_pos (by norm_num))
  have hexp : Real.log 4 * ∑ i : Fin d.m, (t.1.1 i : ℝ) ≤
      H * (Real.log 4 / d.wstar) := by
    calc
      Real.log 4 * ∑ i : Fin d.m, (t.1.1 i : ℝ) ≤
          Real.log 4 * (H / d.wstar) := mul_le_mul_of_nonneg_left hsum hlog
      _ = H * (Real.log 4 / d.wstar) := by ring
  exact hprod.trans (Real.exp_le_exp.mpr hexp)