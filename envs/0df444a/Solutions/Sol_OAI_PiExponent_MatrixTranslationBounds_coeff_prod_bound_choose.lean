-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.coeff_prod_bound_choose
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:20:35.187469+00:00
-- url     : https://prove2.me/submissions/e2ace591-7d42-4c8e-b6c6-dcd097254b75

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_finite_degree_expansion
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_finite_degree_sum_norm_bound

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ)
    (h0 : ∀ i, PowerSeries.coeff 0 (g i) = 0)
    (h1 : ∀ i n, ‖PowerSeries.coeff n (g i)‖ ≤ (1 : ℝ)) :
    ‖PowerSeries.coeff k (∏ i, g i)‖ ≤ (Nat.choose k (Fintype.card ι) : ℝ) := by
  rw [OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finite_degree_expansion g k h0]
  calc
    ‖∑ f : ι → Fin (k + 1),
        if (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k then
          ∏ i, PowerSeries.coeff (f i).val (g i)
        else 0‖ ≤
        ∑ f : ι → Fin (k + 1),
          ‖if (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k then
              ∏ i, PowerSeries.coeff (f i).val (g i)
            else (0 : ℂ)‖ := norm_sum_le _ _
    _ ≤ (Nat.choose k (Fintype.card ι) : ℝ) :=
      OAI.PiExponent.MatrixTranslationBounds.finite_degree_sum_norm_bound g k h1