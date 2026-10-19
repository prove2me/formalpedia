-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finite_degree_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:23:36.552424+00:00
-- url     : https://prove2.me/submissions/f097bb49-1208-4e7f-8b2a-34fe46759b98

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_finite_degree_expansion_all
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_finite_degree_expansion_positive

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ)
    (h0 : ∀ i, PowerSeries.coeff 0 (g i) = 0) :
    PowerSeries.coeff k (∏ i, g i) =
      ∑ f : ι → Fin (k + 1),
        if (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k then
          ∏ i, PowerSeries.coeff (f i).val (g i)
        else 0 := by
  rw [OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finite_degree_expansion_all]
  exact OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finite_degree_expansion_positive g k h0