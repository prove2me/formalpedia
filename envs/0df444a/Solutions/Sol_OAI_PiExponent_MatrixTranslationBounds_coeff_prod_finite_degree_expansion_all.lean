-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finite_degree_expansion_all
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:37:05.777148+00:00
-- url     : https://prove2.me/submissions/8216174c-d4a0-4165-9740-e940e5e0601d

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_finsupp_antidiag
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_antidiag_fin_reindex

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ) :
    PowerSeries.coeff k (∏ i, g i) =
      ∑ f : ι → Fin (k + 1),
        if (∑ i, (f i).val) = k then
          ∏ i, PowerSeries.coeff (f i).val (g i)
        else 0 := by
  calc
    PowerSeries.coeff k (∏ i, g i) =
        ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k,
          ∏ i, PowerSeries.coeff (l i) (g i) :=
      OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finsupp_antidiag g k
    _ = ∑ f : ι → Fin (k + 1),
          if (∑ i, (f i).val) = k then
            ∏ i, PowerSeries.coeff (f i).val (g i)
          else 0 :=
      OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex g k