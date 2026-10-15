-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_pow_zero_of_support_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T13:39:26.804992+00:00
-- url     : https://prove2.me/submissions/195054fd-ffe8-4c59-821f-5cc436f4afa6

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_exists_coeff_factors_of_pow_coeff_ne_zero
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_sum_lower_bound_of_exp_decomp

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (wt : Fin (m + 1) → ℝ)
    (F : MvPowerSeries (Fin (m + 1)) ℂ) (B : ℝ) (n : ℕ)
    (hF : ∀ b : Fin (m + 1) → ℕ,
      (∑ k : Fin (m + 1), wt k * (b k : ℝ)) < B →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector b) F = 0)
    (hn : 0 < n) (a : Fin (m + 1) → ℕ)
    (ha : (∑ k : Fin (m + 1), wt k * (a k : ℝ)) < (n : ℝ) * B) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (F ^ n) = 0 := by
  by_contra hne
  obtain ⟨b, hbcoeff, hdecomp⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.exists_coeff_factors_of_pow_coeff_ne_zero
      F n a hne
  have hbwt : ∀ i : Fin n, B ≤ ∑ k : Fin (m + 1), wt k * (b i k : ℝ) := by
    intro i
    apply le_of_not_gt
    intro hlt
    exact hbcoeff i (hF (b i) hlt)
  have hbound :=
    OAI.PiExponent.LogarithmicJetIdeals.weighted_sum_lower_bound_of_exp_decomp
      wt B b a hdecomp hbwt
  exact (not_lt_of_ge hbound) ha