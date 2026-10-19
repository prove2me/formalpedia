-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_product_support_of_factors
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:20:13.79996+00:00
-- url     : https://prove2.me/submissions/7f81cdce-d587-4511-abb0-38c00212417d

import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_monomial_shear_product_support_core
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_monomial_prefactor_preserves_successor_support_bounds

open scoped BigOperators

theorem solution
    {m : ℕ} (n : ℕ) (b : Fin m → ℕ)
    (f : Fin m → MvPowerSeries (Fin (m + 1)) ℂ)
    (e : Fin (m + 1) →₀ ℕ)
    (hf : ∀ i : Fin m, ∀ d : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff d (f i) ≠ 0 → d i.succ ≤ b i)
    (hzero : ∀ i : Fin m, ∀ d : Fin (m + 1) →₀ ℕ, ∀ j : Fin m,
      j ≠ i → d j.succ ≠ 0 → MvPowerSeries.coeff d (f i) = 0)
    (hne : MvPowerSeries.coeff e
      (MvPowerSeries.X 0 ^ n * ∏ i : Fin m, f i) ≠ 0) :
    ∀ i : Fin m, e i.succ ≤ b i := by
  have hp : ∀ d : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff d (∏ i : Fin m, f i) ≠ 0 →
      ∀ i : Fin m, d i.succ ≤ b i := by
    intro d hd
    exact
      OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_product_support_core
        b f hf hzero d hd
  exact
    OAI.PiExponent.AdmissibleFormalInterpolation.monomial_prefactor_preserves_successor_support_bounds
      n b (∏ i : Fin m, f i) e hp hne