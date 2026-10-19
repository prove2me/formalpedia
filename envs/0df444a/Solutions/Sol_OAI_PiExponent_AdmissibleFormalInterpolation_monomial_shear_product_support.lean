-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_product_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:14:01.565128+00:00
-- url     : https://prove2.me/submissions/9974a002-7818-4ea6-9e7c-1c906d2ecbd1

import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_monomial_shear_factor_power_support
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_monomial_shear_product_support_of_factors

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (a e : Fin (m + 1) →₀ ℕ)
    (g : Fin m → MvPowerSeries (Fin (m + 1)) ℂ)
    (hg : ∀ i : Fin m, ∀ d : Fin (m + 1) →₀ ℕ, ∀ j : Fin m,
      d j.succ ≠ 0 → MvPowerSeries.coeff d (g i) = 0)
    (hne : MvPowerSeries.coeff e
      (MvPowerSeries.X 0 ^ a 0 *
        ∏ i : Fin m, (MvPowerSeries.X i.succ + g i) ^ a i.succ) ≠ 0) :
    ∀ i : Fin m, e i.succ ≤ a i.succ := by
  exact monomial_shear_product_support_of_factors
    (n := a 0) (b := fun i => a i.succ)
    (f := fun i => (MvPowerSeries.X i.succ + g i) ^ a i.succ) (e := e)
    (by
      intro i d hd
      exact (monomial_shear_factor_power_support i (a i.succ) g hg d).1 hd)
    (by
      intro i d j hji hd
      exact (monomial_shear_factor_power_support i (a i.succ) g hg d).2 j hji hd)
    hne