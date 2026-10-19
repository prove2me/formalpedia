-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.product_support_weight
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:00:52.691737+00:00
-- url     : https://prove2.me/submissions/9e5921aa-62cf-42a0-a18e-20972ffd2a5a

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_generic_product_support_weight
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_exponentVector_weight

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (sigma : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (hsigma : ∀ i : Fin (m + 1), ∀ b : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff b (sigma i) ≠ 0 →
        q i ≤ ∑ j, q j * (b j : ℝ))
    (b a : Fin (m + 1) → ℕ)
    (hprod : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (∏ i, sigma i ^ b i) ≠ 0) :
    (∑ j, q j * (b j : ℝ)) ≤ ∑ j, q j * (a j : ℝ) := by
  calc
    (∑ j, q j * (b j : ℝ)) ≤
        ∑ j, q j * (InterpolationMatrix.exponentVector a j : ℝ) :=
      OAI.PiExponent.LogarithmicJetIdeals.generic_product_support_weight
        q sigma hsigma b (InterpolationMatrix.exponentVector a) hprod
    _ = ∑ j, q j * (a j : ℝ) :=
      OAI.PiExponent.LogarithmicJetIdeals.exponentVector_weight q a