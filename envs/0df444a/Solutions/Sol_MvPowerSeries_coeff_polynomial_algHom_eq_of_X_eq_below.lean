-- Prove2me | solution 1 for MvPowerSeries.coeff_polynomial_algHom_eq_of_X_eq_below
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T16:15:43.731908+00:00
-- url     : https://prove2.me/submissions/ce137446-b111-4df5-9f56-dbc1389bbe42

import Mathlib.RingTheory.MvPowerSeries.Basic
import Theorems.Thm_MvPowerSeries_coeff_polynomial_algHom_const
import Theorems.Thm_MvPowerSeries_coeff_polynomial_algHom_add
import Theorems.Thm_MvPowerSeries_coeff_polynomial_algHom_mul
import Theorems.Thm_MvPowerSeries_coeff_polynomial_algHom_monomial

theorem solution
    {σ τ R : Type*} [CommSemiring R]
    (F G : MvPolynomial τ R →ₐ[R] MvPowerSeries σ R)
    (j : σ) (T : ℕ)
    (h : ∀ (i : τ) (b : σ →₀ ℕ), b j < T →
      MvPowerSeries.coeff b (F (MvPolynomial.X i)) =
        MvPowerSeries.coeff b (G (MvPolynomial.X i)))
    (P : MvPolynomial τ R) (a : σ →₀ ℕ) (ha : a j < T) :
    MvPowerSeries.coeff a (F P) = MvPowerSeries.coeff a (G P) := by
  revert a
  induction P using MvPolynomial.induction_on' with
  | monomial s r =>
      intro a ha
      exact MvPowerSeries.coeff_polynomial_algHom_monomial F G j T h s r a ha
  | add p q hp hq =>
      intro a ha
      exact MvPowerSeries.coeff_polynomial_algHom_add F G j T p q a ha hp hq
