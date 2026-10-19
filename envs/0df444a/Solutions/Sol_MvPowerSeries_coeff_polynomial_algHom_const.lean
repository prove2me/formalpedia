-- Prove2me | solution 1 for MvPowerSeries.coeff_polynomial_algHom_const
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:14:26.758607+00:00
-- url     : https://prove2.me/submissions/8cfcc32d-38d3-404f-998b-f4e883d5678f

import Mathlib
import Mathlib.RingTheory.MvPowerSeries.Basic

theorem solution
    {σ τ R : Type*} [CommSemiring R]
    (F G : MvPolynomial τ R →ₐ[R] MvPowerSeries σ R)
    (j : σ) (T : ℕ) (r : R) (a : σ →₀ ℕ) (ha : a j < T) :
    MvPowerSeries.coeff a (F (MvPolynomial.C r)) =
      MvPowerSeries.coeff a (G (MvPolynomial.C r)) := by
  have hF : F (MvPolynomial.C r) = algebraMap R _ r := by
    rw [← MvPolynomial.algebraMap_eq]; exact F.commutes r
  have hG : G (MvPolynomial.C r) = algebraMap R _ r := by
    rw [← MvPolynomial.algebraMap_eq]; exact G.commutes r
  rw [hF, hG]
