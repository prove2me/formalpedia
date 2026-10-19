-- Prove2me | solution 1 for MvPowerSeries.coeff_polynomial_algHom_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:14:19.531004+00:00
-- url     : https://prove2.me/submissions/80769a6f-b4b7-4e70-984d-3b331ea62fe0

import Mathlib
import Mathlib.RingTheory.MvPowerSeries.Basic

theorem solution
    {σ τ R : Type*} [CommSemiring R]
    (F G : MvPolynomial τ R →ₐ[R] MvPowerSeries σ R)
    (j : σ) (T : ℕ)
    (p q : MvPolynomial τ R) (a : σ →₀ ℕ) (ha : a j < T)
    (hp : ∀ b : σ →₀ ℕ, b j < T →
      MvPowerSeries.coeff b (F p) = MvPowerSeries.coeff b (G p))
    (hq : ∀ b : σ →₀ ℕ, b j < T →
      MvPowerSeries.coeff b (F q) = MvPowerSeries.coeff b (G q)) :
    MvPowerSeries.coeff a (F (p + q)) = MvPowerSeries.coeff a (G (p + q)) := by
  rw [map_add, map_add, map_add, map_add, hp a ha, hq a ha]
