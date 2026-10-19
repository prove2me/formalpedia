-- Prove2me | solution 1 for MvPowerSeries.coeff_polynomial_algHom_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:14:34.119611+00:00
-- url     : https://prove2.me/submissions/77c4856e-ebf8-43ca-abef-fb45f124313e

import Mathlib
import Mathlib.RingTheory.MvPowerSeries.Basic

theorem pie_agree_mul {σ τ R : Type*} [CommSemiring R]
    (F G : MvPolynomial τ R →ₐ[R] MvPowerSeries σ R)
    (j : σ) (T : ℕ)
    (p q : MvPolynomial τ R)
    (hp : ∀ b : σ →₀ ℕ, b j < T →
      MvPowerSeries.coeff b (F p) = MvPowerSeries.coeff b (G p))
    (hq : ∀ b : σ →₀ ℕ, b j < T →
      MvPowerSeries.coeff b (F q) = MvPowerSeries.coeff b (G q)) :
    ∀ a : σ →₀ ℕ, a j < T →
    MvPowerSeries.coeff a (F (p * q)) = MvPowerSeries.coeff a (G (p * q)) := by
  classical
  intro a ha
  rw [show F (p * q) = F p * F q from map_mul F p q, show G (p * q) = G p * G q from map_mul G p q,
    MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h1 : x.1 j < T := by
    have := congrArg (fun f => f j) hx
    simp only [Finsupp.add_apply] at this
    omega
  have h2 : x.2 j < T := by
    have := congrArg (fun f => f j) hx
    simp only [Finsupp.add_apply] at this
    omega
  rw [hp _ h1, hq _ h2]

theorem solution
    {σ τ R : Type*} [CommSemiring R]
    (F G : MvPolynomial τ R →ₐ[R] MvPowerSeries σ R)
    (j : σ) (T : ℕ)
    (p q : MvPolynomial τ R) (a : σ →₀ ℕ) (ha : a j < T)
    (hp : ∀ b : σ →₀ ℕ, b j < T →
      MvPowerSeries.coeff b (F p) = MvPowerSeries.coeff b (G p))
    (hq : ∀ b : σ →₀ ℕ, b j < T →
      MvPowerSeries.coeff b (F q) = MvPowerSeries.coeff b (G q)) :
    MvPowerSeries.coeff a (F (p * q)) = MvPowerSeries.coeff a (G (p * q)) :=
  pie_agree_mul F G j T p q hp hq a ha
