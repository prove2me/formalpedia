-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.monomial_prefactor_preserves_successor_support_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:24:23.156345+00:00
-- url     : https://prove2.me/submissions/2c5f44f6-1c83-441a-8643-da6cb710f0a6

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators

theorem solution
    {m : ℕ} (n : ℕ) (b : Fin m → ℕ)
    (p : MvPowerSeries (Fin (m + 1)) ℂ)
    (e : Fin (m + 1) →₀ ℕ)
    (hp : ∀ d : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff d p ≠ 0 → ∀ i : Fin m, d i.succ ≤ b i)
    (hne : MvPowerSeries.coeff e (MvPowerSeries.X 0 ^ n * p) ≠ 0) :
    ∀ i : Fin m, e i.succ ≤ b i := by
  classical
  let d : Fin (m + 1) →₀ ℕ := e - Finsupp.single 0 n
  have hcoeff : MvPowerSeries.coeff d p ≠ 0 := by
    dsimp [d]
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul] at hne
    by_cases hle : Finsupp.single (0 : Fin (m + 1)) n ≤ e
    · simpa [hle] using hne
    · simp [hle] at hne
  have hcoord (i : Fin m) : d i.succ = e i.succ := by
    simp [d, Finsupp.sub_apply, Fin.succ_ne_zero]
  intro i
  rw [← hcoord i]
  exact hp d hcoeff i