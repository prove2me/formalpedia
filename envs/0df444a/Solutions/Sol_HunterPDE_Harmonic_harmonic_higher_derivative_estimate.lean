-- Prove2me | solution 1 for HunterPDE.Harmonic.harmonic_higher_derivative_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T15:31:49.542478+00:00
-- url     : https://prove2.me/submissions/2beb9e30-e97b-4760-94af-60631281aaa7

import Theorems.Thm_HunterPDE_Harmonic_harmonic_directional_derivative
import Theorems.Thm_HunterPDE_Shared_iteratedPartial_estimate_of_first_estimates
import Theorems.Thm_HunterPDE_Harmonic_harmonic_derivative_estimate
import Mathlib.Algebra.BigOperators.Fin

open HunterPDE.Harmonic HunterPDE.Shared
set_option autoImplicit false

theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω) (hu : InnerProductSpace.HarmonicOnNhd u Ω)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall x r ⊆ Ω)
    (α : Fin n → ℕ) (k : ℕ) (hk : ∑ i, α i = k) (hk1 : 1 ≤ k)
    {M : ℝ} (hM : ∀ y ∈ Metric.closedBall x r, |u y| ≤ M) :
    |HunterPDE.Shared.multiDeriv u α x| ≤
      ((n : ℝ) ^ k * Real.exp 1 ^ (k - 1) * (k.factorial : ℝ) / r ^ k) * M := by
  classical
  have hlen : (multiIndexList α).length = k := by
    rw [multiIndexList, List.length_flatMap]
    simp only [List.length_replicate]
    rw [← List.ofFn_eq_map, List.sum_ofFn]
    exact hk
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    simp at hk
    omega
  have hh : ∀ l : List (Fin n), InnerProductSpace.HarmonicOnNhd (iteratedPartial u l) Ω := by
    intro l
    induction l with
    | nil => exact hu
    | cons i l ih =>
      exact harmonic_directional_derivative hn hΩ ih (EuclideanSpace.single i 1)
  have hfirst : ∀ (l : List (Fin n)) (y : EuclideanSpace ℝ (Fin n)) (s : ℝ),
      0 < s → Metric.closedBall y s ⊆ Ω → ∀ (i : Fin n) (A : ℝ),
      (∀ z ∈ Metric.closedBall y s, |iteratedPartial u l z| ≤ A) →
      |partialDeriv (iteratedPartial u l) i y| ≤ (n / s) * A := by
    intro l y s hs hsub i A hA
    exact harmonic_derivative_estimate hΩ (hh l) hs hsub i hA
  simpa only [multiDeriv, hlen] using
    iteratedPartial_estimate_of_first_estimates hfirst (multiIndexList α)
      (by simpa only [hlen] using hk1) hr hball hM
