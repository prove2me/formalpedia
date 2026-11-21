-- Prove2me | solution 1 for MomentSearch.rakhmanov_phase_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:00:53.993171+00:00
-- url     : https://prove2.me/submissions/b1baa478-8655-4003-ad69-1e618624b1f5

import Mathlib
import Theorems.Thm_MomentSearch_rakhmanov_quantile_product_representation

theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun t => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - t ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let L : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, ρ t * Real.log |z - t|
    ∃ S : Polynomial ℝ, ∃ A : ℝ → ℝ,
      S.natDegree ≤ N - k ∧ ContinuousOn A (Set.Icc (-1 : ℝ) 1) ∧
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, 0 < A z ∧ S.eval z = A z * Real.exp (L z) * f z) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ z ∈ Set.Icc (-1 : ℝ) 1, A z ≤ 12 * A x) := by
  intro r ρ f L
  let V (z : ℝ) := ∫ t in (-1 : ℝ)..1, Real.log (1 / |z - t|) * ρ t
  obtain ⟨S, A, hdeg, hcont, hrep, hcomp⟩ :=
    MomentSearch.rakhmanov_quantile_product_representation N k hk hkN
  change ∀ z ∈ Set.Icc (-1 : ℝ) 1, 0 < A z ∧
    S.eval z = A z * Real.exp (-V z) * f z at hrep
  have hV (z : ℝ) : V z = -L z := by
    unfold V L
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    change Real.log (1 / |z - t|) * ρ t = -(ρ t * Real.log |z - t|)
    rw [one_div, Real.log_inv]
    ring
  refine ⟨S, A, hdeg, hcont, ?_, fun x hx z hz => hcomp z hz x hx⟩
  intro z hz
  simpa only [hV, neg_neg] using hrep z hz
