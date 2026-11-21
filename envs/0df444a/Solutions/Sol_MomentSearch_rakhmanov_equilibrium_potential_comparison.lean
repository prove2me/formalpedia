-- Prove2me | solution 1 for MomentSearch.rakhmanov_equilibrium_potential_comparison
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:00:53.903116+00:00
-- url     : https://prove2.me/submissions/eceb37a9-54a6-465d-8afe-01249126238e

import Mathlib
import Theorems.Thm_MomentSearch_rakhmanov_equilibrium_potential

theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let w : ℝ → ℝ := fun z => Real.exp (-(N : ℝ) / 2 *
      ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)))
    let V : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, Real.log (1 / |z-t|) * ρ t
    ∃ d : ℝ,
      (∀ x ∈ Set.Ioo (-r) r, V x - Real.log (w x) = d) ∧
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, d ≤ V z - Real.log (w z) := by
  intro r ρ w V
  let L (z : ℝ) := ∫ t in (-1 : ℝ)..1, ρ t * Real.log |z - t|
  let U (z : ℝ) := (N : ℝ) / 2 *
    ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z))
  obtain ⟨K, hflat, hle⟩ := MomentSearch.rakhmanov_equilibrium_potential N k hk hkN
  change ∀ x ∈ Set.Icc (-r) r, L x - U x = K at hflat
  change ∀ x ∈ Set.Icc (-1 : ℝ) 1, L x - U x ≤ K at hle
  have hV (z : ℝ) : V z = -L z := by
    unfold V L
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    change Real.log (1 / |z - t|) * ρ t = -(ρ t * Real.log |z - t|)
    rw [one_div, Real.log_inv]
    ring
  have hw (z : ℝ) : Real.log (w z) = -U z := by
    dsimp [w, U]
    rw [Real.log_exp]
    ring
  refine ⟨-K, ?_, ?_⟩
  · intro x hx
    rw [hV, hw]
    linarith only [hflat x ⟨hx.1.le, hx.2.le⟩]
  · intro z hz
    rw [hV, hw]
    linarith only [hle z hz]
