-- Prove2me | solution 1 for Kyprianou.ProofPreparation.continuousWithinAt_of_uniform_approx
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:03:58.261564+00:00
-- url     : https://prove2.me/submissions/0b99d981-c356-4270-ad88-628dcdf26b75

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology
open scoped Topology NNReal ENNReal
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem continuousWithinAt_of_uniform_approx
    {s : Set ℝ} {x : ℝ} (hx : x ∈ s)
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfn : ∀ n, ContinuousWithinAt (fn n) s x)
    (huni : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ y ∈ s, |fn n y - f y| < ε) :
    ContinuousWithinAt f s x := by
  apply continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt hx
  intro u hu
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨n₀, hn₀⟩ := huni ε hε
  refine ⟨s, self_mem_nhdsWithin, fn n₀, hfn n₀, fun y hy => hεu ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  exact hn₀ n₀ le_rfl y hy

end Kyprianou.ProofPreparation

theorem solution
    {s : Set ℝ} {x : ℝ} (hx : x ∈ s)
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfn : ∀ n, ContinuousWithinAt (fn n) s x)
    (huni : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ y ∈ s, |fn n y - f y| < ε) :
    ContinuousWithinAt f s x := by
  first
  | exact Kyprianou.ProofPreparation.continuousWithinAt_of_uniform_approx
  | exact Kyprianou.ProofPreparation.continuousWithinAt_of_uniform_approx ..
  | (apply Kyprianou.ProofPreparation.continuousWithinAt_of_uniform_approx <;> assumption)
