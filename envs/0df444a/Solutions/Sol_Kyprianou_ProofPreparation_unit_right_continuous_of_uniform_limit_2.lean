-- Prove2me | solution 2 for Kyprianou.ProofPreparation.unit_right_continuous_of_uniform_limit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:03:59.61321+00:00
-- url     : https://prove2.me/submissions/6351bfa7-08e6-472d-9e70-5d5b778ef792

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
theorem unit_right_continuous_of_uniform_limit
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfn : ∀ n, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt (fn n) (Set.Icc t 1) t)
    (huni : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |fn n y - f y| < ε) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t := by
  intro t ht
  apply continuousWithinAt_of_uniform_approx (s := Set.Icc t 1) ⟨le_rfl, ht.2⟩ fn f
    (fun n => hfn n t ht)
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := huni ε hε
  exact ⟨n₀, fun n hn y hy => hn₀ n hn y ⟨ht.1.trans hy.1, hy.2⟩⟩

end Kyprianou.ProofPreparation

theorem solution
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfn : ∀ n, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt (fn n) (Set.Icc t 1) t)
    (huni : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |fn n y - f y| < ε) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t := by
  first
  | exact Kyprianou.ProofPreparation.unit_right_continuous_of_uniform_limit
  | exact Kyprianou.ProofPreparation.unit_right_continuous_of_uniform_limit ..
  | (apply Kyprianou.ProofPreparation.unit_right_continuous_of_uniform_limit <;> assumption)
