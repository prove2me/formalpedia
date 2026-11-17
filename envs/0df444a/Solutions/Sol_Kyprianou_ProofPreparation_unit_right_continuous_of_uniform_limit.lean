-- Prove2me | solution 1 for Kyprianou.ProofPreparation.unit_right_continuous_of_uniform_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:45:55.34101+00:00
-- url     : https://prove2.me/submissions/3d1ed4a4-fc45-4850-8789-41caa9694701

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_continuousWithinAt_of_uniform_approx
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open Kyprianou Kyprianou.ProofPreparation
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfn : ∀ n, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt (fn n) (Set.Icc t 1) t)
    (huni : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |fn n y - f y| < ε) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t := by
  intro t ht
  have hs : Set.Icc t 1 ⊆ Set.Icc (0 : ℝ) 1 := by
    intro y hy
    exact ⟨le_trans ht.1 hy.1, hy.2⟩
  apply continuousWithinAt_of_uniform_approx
    (s := Set.Icc t 1) (x := t) ⟨le_rfl, ht.2⟩ fn f
    (fun n => hfn n t ht)
  intro ε hε
  obtain ⟨n₀, hn⟩ := huni ε hε
  exact ⟨n₀, fun n hnn y hy => hn n hnn y (hs hy)⟩
