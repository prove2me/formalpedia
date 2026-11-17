-- Prove2me | solution 1 for Kyprianou.ProofPreparation.unit_left_limit_of_uniform_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:46:56.249257+00:00
-- url     : https://prove2.me/submissions/75ddbf7e-f6e5-43fa-8245-86a483278147

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_exists_tendsto_of_uniform_approx
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal Nat Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false
noncomputable section

theorem solution
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfn : ∀ n, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ a : ℝ, Tendsto (fn n) (𝓝[<] t) (𝓝 a))
    (huni : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |fn n t - f t| < ε) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ a : ℝ, Tendsto f (𝓝[<] t) (𝓝 a) := by
  intro t ht
  letI : NeBot (𝓝[<] t) := nhdsLT_neBot t
  have hs : Set.Icc (0 : ℝ) 1 ∈ 𝓝[<] t := by
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨Set.Ioi 0, Ioi_mem_nhds ht.1, ?_⟩
    intro x hx
    exact ⟨le_of_lt hx.1, (le_trans (le_of_lt hx.2) ht.2)⟩
  exact exists_tendsto_of_uniform_approx
    (𝓝[<] t) (Set.Icc (0 : ℝ) 1) hs fn f
    (fun n => hfn n t ht) huni
