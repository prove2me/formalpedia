-- Prove2me | solution 1 for Kyprianou.exercise2_4_uniform_cadlag_first_half
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:49:06.49413+00:00
-- url     : https://prove2.me/submissions/15e5eef4-9a20-4b79-a369-bd23626355d6

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_unit_right_continuous_of_uniform_limit
import Theorems.Thm_Kyprianou_ProofPreparation_unit_left_limit_of_uniform_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal Nat Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false
noncomputable section

theorem solution :
    let isCadlagOnUnit : (ℝ → ℝ) → Prop := fun f =>
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        ContinuousWithinAt f (Set.Icc t 1) t) ∧
      (∀ t ∈ Set.Ioc (0 : ℝ) 1,
        ∃ a : ℝ, Tendsto f (nhdsWithin t (Set.Iio t)) (nhds a))
    ∀ (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ),
      (∀ n, isCadlagOnUnit (fn n)) →
      (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ t ∈ Set.Icc (0 : ℝ) 1, |fn n t - f t| < ε) →
      isCadlagOnUnit f := by
  dsimp
  intro fn f hfn huni
  refine ⟨?_, ?_⟩
  · exact Kyprianou.ProofPreparation.unit_right_continuous_of_uniform_limit
      fn f (fun n t ht => (hfn n).1 t ht) huni
  · exact Kyprianou.ProofPreparation.unit_left_limit_of_uniform_limit
      fn f (fun n t ht => (hfn n).2 t ht) huni
