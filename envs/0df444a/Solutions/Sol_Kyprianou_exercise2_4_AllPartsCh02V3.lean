-- Prove2me | solution 1 for Kyprianou.exercise2_4_AllPartsCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:52:41.135964+00:00
-- url     : https://prove2.me/submissions/7f375056-4123-4881-96fc-2422ad9781b2

import Mathlib
import Theorems.Thm_Kyprianou_exercise2_4_uniform_cadlag_first_half
import Theorems.Thm_Kyprianou_ProofPreparation_exercise2_4_finite_large_jumps_unit
import Theorems.Thm_Kyprianou_ProofPreparation_exercise2_4_countable_discontinuities_unit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false

theorem solution :
    let isCadlagOnUnit : (ℝ → ℝ) → Prop := fun f =>
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        ContinuousWithinAt f (Set.Icc t 1) t) ∧
      (∀ t ∈ Set.Ioc (0 : ℝ) 1,
        ∃ l : ℝ,
          Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l))
    ((∀ (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ),
        (∀ n, isCadlagOnUnit (fn n)) →
        (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            |fn n t - f t| < ε) →
        isCadlagOnUnit f) ∧
     (∀ (f : ℝ → ℝ), isCadlagOnUnit f →
        (∀ c : ℝ, 0 < c →
          Set.Finite {t : ℝ |
            t ∈ Set.Ioc (0 : ℝ) 1 ∧
            ∃ l : ℝ,
              Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l) ∧
              c < |f t - l|}) ∧
        Set.Countable {t : ℝ |
          t ∈ Set.Ioc (0 : ℝ) 1 ∧
          ¬ ContinuousWithinAt f (Set.Icc (0 : ℝ) 1) t}))
      := by
  dsimp
  constructor
  · intro fn f hfn huni
    exact exercise2_4_uniform_cadlag_first_half fn f hfn huni
  · intro f hf
    exact ⟨Kyprianou.ProofPreparation.exercise2_4_finite_large_jumps_unit f hf.1 hf.2,
      Kyprianou.ProofPreparation.exercise2_4_countable_discontinuities_unit f hf.1 hf.2⟩
