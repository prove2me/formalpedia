-- Prove2me | solution 1 for Kyprianou.ProofPreparation.exercise2_4_finite_large_jumps_unit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:49:07.798003+00:00
-- url     : https://prove2.me/submissions/123bbbc1-1ddc-4c82-8ac2-591108fc93b6

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_real_unit_large_jumps_finite_of_nnreal_extension
import Theorems.Thm_Kyprianou_ProofPreparation_nnreal_clipped_right_continuous
import Theorems.Thm_Kyprianou_ProofPreparation_nnreal_clipped_left_limit_exists
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal Nat Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false
noncomputable section

theorem solution
    (f : ℝ → ℝ)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t)
    (hL : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l)) :
    ∀ c : ℝ, 0 < c →
      Set.Finite {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧
        ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l) ∧
          c < |f t - l|} := by
  intro c hc
  let Y : ℝ≥0 → ℝ := fun u => f (min (u : ℝ) 1)
  have hEq : ∀ u : ℝ≥0, u ≤ 1 → Y u = f (u : ℝ) := by
    intro u hu
    have huReal : (u : ℝ) ≤ 1 := by exact_mod_cast hu
    simp [Y, min_eq_left huReal]
  exact real_unit_large_jumps_finite_of_nnreal_extension
    f Y hEq (nnreal_clipped_right_continuous f hR)
      (nnreal_clipped_left_limit_exists f hL) c hc
