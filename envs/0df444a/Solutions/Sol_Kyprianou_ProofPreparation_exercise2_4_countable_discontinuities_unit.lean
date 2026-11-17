-- Prove2me | solution 1 for Kyprianou.ProofPreparation.exercise2_4_countable_discontinuities_unit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:50:26.484832+00:00
-- url     : https://prove2.me/submissions/3ec51651-64e2-4fc7-a61e-a900b955eff9

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_exercise2_4_finite_large_jumps_unit
import Theorems.Thm_Kyprianou_ProofPreparation_unit_discontinuity_has_nonzero_left_jump
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
    Set.Countable {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧
      ¬ ContinuousWithinAt f (Set.Icc (0 : ℝ) 1) t} := by
  have hfinite := exercise2_4_finite_large_jumps_unit f hR hL
  have hcount : Set.Countable
      (⋃ n : ℕ, {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧
        ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l) ∧
          (1 / ((n : ℝ) + 1)) < |f t - l|}) := by
    apply Set.countable_iUnion
    intro n
    exact (hfinite _ (by positivity)).countable
  apply hcount.mono
  intro t ht
  obtain ⟨l, hl, hne⟩ :=
    unit_discontinuity_has_nonzero_left_jump f hR hL t ht.1 ht.2
  have hpos : 0 < |f t - l| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
  exact Set.mem_iUnion.mpr ⟨n, ⟨ht.1, l, hl, hn⟩⟩
