-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_zero_near_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:44:25.918022+00:00
-- url     : https://prove2.me/submissions/24519686-f2a3-46b8-914d-38c5316d6b6c

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Continuous cutoff vanishes near zero. -/
theorem solution (m : ℕ) :
    let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m:ℝ)+1)-1))
    Continuous chi ∧ (∀ z, 0 ≤ chi z ∧ chi z ≤ 1) ∧
      (∀ z, |z| * ((m:ℝ)+1) ≤ 1 → chi z = 0) := by
  dsimp
  refine ⟨by fun_prop, ?_, ?_⟩
  · intro z
    exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  · intro z hz
    rw [max_eq_left (sub_nonpos.mpr hz)]
    norm_num
