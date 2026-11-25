-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46LowerHeightSequenceV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:49:26.281803+00:00
-- url     : https://prove2.me/submissions/bdf73d23-6671-447f-8faf-1bd6c1e755b8

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution :
    ∃ a : Nat → Real → Real, (∀ n, Measurable (a n)) ∧
      ∀ y : Real, 0 < y →
        (∀ n, 0 < a n y ∧ a n y < y) ∧
        Monotone (fun n => a n y) ∧
        Tendsto (fun n => a n y) atTop (nhds y) := by
  let a : Nat → Real → Real := fun n y => max (y/2) (y - 1 / ((n : Real) + 1))
  refine ⟨a, fun n => by fun_prop, ?_⟩
  intro y hy
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact ⟨lt_of_lt_of_le (by linarith : 0 < y/2) (le_max_left _ _),
      max_lt (by linarith) (sub_lt_self _ (by positivity))⟩
  · intro m n hmn
    apply max_le_max le_rfl
    exact sub_le_sub_left (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hmn)) _
  · have h := tendsto_const_nhds (x := y) |>.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    simpa [a, max_eq_right (show y/2 ≤ y by linarith)] using
      (tendsto_const_nhds (x := y/2)).max h
