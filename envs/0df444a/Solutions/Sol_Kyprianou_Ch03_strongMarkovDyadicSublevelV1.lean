-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovDyadicSublevelV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:15:34.404188+00:00
-- url     : https://prove2.me/submissions/818ad2fc-b1a9-4adc-a568-b1d7a49318d1

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} (tau : Omega → WithTop NNReal)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (n j : ℕ) (w : Omega) :
    (tau w ≠ ⊤ ∧ Nat.ceil ((finiteTime w : ℝ) * (2 : ℝ)^n) ≤ j) ↔
      tau w ≤ (((j : NNReal) / (2 : NNReal)^n : NNReal) : WithTop NNReal) := by
  by_cases hw : tau w = ⊤
  · rw [hw]
    simp only [ne_eq, not_true_eq_false, false_and, false_iff]
    exact not_le_of_gt (WithTop.coe_lt_top _)
  · have he : Nat.ceil ((finiteTime w : ℝ) * (2 : ℝ)^n) ≤ j ↔
        tau w ≤ (((j : NNReal) / (2 : NNReal)^n : NNReal) : WithTop NNReal) := by
      rw [hFiniteTime w hw, WithTop.coe_le_coe, Nat.ceil_le]
      exact_mod_cast (le_div_iff₀ (show 0 < (2 : ℝ)^n by positivity)).symm
    exact ⟨fun h => he.mp h.2, fun h => ⟨hw, he.mpr h⟩⟩
