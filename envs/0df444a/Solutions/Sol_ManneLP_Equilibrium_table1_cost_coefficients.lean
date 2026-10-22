-- Prove2me | solution 1 for ManneLP.Equilibrium.table1_cost_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:09:52.078521+00:00
-- url     : https://prove2.me/submissions/12c1aeb6-b7bd-450c-9f65-79e835b8d188

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_LP
import Definitions.Def_ManneLP_Equilibrium_Example
set_option autoImplicit false
open ManneLP.Equilibrium

theorem EF_key (a b : ℤ) :
    ∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - a - b) =
      2 / 3 * max 0 (6 * ((0 : ℤ) - a - b : ℤ)) + 1 / 3 * max 0 (6 * (((2 : ℤ) - a - b : ℤ) : ℝ)) := by
  rw [tsum_eq_sum (s := Finset.range 3)]
  · simp [Finset.sum_range_succ, exampleModel, exampleDemand]
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp only [exampleModel, exampleDemand]
    rw [if_neg (by omega), if_neg (by omega)]
    simp

theorem solution :
    (∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - 0 - 0) = 4 ∧
      ∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - 0 - 1) = 2 ∧
      ∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - 1 - 0) = 2 ∧
      ∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - 1 - 1) = 0 ∧
      ∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - 2 - 0) = 0 ∧
      ∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - 2 - 1) = 0 ∧
      ∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - 3 - 0) = 0) ∧
    (costCoeff exampleModel 0 0 = 4 ∧ costCoeff exampleModel 0 1 = 5 ∧
      costCoeff exampleModel 1 0 = 3 ∧ costCoeff exampleModel 1 1 = 4 ∧
      costCoeff exampleModel 2 0 = 2 ∧ costCoeff exampleModel 2 1 = 5 ∧
      costCoeff exampleModel 3 0 = 3) := by
  have h : ∀ a b : ℕ, ∑' n : ℕ, exampleModel.p n * exampleModel.C₃ ((n : ℤ) - (a : ℤ) - (b : ℤ)) =
      2 / 3 * max 0 (6 * ((0 : ℤ) - (a:ℤ) - (b:ℤ) : ℤ)) + 1 / 3 * max 0 (6 * (((2 : ℤ) - (a:ℤ) - (b:ℤ) : ℤ) : ℝ)) :=
    fun a b => EF_key _ _
  have cc : ∀ i j : ℕ, costCoeff exampleModel i j = (i : ℝ) + 3 * (j : ℝ) +
      (2 / 3 * max 0 (6 * ((0 : ℤ) - (i:ℤ) - (j:ℤ) : ℤ)) + 1 / 3 * max 0 (6 * (((2 : ℤ) - (i:ℤ) - (j:ℤ) : ℤ) : ℝ))) := by
    intro i j
    unfold costCoeff
    rw [h i j]
    simp [exampleModel]
  have h0 := h 0 0
  have h1 := h 0 1
  have h2 := h 1 0
  have h3 := h 1 1
  have h4 := h 2 0
  have h5 := h 2 1
  have h6 := h 3 0
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h0 h1 h2 h3 h4 h5 h6
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0]; norm_num
  · rw [h1]; norm_num
  · rw [h2]; norm_num
  · rw [h3]; norm_num
  · rw [h4]; norm_num
  · rw [h5]; norm_num
  · rw [h6]; norm_num
  all_goals
    rw [cc]
    norm_num
