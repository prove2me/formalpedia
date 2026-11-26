-- Prove2me | solution 1 for Kyprianou.Ch04.twoAffineStepsBoundedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:56:16.921511+00:00
-- url     : https://prove2.me/submissions/a14258eb-97e2-47e1-8c46-92ec762cdcfb

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

/-- The sum of two finite step paths and a linear drift is bounded on a finite horizon. -/
theorem solution {ι κ : Type} (L : Finset ι) (S : Finset κ)
    (a r : ι → ℝ) (c q : κ → ℝ) (d : ℝ) (T : NNReal) (U : NNReal → ℝ)
    (hU : ∀ t ≤ T, U t = d * (t : ℝ) +
      (∑ i ∈ L, if r i ≤ (t : ℝ) then a i else 0) +
      (∑ j ∈ S, if q j ≤ (t : ℝ) then c j else 0)) :
    ∀ t ≤ T, |U t| ≤ |d| * (T : ℝ) + ∑ i ∈ L, |a i| + ∑ j ∈ S, |c j| := by
  intro t ht
  have hcast : (t : ℝ) ≤ (T : ℝ) := NNReal.coe_le_coe.mpr ht
  have hdrift : |d * (t : ℝ)| ≤ |d| * (T : ℝ) := by
    rw [abs_mul, abs_of_nonneg t.coe_nonneg]
    exact mul_le_mul_of_nonneg_left hcast (abs_nonneg _)
  have hL : |∑ i ∈ L, if r i ≤ (t : ℝ) then a i else 0| ≤ ∑ i ∈ L, |a i| := by
    calc
      _ ≤ ∑ i ∈ L, |if r i ≤ (t : ℝ) then a i else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun i hi => by split_ifs <;> simp
  have hS : |∑ j ∈ S, if q j ≤ (t : ℝ) then c j else 0| ≤ ∑ j ∈ S, |c j| := by
    calc
      _ ≤ ∑ j ∈ S, |if q j ≤ (t : ℝ) then c j else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun j hj => by split_ifs <;> simp
  rw [hU t ht]
  calc
    _ ≤ |d * (t : ℝ) + ∑ i ∈ L, if r i ≤ (t : ℝ) then a i else 0| +
        |∑ j ∈ S, if q j ≤ (t : ℝ) then c j else 0| := abs_add_le _ _
    _ ≤ (|d * (t : ℝ)| + |∑ i ∈ L, if r i ≤ (t : ℝ) then a i else 0|) +
        |∑ j ∈ S, if q j ≤ (t : ℝ) then c j else 0| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add hdrift hL) hS
