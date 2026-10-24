-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_unitBoxUnion_subset
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T11:54:41.50066+00:00
-- url     : https://prove2.me/submissions/d5a15c78-5a4e-418d-afde-04011e02470a

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Definitions.Def_OAI_PiExponent_DeterminantContradiction_UnitBoxes
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (H : ℝ) (hH : 0 ≤ H) :
    unitBoxUnion (strictWeightedSimplex w H) ⊆
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧
        (∑ i, w i * x i) ≤ H + Finset.univ.sum w} := by
  classical
  intro x hx
  simp only [unitBoxUnion, Set.mem_iUnion, Set.mem_setOf_eq] at hx
  rcases hx with ⟨a, ha, hbox⟩
  change ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1 at hbox
  have hbase : (∑ i, w i * (a i : ℝ)) < H := by
    unfold strictWeightedSimplex at ha
    exact (Finset.mem_filter.mp ha).2
  have hnonneg : ∀ i, 0 ≤ x i := by
    intro i
    exact le_trans (by exact_mod_cast (Nat.zero_le (a i))) (hbox i).1
  have hsum :
      (∑ i, w i * x i) ≤ ∑ i, w i * ((a i : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hbox i).2.le (le_of_lt (hw i))
  have hsplit :
      (∑ i, w i * ((a i : ℝ) + 1)) =
        (∑ i, w i * (a i : ℝ)) + ∑ i, w i := by
    simp [mul_add, Finset.sum_add_distrib]
  refine ⟨hnonneg, ?_⟩
  rw [hsplit] at hsum
  have hweights : (∑ i, w i) = Finset.univ.sum w := by
    rfl
  rw [hweights]
  linarith