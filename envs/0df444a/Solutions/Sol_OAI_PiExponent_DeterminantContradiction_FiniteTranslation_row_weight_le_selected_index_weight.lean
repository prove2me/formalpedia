-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.row_weight_le_selected_index_weight
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:16:16.151638+00:00
-- url     : https://prove2.me/submissions/2f709718-903b-49f6-aca5-0c55e7f3e029

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Choose.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (f : Family d H)
    (hf : (∏ r : Row d H, scalar d r (f r)) ≠ 0)
    (r : Row d H) :
    ∑ i : Fin d.m,
        (r.2.1 i.succ : ℝ) * MatrixArithmetic.logWeights (finiteDenominators d) i ≤
      weight d (f r).1 := by
  classical
  have hscalar : scalar d r (f r) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hf r (Finset.mem_univ r)
  have hcoord : ∀ i : Fin d.m, r.2.1 i.succ ≤ (f r).1.1 i := by
    intro i
    apply le_of_not_gt
    intro hlt
    have hprod :
        (∏ j : Fin d.m,
          ((f r).1.1 j).choose (r.2.1 j.succ) *
            ((f r).1.1 j - r.2.1 j.succ).choose ((f r).2.1 j) : ℕ) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [Nat.choose_eq_zero_of_lt hlt, zero_mul]
    exact hscalar (by simp only [scalar, hprod, Nat.cast_zero, zero_mul])
  unfold weight
  apply Finset.sum_le_sum
  intro i hi
  have hcoordR : (r.2.1 i.succ : ℝ) ≤ ((f r).1.1 i : ℝ) :=
    Nat.cast_le.mpr (hcoord i)
  have hweight : 0 ≤ MatrixArithmetic.logWeights (finiteDenominators d) i := by
    unfold MatrixArithmetic.logWeights
    exact Nat.cast_nonneg _
  calc
    (r.2.1 i.succ : ℝ) * MatrixArithmetic.logWeights (finiteDenominators d) i ≤
        ((f r).1.1 i : ℝ) * MatrixArithmetic.logWeights (finiteDenominators d) i :=
      mul_le_mul_of_nonneg_right hcoordR hweight
    _ = MatrixArithmetic.logWeights (finiteDenominators d) i * ((f r).1.1 i : ℝ) :=
      mul_comm _ _