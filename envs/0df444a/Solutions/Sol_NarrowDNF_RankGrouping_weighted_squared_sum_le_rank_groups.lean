-- Prove2me | solution 1 for NarrowDNF.RankGrouping.weighted_squared_sum_le_rank_groups
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:54.982808+00:00
-- url     : https://prove2.me/submissions/1ddc581e-2f20-4f11-a10b-22ee814899d2

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

namespace NarrowDNF.RankGrouping
end NarrowDNF.RankGrouping

section


/-!
# Finite Bernoulli product probability

The probability model is an explicit finite sum of product weights. Algebraic
identities hold for every real parameter; positivity claims state `0 ≤ p ≤ 1`.
No theorem here assumes a probability law or an analytic input without proof.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ProductMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



@[simp] private theorem bitWeight_false (p : ℝ) : bitWeight p false = 1 - p := rfl
@[simp] private theorem bitWeight_true (p : ℝ) : bitWeight p true = p := rfl

















/-- Finite distributivity for independently chosen coordinates. -/
private theorem sum_prod_coordinates {α : Type*} [Fintype α] (F : ι → α → ℝ) :
    (∑ x : ι → α, ∏ i, F i (x i)) = ∏ i, ∑ a, F i a := by
  classical
  simpa only [Fintype.piFinset_univ] using
    (Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset α)) F).symm

@[simp] private theorem sum_weight (p : ℝ) : ∑ x : ι → Bool, weight p x = 1 := by
  unfold weight
  rw [sum_prod_coordinates]
  simp

@[simp] private theorem expectation_const (p c : ℝ) : expectation (ι := ι) p (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul]

@[simp] private theorem expectation_zero (p : ℝ) : expectation (ι := ι) p (fun _ => 0) = 0 :=
  expectation_const p 0

@[simp] private theorem expectation_one (p : ℝ) : expectation (ι := ι) p (fun _ => 1) = 1 :=
  expectation_const p 1

















@[simp] private theorem error_self (p : ℝ) (f : (ι → Bool) → Bool) : error p f f = 0 := by
  simp [error, probability]









omit [Fintype ι] in
@[simp] private theorem insertBit_at (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) :
    insertBit i b z i = b := by simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype ι] in
@[simp] private theorem insertBit_away (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool)
    (j : {j // j ≠ i}) : insertBit i b z j = z j := by
  simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt, j.property]























omit [Fintype ι] [DecidableEq ι] in
@[simp] private theorem extendFalse_on (P : ι → Prop) [DecidablePred P]
    (z : {i // P i} → Bool) (i : {i // P i}) : extendFalse P z i = z i := by
  simp [extendFalse, i.property]

omit [Fintype ι] [DecidableEq ι] in
@[simp] private theorem extendFalse_off (P : ι → Prop) [DecidablePred P]
    (z : {i // P i} → Bool) (i : ι) (hi : ¬ P i) : extendFalse P z i = false := by
  simp [extendFalse, hi]



end NarrowDNF.ProductMeasure

end

end

section


namespace NarrowDNF.RankGrouping
open scoped BigOperators

variable {α β : Type*} [DecidableEq β]

/-- A finite sum grouped by any rank map, with no multiplicity lost. -/
private theorem sum_by_rank (A : Finset α) (R : Finset β) (rank : α → β)
    (hcover : ∀ i ∈ A, rank i ∈ R) (v : α → ℝ) :
    (∑ i ∈ A, v i) = ∑ r ∈ R, ∑ i ∈ A with rank i = r, v i := by
  exact (Finset.sum_fiberwise_of_maps_to hcover v).symm

/-- Rank-group Cauchy–Schwarz. Choosing ranks 1,...,k gives exactly factor k;
choosing ranks 0,...,k gives k+1. -/
private theorem squared_sum_le_rank_groups (A : Finset α) (R : Finset β) (rank : α → β)
    (hcover : ∀ i ∈ A, rank i ∈ R) (v : α → ℝ) :
    (∑ i ∈ A, v i)^2 ≤ (R.card : ℝ) *
      ∑ r ∈ R, (∑ i ∈ A with rank i = r, v i)^2 := by
  rw [sum_by_rank A R rank hcover v]
  simpa using Finset.sum_mul_sq_le_sq_mul_sq R (fun _ => (1:ℝ))
    (fun r => ∑ i ∈ A with rank i = r, v i)



end NarrowDNF.RankGrouping


end

open NarrowDNF
open NarrowDNF.RankGrouping
open scoped BigOperators
variable {α β : Type*} [DecidableEq β]
/-- The same rank-group inequality under arbitrary finite nonnegative weights. -/
theorem solution {Ω : Type*} [Fintype Ω]
    (weights : Ω → ℝ) (hw : ∀ x, 0 ≤ weights x)
    (A : Finset α) (R : Finset β) (rank : α → β)
    (hcover : ∀ i ∈ A, rank i ∈ R) (v : Ω → α → ℝ) :
    (∑ x, weights x * (∑ i ∈ A, v x i)^2) ≤ (R.card : ℝ) *
      ∑ r ∈ R, ∑ x, weights x * (∑ i ∈ A with rank i = r, v x i)^2 := by
  calc
    _ ≤ ∑ x, weights x * ((R.card : ℝ) * ∑ r ∈ R, (∑ i ∈ A with rank i = r, v x i)^2) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
        (squared_sum_le_rank_groups A R rank hcover (v x)) (hw x)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro x _
      ring
