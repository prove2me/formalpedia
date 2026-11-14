-- Prove2me | solution 1 for NarrowDNF.ProductMeasure.expectation_split
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:22.150602+00:00
-- url     : https://prove2.me/submissions/fd63b3aa-4c07-4bca-af13-6a905e51809d

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





/-- Split off the mass contributed by a chosen coordinate. -/
private theorem weight_split (p : ℝ) (i : ι) (x : ι → Bool) :
    weight p x = bitWeight p (x i) * weight p (fun j : {j // j ≠ i} => x j) := by
  exact Fintype.prod_eq_mul_prod_subtype_ne (fun j => bitWeight p (x j)) i



omit [Fintype ι] in
@[simp] private theorem insertBit_at (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) :
    insertBit i b z i = b := by simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype ι] in
@[simp] private theorem insertBit_away (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool)
    (j : {j // j ≠ i}) : insertBit i b z j = z j := by
  simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt, j.property]





























end NarrowDNF.ProductMeasure

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Fubini's formula for one Bernoulli coordinate and its complement. -/
theorem solution (p : ℝ) (i : ι) (F : (ι → Bool) → ℝ) :
    expectation p F =
      (1-p) * expectation p (fun z => F (insertBit i false z)) +
        p * expectation p (fun z => F (insertBit i true z)) := by
  have h := Fintype.sum_equiv (Equiv.funSplitAt i Bool)
    (fun x => weight p x * F x)
    (fun t : Bool × ({j // j ≠ i} → Bool) =>
      bitWeight p t.1 * weight p t.2 * F (insertBit i t.1 t.2))
    (fun x => by
      have hin : insertBit i (x i) (fun j : {j // j ≠ i} => x j) = x :=
        (Equiv.funSplitAt i Bool).symm_apply_apply x
      change weight p x * F x = bitWeight p (x i) *
        weight p (fun j : {j // j ≠ i} => x j) * F (insertBit i (x i) (fun j => x j))
      rw [hin, weight_split p i x])
  unfold expectation
  rw [h, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [bitWeight_true, bitWeight_false, mul_assoc, ← Finset.mul_sum]
  exact add_comm _ _
