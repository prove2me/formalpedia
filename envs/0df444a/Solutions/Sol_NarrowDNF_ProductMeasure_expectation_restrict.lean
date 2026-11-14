-- Prove2me | solution 1 for NarrowDNF.ProductMeasure.expectation_restrict
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:25.067198+00:00
-- url     : https://prove2.me/submissions/ddf2faf2-7982-472f-bdfa-20a5bf7c4846

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









omit [Fintype ι] in
@[simp] private theorem insertBit_at (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) :
    insertBit i b z i = b := by simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype ι] in
@[simp] private theorem insertBit_away (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool)
    (j : {j // j ≠ i}) : insertBit i b z j = z j := by
  simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt, j.property]

















omit [DecidableEq ι] in
/-- Product weights factor over a coordinate predicate and its complement. -/
private theorem weight_partition (p : ℝ) (P : ι → Prop) [DecidablePred P] (x : ι → Bool) :
    weight p x = weight p (fun i : {i // P i} => x i) *
      weight p (fun i : {i // ¬ P i} => x i) := by
  exact (Fintype.prod_subtype_mul_prod_subtype P (fun i => bitWeight p (x i))).symm











end NarrowDNF.ProductMeasure

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The marginal on any chosen coordinates is the corresponding product law. -/
theorem solution (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (F : ({i // P i} → Bool) → ℝ) :
    expectation p (fun x : ι → Bool => F (fun i => x i)) = expectation p F := by
  let e := Equiv.piEquivPiSubtypeProd P (fun _ : ι => Bool)
  have h := Fintype.sum_equiv e
    (fun x => weight p x * F (fun i => x i))
    (fun t : ({i // P i} → Bool) × ({i // ¬ P i} → Bool) =>
      weight p t.1 * weight p t.2 * F t.1)
    (fun x => by rw [weight_partition p P x]; rfl)
  unfold expectation
  rw [h, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  calc
    (∑ z : {i // ¬ P i} → Bool, weight p y * weight p z * F y) =
        (∑ z : {i // ¬ P i} → Bool, weight p z) * (weight p y * F y) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = weight p y * F y := by rw [sum_weight, one_mul]
