-- Prove2me | solution 1 for NarrowDNF.Influence.variance_eq_secondMoment
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:04.121989+00:00
-- url     : https://prove2.me/submissions/c0984e9c-4529-4da3-a0fc-a5a1318c0262

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.Influence
end NarrowDNF.Influence

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

private theorem expectation_add (p : ℝ) (F G : (ι → Bool) → ℝ) :
    expectation p (fun x => F x + G x) = expectation p F + expectation p G := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

private theorem expectation_mul_const (p c : ℝ) (F : (ι → Bool) → ℝ) :
    expectation p (fun x => F x * c) = expectation p F * c := by
  simp [expectation, mul_assoc, Finset.sum_mul]

private theorem expectation_const_mul (p c : ℝ) (F : (ι → Bool) → ℝ) :
    expectation p (fun x => c * F x) = c * expectation p F := by
  simpa [mul_comm] using expectation_mul_const p c F





















































end NarrowDNF.ProductMeasure

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.Influence
section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem solution (p : ℝ) (F : (ι → Bool) → ℝ) :
    variance p F = ProductMeasure.expectation p (fun x => F x ^ 2) -
      ProductMeasure.expectation p F ^ 2 := by
  unfold variance
  calc
    _ = ProductMeasure.expectation p (fun x => F x ^ 2 +
        (-2 * ProductMeasure.expectation p F) * F x +
        ProductMeasure.expectation p F ^ 2) := by
          congr 1
          funext x
          ring
    _ = _ := by
      rw [ProductMeasure.expectation_add, ProductMeasure.expectation_add,
        ProductMeasure.expectation_const_mul, ProductMeasure.expectation_const]
      ring
