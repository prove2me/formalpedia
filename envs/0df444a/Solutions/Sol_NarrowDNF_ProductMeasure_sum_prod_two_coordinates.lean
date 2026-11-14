-- Prove2me | solution 1 for NarrowDNF.ProductMeasure.sum_prod_two_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:23.044994+00:00
-- url     : https://prove2.me/submissions/6b25ccb3-8844-4e2e-b457-a581711685e4

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





























end NarrowDNF.ProductMeasure

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Finite double-product distributivity used in the forcing law. -/
theorem solution (F : ι → Bool → Bool → ℝ) :
    (∑ x : ι → Bool, ∑ y : ι → Bool, ∏ i, F i (x i) (y i)) =
      ∏ i, ∑ a : Bool, ∑ b : Bool, F i a b := by
  classical
  let e : ((ι → Bool) × (ι → Bool)) ≃ (ι → Bool × Bool) :=
    { toFun := fun t i => (t.1 i, t.2 i)
      invFun := fun z => (fun i => (z i).1, fun i => (z i).2)
      left_inv := by intro t; rfl
      right_inv := by intro z; rfl }
  rw [← Fintype.sum_prod_type' (fun (x y : ι → Bool) => ∏ i, F i (x i) (y i))]
  rw [Fintype.sum_equiv e
    (fun t => ∏ i, F i (t.1 i) (t.2 i))
    (fun z => ∏ i, F i (z i).1 (z i).2) (fun _ => rfl)]
  rw [sum_prod_coordinates (fun i (t : Bool × Bool) => F i t.1 t.2)]
  simp only [Fintype.sum_prod_type]
