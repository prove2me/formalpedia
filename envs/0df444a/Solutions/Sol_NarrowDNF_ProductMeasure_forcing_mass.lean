-- Prove2me | solution 1 for NarrowDNF.ProductMeasure.forcing_mass
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:23:33.631173+00:00
-- url     : https://prove2.me/submissions/a9905b76-a601-4c4f-b983-e890c151dd16

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_ProductMeasure_sum_prod_two_coordinates

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
/-- Exact point masses of coordinatewise OR of two independent biased cubes.
The second cube is the random set of forced coordinates in Lemma 3.4. -/
theorem solution (p : ℝ) (z : ι → Bool) :
    (∑ x : ι → Bool, ∑ d : ι → Bool,
      if (fun i => x i || d i) = z then weight p x * weight p d else 0) =
        weight (2*p-p^2) z := by
  have hterm (x d : ι → Bool) :
      (if (fun i => x i || d i) = z then weight p x * weight p d else 0) =
        ∏ i, if (x i || d i) = z i then bitWeight p (x i) * bitWeight p (d i) else 0 := by
    rw [Fintype.prod_ite_zero, Finset.prod_mul_distrib]
    simp only [weight, funext_iff]
  simp_rw [hterm]
  rw [sum_prod_two_coordinates
    (fun i a b => if (a || b) = z i then bitWeight p a * bitWeight p b else 0)]
  apply Finset.prod_congr rfl
  intro i _
  cases z i <;> simp [bitWeight] <;> ring
