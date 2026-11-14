-- Prove2me | solution 1 for NarrowDNF.ConditionalExpectation.expectation_mul_of_complement_local
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:18:58.914197+00:00
-- url     : https://prove2.me/submissions/5db11244-6068-467f-be78-57b0f980ffa5

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_ConditionalExpectation_expectation_merge
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_restrict

namespace NarrowDNF.ConditionalExpectation
end NarrowDNF.ConditionalExpectation

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



private theorem expectation_mul_const (p c : ℝ) (F : (ι → Bool) → ℝ) :
    expectation p (fun x => F x * c) = expectation p F * c := by
  simp [expectation, mul_assoc, Finset.sum_mul]

private theorem expectation_const_mul (p c : ℝ) (F : (ι → Bool) → ℝ) :
    expectation p (fun x => c * F x) = c * expectation p F := by
  simpa [mul_comm] using expectation_mul_const p c F











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

/-- A local observable may be integrated over only the coordinates it reads. -/
private theorem expectation_local (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (F : (ι → Bool) → ℝ)
    (hF : ∀ x y, (∀ i, P i → x i = y i) → F x = F y) :
    expectation p F = expectation p (fun z => F (extendFalse P z)) := by
  calc
    expectation p F =
        expectation p (fun x : ι → Bool => F (extendFalse P (fun i => x i))) := by
      apply congrArg (expectation p)
      funext x
      apply hF
      intro i hi
      simp [extendFalse, hi]
    _ = expectation p (fun z => F (extendFalse P z)) :=
      expectation_restrict p P (fun z => F (extendFalse P z))

end NarrowDNF.ProductMeasure

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.ConditionalExpectation
open ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Independence for observables reading complementary coordinate sets. -/
theorem solution (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (F G : Cube ι → ℝ)
    (hF : ∀ x y, (∀ i, P i → x i = y i) → F x = F y)
    (hG : ∀ x y, (∀ i, ¬ P i → x i = y i) → G x = G y) :
    expectation p (fun x => F x * G x) = expectation p F * expectation p G := by
  have hFm (z : {i // P i} → Bool) (y : {i // ¬ P i} → Bool) :
      F (merge P z y) = F (extendFalse P z) := by
    apply hF
    intro i hi
    simp [merge, extendFalse, hi]
  have hGm (z : {i // P i} → Bool) (y : {i // ¬ P i} → Bool) :
      G (merge P z y) = G (extendFalse (fun i => ¬ P i) y) := by
    apply hG
    intro i hi
    simp [merge, extendFalse, hi]
  rw [expectation_merge p P]
  simp_rw [hFm, hGm, expectation_const_mul]
  rw [expectation_mul_const, ← expectation_local p P F hF,
    ← expectation_local p (fun i => ¬ P i) G hG]
