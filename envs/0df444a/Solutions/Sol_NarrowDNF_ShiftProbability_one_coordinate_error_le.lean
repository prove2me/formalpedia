-- Prove2me | solution 1 for NarrowDNF.ShiftProbability.one_coordinate_error_le
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:23:40.413063+00:00
-- url     : https://prove2.me/submissions/4a300ebc-28af-4ffb-a37a-6d02219ce072

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_FiberShift
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

namespace NarrowDNF.ShiftProbability
end NarrowDNF.ShiftProbability

section


/-!
# Bias-matched shifts on a Boolean fiber

This file proves the two-point calculation used in Lemma 3.1 of
the 2026-11-06 STOC revision. The probability of the upper shift is `1 - p` and the
probability of the lower shift is `p`; the input fiber has the same bias `p`.

The error theorem is a conditional, single-fiber statement. Passing to an
arbitrary Boolean cube requires a separate summation/integration argument.
-/

namespace NarrowDNF.FiberShift

@[simp] private theorem true_not_le_false : ¬ ((true : Bool) ≤ false) := by decide























/-- Exact error improvement: only the target fiber `01` paired with the
approximating fiber `10` gives a strict improvement when `0 < p < 1`. -/
private theorem randomized_error_eq_sub (p : ℝ) (f v : Fiber) (hf : f.1 ≤ f.2) :
    (1 - p) * error p f (upper v) + p * error p f (lower v) =
      error p f v -
        (if f = (false, true) ∧ v = (true, false) then 2 * p * (1 - p) else 0) := by
  rcases f with ⟨f0, f1⟩
  rcases v with ⟨v0, v1⟩
  cases f0 <;> cases f1 <;> cases v0 <;> cases v1 <;>
    simp_all [error, mismatch, upper, lower] <;> ring

/-- The bias-matched randomized shift does not increase conditional error
against a nondecreasing target fiber. The closed interval also includes the
degenerate biases, strengthening the paper's `0 < p < 1` hypothesis. -/
private theorem randomized_error_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f v : Fiber) (hf : f.1 ≤ f.2) :
    (1 - p) * error p f (upper v) + p * error p f (lower v) ≤ error p f v := by
  rw [randomized_error_eq_sub p f v hf]
  by_cases h : f = (false, true) ∧ v = (true, false)
  · simp only [if_pos h]
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1)]
  · simp [h]

end NarrowDNF.FiberShift


end

section


/-!
# Coordinate shifts on Boolean functions

The unbranched shift formulas are equivalent to the two-slice definitions in
the shift definitions preceding Lemma 3.1 of the 2026-11-06 STOC revision, by Boolean idempotence. This file concerns
monotonicity; the global biased-error bound requires a separate finite-sum
argument.
-/

namespace NarrowDNF

variable {ι : Type*} [DecidableEq ι]









@[simp] private theorem upperShift_lowerInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    upperShift i v (lowerInput i x) = v (lowerInput i x) := by
  simp [upperShift, lowerInput]

@[simp] private theorem upperShift_upperInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    upperShift i v (upperInput i x) = (v (lowerInput i x) || v (upperInput i x)) := by
  simp [upperShift, lowerInput, upperInput, Bool.or_comm]

@[simp] private theorem lowerShift_lowerInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    lowerShift i v (lowerInput i x) = (v (lowerInput i x) && v (upperInput i x)) := by
  simp [lowerShift, lowerInput, upperInput]

@[simp] private theorem lowerShift_upperInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    lowerShift i v (upperInput i x) = v (upperInput i x) := by
  simp [lowerShift, upperInput]

private theorem lowerInput_le (i : ι) (x : Cube ι) : lowerInput i x ≤ x := by
  intro j
  by_cases hji : j = i
  · subst j
    simp [lowerInput]
  · simp [lowerInput, hji]

private theorem le_upperInput (i : ι) (x : Cube ι) : x ≤ upperInput i x := by
  intro j
  by_cases hji : j = i
  · subst j
    simp [upperInput]
  · simp [upperInput, hji]





















private theorem coordinateMonotone_of_monotone {v : Cube ι → Bool} (hv : Monotone v)
    (i : ι) : CoordinateMonotone i v := by
  intro x
  exact hv ((lowerInput_le i x).trans (le_upperInput i x))











end NarrowDNF


end

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









private theorem bitWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bitWeight p b := by
  cases b <;> simp only [bitWeight_false, bitWeight_true]
  · exact sub_nonneg.mpr hp1
  · exact hp0

omit [DecidableEq ι] in
private theorem weight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ι → Bool) :
    0 ≤ weight p x :=
  Finset.prod_nonneg fun i _ => bitWeight_nonneg hp0 hp1 (x i)





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



private theorem expectation_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F G : (ι → Bool) → ℝ} (hFG : ∀ x, F x ≤ G x) :
    expectation p F ≤ expectation p G :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hFG x) (weight_nonneg hp0 hp1 x)







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


/-!
# Randomized coordinate shifting under the biased product measure

This file proves the full error inequality of Lemma 3.1 and the iterated
expectation inequality following Lemma 3.1 in the 2026-11-06 STOC revision. Random choices form an
explicit Bernoulli product cube; the independence needed by iteration is
derived from the finite-sum Fubini formula.
-/

noncomputable section

namespace NarrowDNF.ShiftProbability

open ProductMeasure

variable {ι : Type*} [DecidableEq ι]

private theorem update_insertBit (i : ι) (a b : Bool) (z : {j // j ≠ i} → Bool) :
    Function.update (insertBit i a z) i b = insertBit i b z := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simpa only [Function.update_of_ne hji] using
      (insertBit_away i a z ⟨j, hji⟩).trans (insertBit_away i b z ⟨j, hji⟩).symm

@[simp] private theorem lowerInput_insertBit (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) :
    lowerInput i (insertBit i b z) = insertBit i false z :=
  update_insertBit i b false z

@[simp] private theorem upperInput_insertBit (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) :
    upperInput i (insertBit i b z) = insertBit i true z :=
  update_insertBit i b true z

variable [Fintype ι]

/-- Global disagreement is the expectation of the conditional fiber error. -/
private theorem error_eq_fiber_expectation (p : ℝ) (i : ι) (f v : Cube ι → Bool) :
    ProductMeasure.error p f v = expectation p (fun z =>
      FiberShift.error p (f (insertBit i false z), f (insertBit i true z))
        (v (insertBit i false z), v (insertBit i true z))) := by
  unfold ProductMeasure.error probability
  rw [expectation_split p i, ← expectation_const_mul, ← expectation_const_mul,
    ← expectation_add]
  congr 1
  funext z
  by_cases h0 : f (insertBit i false z) = v (insertBit i false z) <;>
    by_cases h1 : f (insertBit i true z) = v (insertBit i true z) <;>
      simp [FiberShift.error, FiberShift.mismatch, h0, h1]



























end NarrowDNF.ShiftProbability

end

end

noncomputable section
open NarrowDNF
open NarrowDNF.ShiftProbability
open ProductMeasure
variable {ι : Type*} [DecidableEq ι]
variable [Fintype ι]
/-- Full error bound in Lemma 3.1: the random shift choice is independent
of the input, and uses upper with mass `1-p` and lower with mass `p`. -/
theorem solution (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : ι) (f v : Cube ι → Bool) (hf : Monotone f) :
    (1-p) * ProductMeasure.error p f (upperShift i v) +
        p * ProductMeasure.error p f (lowerShift i v) ≤ ProductMeasure.error p f v := by
  rw [error_eq_fiber_expectation p i f (upperShift i v),
    error_eq_fiber_expectation p i f (lowerShift i v), error_eq_fiber_expectation p i f v,
    ← expectation_const_mul, ← expectation_const_mul, ← expectation_add]
  apply expectation_mono hp0 hp1
  intro z
  have hmono : f (insertBit i false z) ≤ f (insertBit i true z) := by
    simpa only [lowerInput_insertBit, upperInput_insertBit] using
      coordinateMonotone_of_monotone hf i (insertBit i false z)
  simpa [upperShift, lowerShift, FiberShift.upper, FiberShift.lower, Bool.or_comm] using
    FiberShift.randomized_error_le p hp0 hp1
      (f (insertBit i false z), f (insertBit i true z))
      (v (insertBit i false z), v (insertBit i true z)) hmono
