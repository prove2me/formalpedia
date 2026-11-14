-- Prove2me | solution 1 for NarrowDNF.Activation.load_forcing_le
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:17:06.935197+00:00
-- url     : https://prove2.me/submissions/e3c4535f-c814-447d-afa2-09c7a144312c

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ActivationLoad
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_restrict
import Theorems.Thm_NarrowDNF_ProductMeasure_weight_forcing_le

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

section


namespace NarrowDNF

variable {ι : Type*} [Fintype ι] [DecidableEq ι]









namespace Activation





omit [DecidableEq ι] in
@[simp] private theorem mem_activeFinset (J : Activation ι) (x : Cube ι) (i : ι) :
    i ∈ J.activeFinset x ↔ i ∈ J.active x := by
  classical
  simp [activeFinset]

omit [DecidableEq ι] in
@[simp] private theorem mem_certificate (J : Activation ι) (x : Cube ι) (i : ι) :
    i ∈ J.certificate x ↔ i ∈ J.active x ∧ x i = true := by
  classical
  simp [certificate]

















end Activation
end NarrowDNF


end

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







private theorem expectation_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F : (ι → Bool) → ℝ} (hF : ∀ x, 0 ≤ F x) : 0 ≤ expectation p F :=
  Finset.sum_nonneg fun x _ => mul_nonneg (weight_nonneg hp0 hp1 x) (hF x)



private theorem probability_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : (ι → Bool) → Prop) [DecidablePred P] : 0 ≤ probability p P := by
  apply expectation_nonneg hp0 hp1
  intro x
  split_ifs <;> norm_num





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

section


/-!
# Load transport under random forcing

Point-mass and expectation bounds at effective bias `2*p-p^2`. Bounds are stated
without division by point masses, so they hold also for degenerate biases.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ProductMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]









private theorem expectation_forcing_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (F : (ι → Bool) → ℝ) (hF : ∀ x, 0 ≤ F x) :
    expectation (2 * p - p ^ 2) F ≤ (2 - p) ^ Fintype.card ι * expectation p F := by
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  calc
    weight (2 * p - p ^ 2) x * F x ≤
        ((2-p) ^ Fintype.card ι * weight p x) * F x :=
      mul_le_mul_of_nonneg_right (weight_forcing_le hp0 hp1 x) (hF x)
    _ = (2-p) ^ Fintype.card ι * (weight p x * F x) := mul_assoc _ _ _

end NarrowDNF.ProductMeasure

namespace NarrowDNF

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





namespace Activation

open ProductMeasure
attribute [local instance] Classical.propDecidable



private theorem probability_restrict (J : Activation ι) (p : ℝ) (S : Finset ι) :
    probability p (J.fires S) =
      probability p (fun z : S → Bool => J.fires S (extendLocal S z)) := by
  unfold probability
  change (expectation p (fun x : Cube ι => if J.fires S x then 1 else 0)) =
    expectation p (fun z : S → Bool => if J.fires S (extendLocal S z) then 1 else 0)
  have h := expectation_local p (fun i => i ∈ S)
    (fun x => if J.fires S x then 1 else 0) (by
      intro x y hxy
      simp only [J.locality S x y hxy])
  convert h using 1
  congr 1
  exact Subsingleton.elim _ _

/-- An activation pays for its own indexing set, not the ambient dimension. -/
private theorem probability_forcing_le (J : Activation ι) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset ι) :
    probability (2*p-p^2) (J.fires S) ≤
      (2-p)^S.card * probability p (J.fires S) := by
  rw [probability_restrict J (2*p-p^2) S, probability_restrict J p S]
  simpa only [probability, Fintype.card_coe] using
    expectation_forcing_le hp0 hp1
      (fun z : S → Bool => if J.fires S (extendLocal S z) then (1 : ℝ) else 0)
      (by intro z; split <;> norm_num)













end Activation
end NarrowDNF

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open NarrowDNF
open NarrowDNF.Activation
open ProductMeasure
attribute [local instance] Classical.propDecidable
theorem solution (J : Activation ι) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {d : ℕ} (hd : J.ArityLE d) :
    J.load (2*p-p^2) ≤ (2-p)^d * J.load p := by
  unfold load
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S.card ≤ d
  · have hpow : (2-p)^S.card ≤ (2-p)^d :=
      pow_le_pow_right₀ (by linarith) hS
    have hprob := probability_nonneg hp0 hp1 (J.fires S)
    calc
      (S.card : ℝ) * probability (2*p-p^2) (J.fires S) ≤
          (S.card : ℝ) * ((2-p)^S.card * probability p (J.fires S)) :=
        mul_le_mul_of_nonneg_left (probability_forcing_le J hp0 hp1 S) (by positivity)
      _ ≤ (S.card : ℝ) * ((2-p)^d * probability p (J.fires S)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hprob) (by positivity)
      _ = (2-p)^d * ((S.card : ℝ) * probability p (J.fires S)) := by ring
  · have hz : ∀ x, ¬ J.fires S x := hd S (Nat.lt_of_not_ge hS)
    simp [probability, hz]
