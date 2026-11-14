-- Prove2me | solution 1 for NarrowDNF.BourgainIntegration.large_event_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:04:26.465285+00:00
-- url     : https://prove2.me/submissions/5c834999-a380-4900-8af3-3b7d35721415

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_BourgainComponents
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.BourgainComponents
end NarrowDNF.BourgainComponents

namespace NarrowDNF.BourgainIntegration
end NarrowDNF.BourgainIntegration

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

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


/-!
# Finite Bernoulli variance and resampling influence

The one-coordinate identities in this file use the paper's resampling
normalization: a pivotal Boolean fiber has influence `2 * p * (1 - p)`.
The endpoints `p = 0` and `p = 1` are included in the algebraic identities.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.Influence




















/-- The square of a Boolean numerical value is itself. -/
@[simp] private theorem boolValue_sq (b : Bool) : boolValue b ^ 2 = boolValue b := by
  cases b <;> norm_num [boolValue]



section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

































end Cube
end NarrowDNF.Influence


end

end

section


/-!
# Finite biased Fourier expansion

A basis index is a Boolean support mask. Its true coordinates are exactly the
usual subset index. All expectations use Bernoulli product weights, and the
normalization of influence is independent resampling rather than bit flipping.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.Fourier











section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]































































/-- The constant Fourier coefficient is the mean. -/
@[simp] private theorem coefficient_zeroMask (p : ℝ) (f : (ι → Bool) → ℝ) :
    coefficient p f (fun _ => false) = ProductMeasure.expectation p f := by
  simp [coefficient, character, bitBasis]














@[simp] private theorem degree_maskEquivFinset_symm (S : Finset ι) :
    degree (maskEquivFinset.symm S) = S.card :=
  congrArg Finset.card (maskEquivFinset.apply_symm_apply S)


























end Cube
end NarrowDNF.Fourier







end

end

section


/-!
# Finite combinatorial part of Bourgain's component estimate

The definitions use the actual biased Fourier components. The pointwise
lemmas below are independent of any analytic square-function hypothesis.
They are ingredients, not a claim to have proved Hatami (11) or (18).
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.BourgainComponents

variable {ι : Type*} [Fintype ι] [DecidableEq ι]













omit [Fintype ι] in
private theorem coordinateSquare_nonneg (F : Finset (Finset ι)) (c : Finset ι → ℝ) (i : ι) :
    0 ≤ coordinateSquare F c i := by
  apply Finset.sum_nonneg
  intro S _
  split_ifs <;> first | exact le_rfl | positivity













/-- The large-coordinate count is bounded pointwise by the total coordinate
square mass. This is the unintegrated Markov step. -/
private theorem largeCoordinates_count_le (F : Finset (Finset ι)) (c : Finset ι → ℝ) (τ : ℝ) :
    τ^2 * ((largeCoordinates F c τ).card : ℝ) ≤ ∑ i, coordinateSquare F c i := by
  classical
  calc
    _ = ∑ i, if i ∈ largeCoordinates F c τ then τ^2 else 0 := by
      simp [mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · exact le_of_lt ((Finset.mem_filter.mp hi).2)
      · exact coordinateSquare_nonneg F c i

end NarrowDNF.BourgainComponents

end

end

noncomputable section
open NarrowDNF
open NarrowDNF.BourgainIntegration
open BourgainComponents
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Markov's inequality for the number of large square-function coordinates. -/
theorem solution (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (F : Finset (Finset ι)) (c : α → Finset ι → ℝ) (M : ℕ) (hM : 0 < M)
    (τ : ℝ) (hτ : 0 < τ) :
    (∑ x, w x * (if M ≤ (largeCoordinates F (c x) τ).card then 1 else 0)) ≤
      (∑ x, w x * ∑ i, coordinateSquare F (c x) i) / ((M : ℝ)*τ^2) := by
  have hd : (0:ℝ) < (M:ℝ)*τ^2 := mul_pos (Nat.cast_pos.mpr hM) (sq_pos_of_pos hτ)
  apply (le_div_iff₀ hd).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : M ≤ (largeCoordinates F (c x) τ).card
  · simp only [if_pos hx, mul_one]
    apply mul_le_mul_of_nonneg_left _ (hw x)
    have hcast : (M : ℝ) ≤ (largeCoordinates F (c x) τ).card := by exact_mod_cast hx
    have hcount := largeCoordinates_count_le F (c x) τ
    nlinarith [sq_nonneg τ]
  · simp only [if_neg hx, mul_zero, zero_mul]
    exact mul_nonneg (hw x) (Finset.sum_nonneg fun i _ => coordinateSquare_nonneg F (c x) i)
