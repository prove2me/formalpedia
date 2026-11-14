-- Prove2me | solution 1 for NarrowDNF.BourgainComponents.pointwise_bourgain_split
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:32:43.00144+00:00
-- url     : https://prove2.me/submissions/9cba1f22-0c12-4ed1-bc2a-b49e9559965c

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_BourgainComponents
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_BourgainComponents_truncated_mass_split

namespace NarrowDNF.BourgainComponents
end NarrowDNF.BourgainComponents

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















end NarrowDNF.BourgainComponents

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainComponents
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Full pointwise three-piece Bourgain decomposition, with an integer
large-coordinate cutoff M. -/
theorem solution (F : Finset (Finset ι)) (c : Finset ι → ℝ)
    (k M : ℕ) (hF : ∀ S ∈ F, S.card ≤ k) (η τ : ℝ) :
    truncatedMass F c η ≤ (M : ℝ)^k * η^2 +
      (∑ i, if coordinateSquare F c i ≤ τ^2 then coordinateSquare F c i else 0) +
      (if M ≤ (largeCoordinates F c τ).card then ∑ S ∈ F, c S^2 else 0) := by
  classical
  let A := largeCoordinates F c τ
  have hsmall : (∑ i, if i ∈ A then 0 else coordinateSquare F c i) =
      ∑ i, if coordinateSquare F c i ≤ τ^2 then coordinateSquare F c i else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [A, largeCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : coordinateSquare F c i ≤ τ^2
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  by_cases hM : M ≤ A.card
  · have hbound : truncatedMass F c η ≤ ∑ S ∈ F, c S^2 := by
      apply Finset.sum_le_sum
      intro S _
      split_ifs <;> first | exact le_rfl | positivity
    have hnonneg : 0 ≤ ∑ i, if coordinateSquare F c i ≤ τ^2 then coordinateSquare F c i else 0 := by
      apply Finset.sum_nonneg
      intro i _
      split_ifs
      · exact coordinateSquare_nonneg F c i
      · exact le_rfl
    have hnonneg' : 0 ≤ (M : ℝ)^k * η^2 := by positivity
    change M ≤ (largeCoordinates F c τ).card at hM
    rw [if_pos hM]
    linarith
  · have hcard : A.card + 1 ≤ M := by omega
    have hpow : ((A.card+1 : ℕ) : ℝ)^k ≤ (M : ℝ)^k := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast hcard
    have h := (truncated_mass_split F c A k hF η).trans
      (add_le_add (mul_le_mul_of_nonneg_right hpow (sq_nonneg η)) le_rfl)
    rw [hsmall] at h
    change ¬ M ≤ (largeCoordinates F c τ).card at hM
    simpa only [if_neg hM, add_zero] using h
