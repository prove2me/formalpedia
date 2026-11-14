-- Prove2me | solution 1 for NarrowDNF.BourgainIntegration.integrated_bourgain_split
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:34:42.111321+00:00
-- url     : https://prove2.me/submissions/02ce8b70-d618-4ed5-9b83-a2ab2a9a6f34

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
import Theorems.Thm_NarrowDNF_BourgainComponents_pointwise_bourgain_split
import Theorems.Thm_NarrowDNF_BourgainIntegration_event_cauchy
import Theorems.Thm_NarrowDNF_BourgainIntegration_large_event_probability_le
import Theorems.Thm_NarrowDNF_BourgainIntegration_small_square_le

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
/-- The integrated three-piece Bourgain estimate, with every probability and
Cauchy–Schwarz/Markov step proved for the explicit finite weights. -/
theorem solution (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : ∑ x, w x = 1) (F : Finset (Finset ι)) (c : α → Finset ι → ℝ)
    (k M : ℕ) (hF : ∀ S ∈ F, S.card ≤ k) (hM : 0 < M)
    (η τ : ℝ) (hτ : 0 < τ) :
    (∑ x, w x * truncatedMass F (c x) η) ≤
      (M:ℝ)^k * η^2 + τ^(2/3:ℝ) *
        (∑ i, ∑ x, w x * (coordinateSquare F (c x) i)^(2/3:ℝ)) +
      Real.sqrt (∑ x, w x * (∑ S ∈ F, c x S^2)^2) *
        Real.sqrt (∑ x, w x * ∑ i, coordinateSquare F (c x) i) /
          (Real.sqrt (M:ℝ) * τ) := by
  let small := fun x => ∑ i, if coordinateSquare F (c x) i ≤ τ^2 then coordinateSquare F (c x) i else 0
  let total := fun x => ∑ S ∈ F, c x S^2
  let bad := fun x => M ≤ (largeCoordinates F (c x) τ).card
  have hsmall : (∑ x, w x * small x) ≤ τ^(2/3:ℝ) *
      (∑ i, ∑ x, w x * (coordinateSquare F (c x) i)^(2/3:ℝ)) := by
    calc
      _ ≤ ∑ x, w x * ∑ i, τ^(2/3:ℝ) * (coordinateSquare F (c x) i)^(2/3:ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (hw x)
        apply Finset.sum_le_sum
        intro i _
        exact small_square_le _ _ (coordinateSquare_nonneg F (c x) i) hτ
      _ = _ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro x _
        ring
  have hprob := large_event_probability_le w hw F c M hM τ hτ
  have hroot : Real.sqrt (∑ x, w x * (if bad x then 1 else 0)) ≤
      Real.sqrt (∑ x, w x * ∑ i, coordinateSquare F (c x) i) /
        (Real.sqrt (M:ℝ)*τ) := by
    calc
      _ ≤ Real.sqrt ((∑ x, w x * ∑ i, coordinateSquare F (c x) i) / ((M:ℝ)*τ^2)) :=
        Real.sqrt_le_sqrt hprob
      _ = _ := by
        rw [Real.sqrt_div, Real.sqrt_mul (Nat.cast_nonneg M), Real.sqrt_sq_eq_abs, abs_of_pos hτ]
        exact Finset.sum_nonneg fun x _ => mul_nonneg (hw x)
          (Finset.sum_nonneg fun i _ => coordinateSquare_nonneg F (c x) i)
  have htail := (event_cauchy w total hw (fun x => Finset.sum_nonneg fun S _ => sq_nonneg _) bad).trans
    (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _))
  have hbase : (∑ x, w x * truncatedMass F (c x) η) ≤
      (M:ℝ)^k * η^2 + (∑ x, w x * small x) + (∑ x, w x * (if bad x then total x else 0)) := by
    calc
      _ ≤ ∑ x, w x * ((M:ℝ)^k*η^2 + small x + (if bad x then total x else 0)) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (pointwise_bourgain_split F (c x) k M hF η τ) (hw x)
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul]
  calc
    _ ≤ (M:ℝ)^k * η^2 + (∑ x, w x * small x) + (∑ x, w x * (if bad x then total x else 0)) := hbase
    _ ≤ _ := by
      have := add_le_add (add_le_add (le_refl ((M:ℝ)^k * η^2)) hsmall) htail
      simpa only [total, mul_div_assoc] using this
