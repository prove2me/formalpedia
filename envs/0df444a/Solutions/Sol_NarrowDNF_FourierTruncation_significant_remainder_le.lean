-- Prove2me | solution 1 for NarrowDNF.FourierTruncation.significant_remainder_le
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:26:39.085039+00:00
-- url     : https://prove2.me/submissions/d59f8569-6b6c-4304-8b64-8528e5df0918

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_FourierTruncation
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Fourier_inner_parseval

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.FourierTruncation
end NarrowDNF.FourierTruncation

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.Influence
end NarrowDNF.Influence

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



private theorem expectation_mul_const (p c : ℝ) (F : (ι → Bool) → ℝ) :
    expectation p (fun x => F x * c) = expectation p F * c := by
  simp [expectation, mul_assoc, Finset.sum_mul]

private theorem expectation_const_mul (p c : ℝ) (F : (ι → Bool) → ℝ) :
    expectation p (fun x => c * F x) = c * expectation p F := by
  simpa [mul_comm] using expectation_mul_const p c F

private theorem expectation_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F : (ι → Bool) → ℝ} (hF : ∀ x, 0 ≤ F x) : 0 ≤ expectation p F :=
  Finset.sum_nonneg fun x _ => mul_nonneg (weight_nonneg hp0 hp1 x) (hF x)









@[simp] private theorem error_self (p : ℝ) (f : (ι → Bool) → Bool) : error p f f = 0 := by
  simp [error, probability]









omit [Fintype ι] in
@[simp] private theorem insertBit_at (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) :
    insertBit i b z i = b := by simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype ι] in
@[simp] private theorem insertBit_away (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool)
    (j : {j // j ≠ i}) : insertBit i b z j = z j := by
  simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt, j.property]



/-- Independence factorization for observables that factor over coordinates. -/
private theorem expectation_prod (p : ℝ) (F : ι → Bool → ℝ) :
    expectation p (fun x => ∏ i, F i (x i)) =
      ∏ i, ((1-p) * F i false + p * F i true) := by
  unfold expectation weight
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_prod_coordinates (fun i b => bitWeight p b * F i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp [add_comm]



















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





private theorem sqrt_bias_ne_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Real.sqrt (p * (1-p)) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (mul_pos hp0 (sub_pos.mpr hp1)))

private theorem bit_orthogonality {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (s t : Bool) :
    (1-p) * (bitBasis p s false * bitBasis p t false) +
      p * (bitBasis p s true * bitBasis p t true) = if s = t then 1 else 0 := by
  have hs := sqrt_bias_ne_zero hp0 hp1
  have hs2 := Real.sq_sqrt (le_of_lt (mul_pos hp0 (sub_pos.mpr hp1)))
  cases s <;> cases t <;> simp [bitBasis, standardBit]
  all_goals field_simp
  all_goals nlinarith



section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]







/-- Orthonormality for the biased product measure. -/
private theorem orthogonality {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (s t : ι → Bool) :
    ProductMeasure.expectation p (fun x => character p s x * character p t x) =
      if s = t then 1 else 0 := by
  unfold character
  simp_rw [← Finset.prod_mul_distrib]
  rw [ProductMeasure.expectation_prod p (fun i b => bitBasis p (s i) b * bitBasis p (t i) b)]
  simp_rw [bit_orthogonality hp0 hp1]
  rw [Fintype.prod_boole]
  simp only [funext_iff]








/-- Parseval: squared L2 norm equals total squared Fourier mass. -/
private theorem parseval {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => f x ^ 2) =
      ∑ s : ι → Bool, coefficient p f s ^ 2 := by
  simpa only [pow_two] using inner_parseval hp0 hp1 f f












private theorem expectation_sub (p : ℝ) (f g : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => f x - g x) =
      ProductMeasure.expectation p f - ProductMeasure.expectation p g := by
  simp [ProductMeasure.expectation, mul_sub, Finset.sum_sub_distrib]

































/-- The constant Fourier coefficient is the mean. -/
@[simp] private theorem coefficient_zeroMask (p : ℝ) (f : (ι → Bool) → ℝ) :
    coefficient p f (fun _ => false) = ProductMeasure.expectation p f := by
  simp [coefficient, character, bitBasis]














@[simp] private theorem degree_maskEquivFinset_symm (S : Finset ι) :
    degree (maskEquivFinset.symm S) = S.card :=
  congrArg Finset.card (maskEquivFinset.apply_symm_apply S)
















/-- Every subset-indexed biased basis function has squared L2 norm one. -/
private theorem setCharacter_sq_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (S : Finset ι) :
    ProductMeasure.expectation p (fun x => setCharacter p S x ^ 2) = 1 := by
  simpa only [setCharacter, pow_two, if_pos rfl, if_true] using
    orthogonality hp0 hp1 (maskEquivFinset.symm S) (maskEquivFinset.symm S)

/-- The squared L2 mass of a generalized Walsh component is its squared coefficient. -/
private theorem component_sq_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (S : Finset ι) :
    ProductMeasure.expectation p (fun x => component p f S x ^ 2) =
      setCoefficient p f S ^ 2 := by
  simp only [component, mul_pow]
  rw [ProductMeasure.expectation_const_mul, setCharacter_sq_mean hp0 hp1, mul_one]

/-- Subset-indexed Parseval identity. -/
private theorem parseval_finset {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => f x ^ 2) =
      ∑ S : Finset ι, setCoefficient p f S ^ 2 := by
  rw [parseval hp0 hp1]
  apply Fintype.sum_equiv maskEquivFinset
  intro s
  simp only [setCoefficient, Equiv.symm_apply_apply]





end Cube
end NarrowDNF.Fourier







end

end

section


/-!
# Hatami's threshold activation family

The local activations and multiplicity-counted load calculation from Appendix A
of the 2026-11-06 STOC revision. The cutoff is real, as in the source. All threshold masses
are explicit finite sums; no activation-load guarantee is assumed.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.HatamiActivation

open ProductMeasure
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

























omit [Fintype ι] in
@[simp] private theorem localMass_extendLocal (p : ℝ) (T : Finset ι) (z : T → Bool) :
    localMass p T (Activation.extendLocal T z) = weight p z := by
  unfold localMass
  congr 1
  funext i
  simp [Activation.extendLocal, i.property]































































end NarrowDNF.HatamiActivation

end

end

section


noncomputable section
namespace NarrowDNF.FourierTruncation
open ProductMeasure Fourier
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



private theorem expectation_finset_sum {α : Type*} (p : ℝ) (s : Finset α) (F : α → Cube ι → ℝ) :
    expectation p (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, expectation p (F i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

private theorem setCoefficient_sub (p : ℝ) (f g : Cube ι → ℝ) (S : Finset ι) :
    setCoefficient p (fun x => f x - g x) S = setCoefficient p f S - setCoefficient p g S := by
  unfold setCoefficient coefficient
  simp only [sub_mul]
  exact Fourier.expectation_sub p _ _

private theorem component_coefficient {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube ι → ℝ) (S T : Finset ι) :
    setCoefficient p (component p f S) T = if S = T then setCoefficient p f S else 0 := by
  unfold setCoefficient coefficient component setCharacter
  simp only [mul_assoc, expectation_const_mul]
  rw [orthogonality hp0 hp1]
  simp [setCoefficient, coefficient]

private theorem setCoefficient_partialSum {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube ι → ℝ) (retained : Finset (Finset ι)) (T : Finset ι) :
    setCoefficient p (partialSum p f retained) T = if T ∈ retained then setCoefficient p f T else 0 := by
  classical
  unfold partialSum setCoefficient coefficient
  simp only [Finset.sum_mul]
  rw [expectation_finset_sum]
  have h : ∀ S, expectation p (fun x => component p f S x * character p (maskEquivFinset.symm T) x) =
      if S = T then setCoefficient p f S else 0 := fun S => component_coefficient hp0 hp1 f S T
  simp_rw [h]
  simp [setCoefficient, coefficient]

/-- Exact finite Parseval remainder for an arbitrary retained Fourier family. -/
private theorem squaredError_partialSum {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube ι → ℝ) (retained : Finset (Finset ι)) :
    ConditionalExpectation.squaredError (weight p) f (partialSum p f retained) =
      ∑ S ∈ Finset.univ \ retained, setCoefficient p f S ^ 2 := by
  classical
  change expectation p (fun x => (f x - partialSum p f retained x)^2) = _
  rw [parseval_finset hp0 hp1]
  simp_rw [setCoefficient_sub, setCoefficient_partialSum hp0 hp1]
  rw [Finset.sdiff_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S ∈ retained <;> simp [hS]






end NarrowDNF.FourierTruncation

end

end

noncomputable section
open NarrowDNF
open NarrowDNF.FourierTruncation
open ProductMeasure Fourier
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The elementary combination of Hatami's Steps I and II, before inserting
the separate high-degree and Bourgain bounds. -/
theorem solution {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube ι → ℝ) (k η : ℝ) :
    ConditionalExpectation.squaredError (weight p) f
      (partialSum p f (HatamiActivation.significantSets p f k η)) ≤
      (∑ S : Finset ι, if k < (S.card : ℝ) then setCoefficient p f S ^ 2 else 0) +
        smallMassReal p f k η := by
  classical
  rw [squaredError_partialSum hp0 hp1, Finset.sdiff_eq_filter, Finset.sum_filter]
  unfold smallMassReal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _
  by_cases hdeg : (S.card : ℝ) ≤ k
  · simp only [not_lt.mpr hdeg, if_false, zero_add]
    by_cases hS : S ∈ HatamiActivation.significantSets p f k η
    · simp only [hS, not_true_eq_false, if_false]
      apply expectation_nonneg hp0.le hp1.le
      intro x
      split <;> positivity
    · have hsmall : ∀ x, |component p f S x| ≤ η := by
        intro x
        by_contra hx
        apply hS
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ S, hdeg, x, lt_of_not_ge hx⟩
      simp only [hS, not_false_eq_true, if_true, hdeg, hsmall, and_self]
      rw [component_sq_mean hp0 hp1]
  · have hS : S ∉ HatamiActivation.significantSets p f k η := by
      intro h
      exact hdeg (Finset.mem_filter.mp h).2.1
    simp [hS, lt_of_not_ge hdeg, hdeg]
