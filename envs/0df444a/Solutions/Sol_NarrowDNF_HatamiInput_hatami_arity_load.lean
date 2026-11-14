-- Prove2me | solution 1 for NarrowDNF.HatamiInput.hatami_arity_load
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T09:02:42.255208+00:00
-- url     : https://prove2.me/submissions/2124148a-647e-49dc-9027-3cf658eeba60

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ActivationLoad
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_FiberShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_HatamiInput
import Definitions.Def_NarrowDNF_HatamiParameters
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_MainStatements
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Activation_sameAtom_of_active_subset_of_agree
import Theorems.Thm_NarrowDNF_ConditionalExpectation_adaptiveCode_eq_iff
import Theorems.Thm_NarrowDNF_ConditionalExpectation_squaredError_decomposition
import Theorems.Thm_NarrowDNF_Fourier_eq_mean_of_variance_le_zero
import Theorems.Thm_NarrowDNF_Fourier_inner_parseval
import Theorems.Thm_NarrowDNF_Fourier_variance_le_spectralEnergy
import Theorems.Thm_NarrowDNF_HatamiActivation_sum_componentTailMass_le
import Theorems.Thm_NarrowDNF_HatamiActivation_threshold_load_le
import Theorems.Thm_NarrowDNF_HatamiInput_paper_approxTruncated_error_le
import Theorems.Thm_NarrowDNF_HatamiInput_paper_truncation_error_le
import Theorems.Thm_NarrowDNF_HatamiParameters_loadExpression_le_exp
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.ConditionalExpectation
end NarrowDNF.ConditionalExpectation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.HatamiInput
end NarrowDNF.HatamiInput

namespace NarrowDNF.HatamiParameters
end NarrowDNF.HatamiParameters

namespace NarrowDNF.HatamiResidual
end NarrowDNF.HatamiResidual

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

private theorem bitWeight_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (b : Bool) :
    0 < bitWeight p b := by
  cases b <;> simp only [bitWeight_false, bitWeight_true]
  · exact sub_pos.mpr hp1
  · exact hp0

omit [DecidableEq ι] in
private theorem weight_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : ι → Bool) :
    0 < weight p x :=
  Finset.prod_pos fun i _ => bitWeight_pos hp0 hp1 (x i)

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



end NarrowDNF.ProductMeasure

end

end

section


/-!
# Conditional expectation on a finite partition

A partition is represented by a map `φ : α → β`; each realized fiber has
positive mass when the input weights are strictly positive. This file derives
least-squares projection and Boolean threshold rounding from finite sums. It
does not assume Hatami's construction-specific residual bound.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ConditionalExpectation

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]



























omit [Fintype β] in
private theorem conditional_eq_of_atom_eq (φ : α → β) (w F : α → ℝ)
    {a a' : α} (h : φ a = φ a') : conditional φ w F a = conditional φ w F a' := by
  simp only [conditional, h]

omit [Fintype β] in
private theorem decoder_eq_of_atom_eq (φ : α → β) (w : α → ℝ) (f : α → Bool)
    {a a' : α} (h : φ a = φ a') : decoder φ w f a = decoder φ w f a' := by
  unfold decoder
  rw [conditional_eq_of_atom_eq φ w _ h]





/-- Conditional expectation is a least-squares projection onto atom readouts. -/
private theorem squaredError_minimal (φ : α → β) (w F : α → ℝ)
    (hw : ∀ a, 0 < w a) (G : β → ℝ) :
    squaredError w F (conditional φ w F) ≤ squaredError w F (fun a => G (φ a)) := by
  rw [squaredError_decomposition φ w F hw G]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun a _ => mul_nonneg (hw a).le (sq_nonneg _))

/-- The pointwise factor-four Boolean rounding inequality; no range assumption
on the real approximator is necessary. -/
private theorem threshold_error_le (b : Bool) (m : ℝ) :
    (if b = threshold m then (0:ℝ) else 1) ≤ 4 * (value b - m)^2 := by
  by_cases hm : (1/2:ℝ) < m
  · have ht : threshold m = true := by exact decide_eq_true hm
    cases b <;> rw [ht] <;> norm_num [value] <;> nlinarith [sq_nonneg (m-1/2)]
  · have hm' : m ≤ (1/2:ℝ) := le_of_not_gt hm
    have ht : threshold m = false := by exact decide_eq_false hm
    cases b <;> rw [ht] <;> norm_num [value] <;> nlinarith [sq_nonneg (m-1/2)]

omit [Fintype β] in
/-- Thresholding the conditional mean costs at most four times its squared residual. -/
private theorem decoder_error_le_four (φ : α → β) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (f : α → Bool) :
    booleanError w f (decoder φ w f) ≤
      4 * squaredError w (fun a => value (f a)) (conditional φ w (fun a => value (f a))) := by
  unfold booleanError squaredError
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have h := mul_le_mul_of_nonneg_left
    (threshold_error_le (f a) (conditional φ w (fun a => value (f a)) a)) (hw a)
  change w a * (if f a = threshold (conditional φ w (fun x => value (f x)) a) then 0 else 1) ≤ _
  calc
    _ ≤ w a * (4 * (value (f a) - conditional φ w (fun x => value (f x)) a)^2) := h
    _ = _ := by ring







omit [Fintype β] in
/-- A real function constant on partition fibers has a global readout map. -/
private theorem exists_readout (φ : α → β) (G : α → ℝ)
    (hG : ∀ x y, φ x = φ y → G x = G y) :
    ∃ g : β → ℝ, ∀ x, G x = g (φ x) := by
  classical
  let g : β → ℝ := fun b => if h : ∃ a, φ a = b then G h.choose else 0
  refine ⟨g, ?_⟩
  intro x
  have h : ∃ a, φ a = φ x := ⟨x,rfl⟩
  simp only [g, dif_pos h]
  exact (hG h.choose x h.choose_spec).symm

/-- Least-squares optimality for any fiber-measurable function, without requiring
its readout map as an additional argument. -/
private theorem squaredError_minimal_of_measurable (φ : α → β) (w F G : α → ℝ)
    (hw : ∀ a, 0 < w a) (hG : ∀ x y, φ x = φ y → G x = G y) :
    squaredError w F (conditional φ w F) ≤ squaredError w F G := by
  obtain ⟨g,hg⟩ := exists_readout φ G hG
  have heq : G = fun a => g (φ a) := funext hg
  rw [heq]
  exact squaredError_minimal φ w F hw g

section Adaptive
variable {ι : Type*} [Fintype ι] [DecidableEq ι]









private theorem adaptiveDecoder_measurable (p : ℝ) (J : Activation ι) (f : Cube ι → Bool) :
    J.Measurable (adaptiveDecoder p J f) := by
  classical
  intro x y hxy
  apply decoder_eq_of_atom_eq
  exact (adaptiveCode_eq_iff J x y).mpr hxy

/-- The final thresholding step of Appendix A, with the residual left explicit. -/
private theorem adaptiveDecoder_error_le_four {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (J : Activation ι) (f : Cube ι → Bool) :
    ProductMeasure.error p f (adaptiveDecoder p J f) ≤
      4 * ProductMeasure.expectation p (fun x => (value (f x) - adaptiveMean p J f x)^2) := by
  classical
  have h := decoder_error_le_four (adaptiveCode J) (ProductMeasure.weight p)
    (ProductMeasure.weight_nonneg hp0 hp1) f
  unfold booleanError squaredError decoder at h
  unfold ProductMeasure.error ProductMeasure.probability ProductMeasure.expectation
    adaptiveDecoder adaptiveMean
  simpa only [ne_eq, ite_not] using h

end Adaptive

section CoordinatePartition
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



















end CoordinatePartition
section Localization





variable {ι : Type*} [Fintype ι] [DecidableEq ι]











end Localization
end NarrowDNF.ConditionalExpectation

end

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
# Finite Bernoulli variance and resampling influence

The one-coordinate identities in this file use the paper's resampling
normalization: a pivotal Boolean fiber has influence `2 * p * (1 - p)`.
The endpoints `p = 0` and `p = 1` are included in the algebraic identities.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.Influence







/-- Exact Bernoulli variance, valid even for real endpoint values. -/
private theorem fiberVariance_eq (p a b : ℝ) :
    fiberVariance p a b = p * (1 - p) * (b - a) ^ 2 := by
  unfold fiberVariance fiberMean
  ring

/-- Squared endpoint difference of Boolean values is their disagreement indicator. -/
private theorem boolValue_sub_sq (a b : Bool) :
    (boolValue b - boolValue a) ^ 2 = FiberShift.mismatch a b := by
  cases a <;> cases b <;> norm_num [boolValue, FiberShift.mismatch]

/-- A Boolean fiber has positive conditional variance exactly when it is pivotal,
provided the Bernoulli bias is nondegenerate. -/
private theorem bool_fiberVariance_eq (p : ℝ) (a b : Bool) :
    fiberVariance p (boolValue a) (boolValue b) =
      p * (1 - p) * FiberShift.mismatch a b := by
  rw [fiberVariance_eq, boolValue_sub_sq]



private theorem fiberResampling_eq (p : ℝ) (a b : Bool) :
    fiberResampling p a b = 2 * p * (1 - p) * FiberShift.mismatch a b := by
  cases a <;> cases b <;> simp [fiberResampling, FiberShift.mismatch] <;> ring

/-- The factor of two in the paper's influence convention. -/
private theorem fiberResampling_eq_twice_variance (p : ℝ) (a b : Bool) :
    fiberResampling p a b = 2 * fiberVariance p (boolValue a) (boolValue b) := by
  rw [fiberResampling_eq, bool_fiberVariance_eq]
  ring


/-- The square of a Boolean numerical value is itself. -/
@[simp] private theorem boolValue_sq (b : Bool) : boolValue b ^ 2 = boolValue b := by
  cases b <;> norm_num [boolValue]

private theorem boolValue_injective : Function.Injective boolValue := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolValue]

section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]







omit [Fintype ι] in
/-- Replacing an inserted coordinate keeps the complementary input fixed. -/
private theorem update_insertBit (i : ι) (b c : Bool) (z : {j // j ≠ i} → Bool) :
    Function.update (ProductMeasure.insertBit i b z) i c =
      ProductMeasure.insertBit i c z := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simpa [Function.update_of_ne h] using
      (ProductMeasure.insertBit_away i b z ⟨j,h⟩).trans
        (ProductMeasure.insertBit_away i c z ⟨j,h⟩).symm

/-- Disintegration with the two fiber contributions inside one expectation. -/
private theorem expectation_split_inside (p : ℝ) (i : ι) (F : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p F = ProductMeasure.expectation p (fun z =>
      (1-p) * F (ProductMeasure.insertBit i false z) +
        p * F (ProductMeasure.insertBit i true z)) := by
  rw [ProductMeasure.expectation_add, ProductMeasure.expectation_const_mul,
    ProductMeasure.expectation_const_mul]
  exact ProductMeasure.expectation_split p i F





private theorem resamplingInfluence_eq_fiber (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    resamplingInfluence p f i = ProductMeasure.expectation p (fun z =>
      fiberResampling p (f (ProductMeasure.insertBit i false z))
        (f (ProductMeasure.insertBit i true z))) := by
  unfold resamplingInfluence
  rw [expectation_split_inside p i]
  simp only [update_insertBit, fiberResampling]





private theorem resamplingInfluence_eq_twice_coordinateVariance
    (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    resamplingInfluence p f i = 2 * coordinateVariance p (fun x => boolValue (f x)) i := by
  rw [resamplingInfluence_eq_fiber]
  simp_rw [fiberResampling_eq_twice_variance]
  exact ProductMeasure.expectation_const_mul p 2 _











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
















/-- Parseval: squared L2 norm equals total squared Fourier mass. -/
private theorem parseval {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => f x ^ 2) =
      ∑ s : ι → Bool, coefficient p f s ^ 2 := by
  simpa only [pow_two] using inner_parseval hp0 hp1 f f






private theorem character_split (p : ℝ) (s x : ι → Bool) (i : ι) :
    character p s x = bitBasis p (s i) (x i) *
      ∏ j : {j // j ≠ i}, bitBasis p (s j) (x j) :=
  Fintype.prod_eq_mul_prod_subtype_ne (fun j => bitBasis p (s j) (x j)) i

private theorem character_update (p : ℝ) (s x : ι → Bool) (i : ι) (b : Bool) :
    character p s (Function.update x i b) = bitBasis p (s i) b *
      ∏ j : {j // j ≠ i}, bitBasis p (s j) (x j) := by
  rw [character_split p s _ i]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [Function.update_of_ne j.property]

/-- Conditional averaging kills exactly the basis functions using that coordinate. -/
private theorem coordinateMean_character (p : ℝ) (s x : ι → Bool) (i : ι) :
    coordinateMean p (character p s) i x = if s i then 0 else character p s x := by
  unfold coordinateMean
  rw [character_update, character_update]
  rw [character_split p s x i]
  cases s i <;> simp [bitBasis, standardBit, div_eq_mul_inv] <;> ring

private theorem expectation_sub (p : ℝ) (f g : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => f x - g x) =
      ProductMeasure.expectation p f - ProductMeasure.expectation p g := by
  simp [ProductMeasure.expectation, mul_sub, Finset.sum_sub_distrib]

/-- Conditional expectation is self-adjoint for the finite weighted inner product. -/
private theorem coordinateMean_selfAdjoint (p : ℝ) (f g : (ι → Bool) → ℝ) (i : ι) :
    ProductMeasure.expectation p (fun x => coordinateMean p f i x * g x) =
      ProductMeasure.expectation p (fun x => f x * coordinateMean p g i x) := by
  rw [Influence.expectation_split_inside p i,
    Influence.expectation_split_inside p i]
  congr 1
  funext z
  simp only [coordinateMean, Influence.update_insertBit]
  ring

/-- The Fourier multiplier of the coordinate residual is the coordinate's support bit. -/
private theorem coefficient_coordinateResidual (p : ℝ) (f : (ι → Bool) → ℝ)
    (i : ι) (s : ι → Bool) :
    coefficient p (coordinateResidual p f i) s = if s i then coefficient p f s else 0 := by
  unfold coefficient coordinateResidual
  simp_rw [sub_mul]
  rw [expectation_sub, coordinateMean_selfAdjoint]
  simp_rw [coordinateMean_character]
  cases s i <;> simp

/-- Squared L2 norm of the coordinate residual is averaged conditional variance. -/
private theorem residual_sq_eq_coordinateVariance (p : ℝ) (f : (ι → Bool) → ℝ) (i : ι) :
    ProductMeasure.expectation p (fun x => coordinateResidual p f i x ^ 2) =
      Influence.coordinateVariance p f i := by
  rw [Influence.expectation_split_inside p i]
  unfold Influence.coordinateVariance
  congr 1
  funext z
  simp only [coordinateResidual, coordinateMean, Influence.update_insertBit,
    Influence.fiberVariance, Influence.fiberMean]

/-- Conditional variance equals the squared Fourier mass using the coordinate. -/
private theorem coordinateVariance_spectral {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (i : ι) :
    Influence.coordinateVariance p f i =
      ∑ s : ι → Bool, if s i then coefficient p f s ^ 2 else 0 := by
  rw [← residual_sq_eq_coordinateVariance, parseval hp0 hp1]
  simp_rw [coefficient_coordinateResidual]
  apply Finset.sum_congr rfl
  intro s _
  cases s i <;> simp

/-- Exact per-coordinate influence normalization in the biased Fourier basis. -/
private theorem resamplingInfluence_spectral {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (i : ι) :
    Influence.resamplingInfluence p f i =
      2 * ∑ s : ι → Bool, if s i then coefficient p (fun x => Influence.boolValue (f x)) s ^ 2 else 0 := by
  rw [Influence.resamplingInfluence_eq_twice_coordinateVariance,
    coordinateVariance_spectral hp0 hp1]

omit [DecidableEq ι] in
/-- Sum of the support indicators is spectral degree. -/
private theorem sum_support (s : ι → Bool) (a : ℝ) :
    (∑ i, if s i then a else 0) = (degree s : ℝ) * a := by
  classical
  simp [degree, ← Finset.sum_filter]

/-- The paper's Fourier identity, with the precise factor of two from resampling. -/
private theorem totalInfluence_spectral {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    Influence.totalInfluence p f = 2 *
      ∑ s : ι → Bool, (degree s : ℝ) *
        coefficient p (fun x => Influence.boolValue (f x)) s ^ 2 := by
  unfold Influence.totalInfluence
  simp_rw [resamplingInfluence_spectral hp0 hp1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact sum_support s _








/-- The subset-indexed form of the exact resampling spectral identity. -/
private theorem totalInfluence_spectral_finset {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    Influence.totalInfluence p f = 2 *
      ∑ S : Finset ι, (S.card : ℝ) *
        setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2 := by
  rw [totalInfluence_spectral hp0 hp1]
  congr 1
  apply Fintype.sum_equiv maskEquivFinset
  intro s
  simp only [setCoefficient, Equiv.symm_apply_apply]
  rfl










/-- The constant Fourier coefficient is the mean. -/
@[simp] private theorem coefficient_zeroMask (p : ℝ) (f : (ι → Bool) → ℝ) :
    coefficient p f (fun _ => false) = ProductMeasure.expectation p f := by
  simp [coefficient, character, bitBasis]





/-- Product Poincare in the paper's resampling convention. -/
private theorem poincare {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    Influence.variance p (fun x => Influence.boolValue (f x)) ≤
      Influence.totalInfluence p f / 2 := by
  rw [totalInfluence_spectral hp0 hp1]
  have h := variance_le_spectralEnergy hp0 hp1 (fun x => Influence.boolValue (f x))
  linarith





/-- Zero resampling influence means a Boolean function is genuinely constant,
not merely almost surely constant, because every cube point has positive mass. -/
private theorem constant_of_totalInfluence_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (hf : Influence.totalInfluence p f = 0)
    (x y : ι → Bool) : f x = f y := by
  have hv : Influence.variance p (fun z => Influence.boolValue (f z)) ≤ 0 := by
    have h := poincare hp0 hp1 f
    simpa [hf] using h
  have hx := eq_mean_of_variance_le_zero hp0 hp1 (fun z => Influence.boolValue (f z)) hv x
  have hy := eq_mean_of_variance_le_zero hp0 hp1 (fun z => Influence.boolValue (f z)) hv y
  have hxy : Influence.boolValue (f x) = Influence.boolValue (f y) := hx.trans hy.symm
  exact Influence.boolValue_injective hxy


@[simp] private theorem degree_maskEquivFinset_symm (S : Finset ι) :
    degree (maskEquivFinset.symm S) = S.card :=
  congrArg Finset.card (maskEquivFinset.apply_symm_apply S)


























end Cube
end NarrowDNF.Fourier







end

end

section


/-! Explicit numerical bounds for the parameters in Appendix A. -/
noncomputable section
namespace NarrowDNF.HatamiParameters





private theorem delta_pos (k : ℝ) : 0 < delta k := Real.rpow_pos_of_pos (by norm_num) _
private theorem epsilonOne_pos {e0 : ℝ} (he0 : 0 < e0) (k : ℝ) : 0 < epsilonOne k e0 :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos he0 _)






/-- The final L bound with exactly Appendix A's parameter definitions. -/
private theorem paper_load_bound {a C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hC : 1 ≤ C) :
    loadExpression (1000*C/a) (a/1000) ≤ Real.exp (10000000000*C^2/a^2) := by
  have he0 : 0 < a/1000 := by positivity
  have hk1 : (1:ℝ) ≤ 1000*C/a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith
  have hk : (a/1000)⁻¹ ≤ 1000*C/a := by
    rw [inv_div]
    apply div_le_div_of_nonneg_right _ ha.le
    nlinarith
  have h := loadExpression_le_exp he0 hk1 hk
  convert h using 1; congr 1; ring






end NarrowDNF.HatamiParameters

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















private theorem bitWeight_antitone {p : ℝ} (hp : p ≤ 1/2) : Antitone (bitWeight p) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [bitWeight, Bool.le_iff_imp]; linarith

omit [Fintype ι] [DecidableEq ι] in
private theorem localMass_antitone {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (T : Finset ι) : Antitone (localMass p T) := by
  intro x y hxy
  apply Finset.prod_le_prod
  · intro i _
    exact bitWeight_nonneg hp0 (by linarith) _
  · intro i _
    exact bitWeight_antitone hp (hxy i)

omit [Fintype ι] in
private theorem thresholdActivation_increasing {k p δ : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hδ : 0 ≤ δ)
    (retained : Finset (Finset ι)) (m : Finset ι → ℝ) :
    (thresholdActivation k p δ retained m).Increasing := by
  intro T x y hxy hx
  exact ⟨hx.1, (mul_le_mul_of_nonneg_left (localMass_antitone hp0 hp T hxy) hδ).trans hx.2⟩

omit [Fintype ι] in
private theorem thresholdActivation_arity {k p δ : ℝ} (d : ℕ) (hkd : k ≤ (d : ℝ))
    (retained : Finset (Finset ι)) (m : Finset ι → ℝ) :
    (thresholdActivation k p δ retained m).ArityLE d := by
  intro T hT x hx
  have hc : (d : ℝ) < T.card := by exact_mod_cast hT
  exact (not_le_of_gt hc) (hx.1.trans hkd)

omit [Fintype ι] in
private theorem thresholdActivation_arity_ceil (k p δ : ℝ)
    (retained : Finset (Finset ι)) (m : Finset ι → ℝ) :
    (thresholdActivation k p δ retained m).ArityLE (Nat.ceil k) :=
  thresholdActivation_arity _ (Nat.le_ceil k) retained m

omit [Fintype ι] in
@[simp] private theorem localMass_extendLocal (p : ℝ) (T : Finset ι) (z : T → Bool) :
    localMass p T (Activation.extendLocal T z) = weight p z := by
  unfold localMass
  congr 1
  funext i
  simp [Activation.extendLocal, i.property]























private theorem significantSets_card (p : ℝ) (f : Cube ι → ℝ) (k η : ℝ)
    (S : Finset ι) (hS : S ∈ significantSets p f k η) : (S.card : ℝ) ≤ k :=
  (Finset.mem_filter.mp hS).2.1

private theorem componentTailMass_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Cube ι → ℝ) (η : ℝ) (S : Finset ι) : 0 ≤ componentTailMass p f η S :=
  probability_nonneg hp0 hp1 _



















private theorem fourierActivation_increasing {k p δ η : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hδ : 0 ≤ δ) (f : Cube ι → ℝ) :
    (fourierActivation k p δ η f).Increasing :=
  thresholdActivation_increasing hp0 hp hδ _ _

private theorem fourierActivation_arity (k p δ η : ℝ) (f : Cube ι → ℝ) :
    (fourierActivation k p δ η f).ArityLE (Nat.ceil k) :=
  thresholdActivation_arity_ceil k p δ _ _

/-- The complete Fourier-specialized multiplicity load estimate of Appendix A. -/
private theorem fourierActivation_load_le {k p δ η : ℝ} (hk0 : 0 ≤ k)
    (hp0 : 0 < p) (hp1 : p < 1) (hδ : 0 < δ) (hη : 0 < η)
    (f : Cube ι → Bool) :
    (fourierActivation k p δ η (fun x => Influence.boolValue (f x))).load p ≤
      k * (2 : ℝ)^(2*k) / (δ * η^2) := by
  apply le_trans (threshold_load_le hk0 hδ _ _
    (fun S _ => componentTailMass_nonneg hp0.le hp1.le _ η S)
    (fun S hS => significantSets_card p _ k η S hS))
  calc
    _ ≤ (k * (2 : ℝ)^(2*k) / δ) * (1 / η^2) :=
      mul_le_mul_of_nonneg_left (sum_componentTailMass_le hp0 hp1 hη f _)
        (by positivity)
    _ = _ := by ring





/-- The explicit family is local by construction, increasing in the low-bias
range, has the stated arity, and satisfies the exact final exponential load. -/
private theorem paperActivation_properties {a C p : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hC : 1 ≤ C) (hp0 : 0 < p) (hp : p ≤ 1/2) (f : Cube ι → Bool) :
    (paperActivation a C p f).Increasing ∧
      (paperActivation a C p f).ArityLE (Nat.ceil (1000*C/a)) ∧
      (paperActivation a C p f).load p ≤ Real.exp (10000000000*C^2/a^2) := by
  have hk0 : 0 ≤ 1000*C/a := by positivity
  have hδ := HatamiParameters.delta_pos (1000*C/a)
  have hη := HatamiParameters.epsilonOne_pos (by positivity : 0 < a/1000) (1000*C/a)
  refine ⟨fourierActivation_increasing hp0.le hp hδ.le _,
    fourierActivation_arity _ _ _ _ _, ?_⟩
  exact (fourierActivation_load_le hk0 hp0 (by linarith) hδ hη f).trans
    (HatamiParameters.paper_load_bound ha ha1 hC)







end NarrowDNF.HatamiActivation

end

end

section


/-!
# Hatami's actual restricted-activation conditional components

This file formalizes the Step III/IV construction using actual adaptive atom
labels. `approxComponent` is conditional expectation onto the family retaining
only activations whose index is contained in the component's support. Generic
projection and diagonal estimates are proved here. Construction-specific
cross-term bounds are stated only when proved; no analytic estimate is an axiom.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.HatamiResidual

open ProductMeasure
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





omit [Fintype ι] [DecidableEq ι] in
private theorem restrict_active_subset_original (J : Activation ι) (S : Finset ι) (x : Cube ι) :
    (restrict J S).active x ⊆ J.active x := by
  rintro i ⟨T,hi,hT⟩
  exact ⟨T,hi,hT.2⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The restricted adaptive partition is genuinely coarser than the original one. -/
private theorem restrict_sameAtom (J : Activation ι) (S : Finset ι) {x y : Cube ι}
    (hxy : J.SameAtom x y) : (restrict J S).SameAtom x y := by
  apply Activation.sameAtom_of_active_subset_of_agree
    (B := J.active x) (restrict_active_subset_original J S x)
  · rw [hxy.1]
    exact restrict_active_subset_original J S y
  · exact hxy.2















private theorem approxComponent_measurable (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (S : Finset ι) (x y : Cube ι) (hxy : J.SameAtom x y) :
    approxComponent p J f S x = approxComponent p J f S y := by
  apply ConditionalExpectation.conditional_eq_of_atom_eq
  exact (ConditionalExpectation.adaptiveCode_eq_iff _ x y).mpr (restrict_sameAtom J S hxy)

private theorem approxTruncated_measurable (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (retained : Finset (Finset ι)) (x y : Cube ι) (hxy : J.SameAtom x y) :
    approxTruncated p J f retained x = approxTruncated p J f retained y := by
  apply Finset.sum_congr rfl
  intro S _
  exact approxComponent_measurable p J f S x y hxy



section Generic
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]



/-- Weighted squared-error triangle inequality with the sharp elementary factor two. -/
private theorem squaredError_triangle_two (w F G H : α → ℝ) (hw : ∀ a, 0 ≤ w a) :
    ConditionalExpectation.squaredError w F H ≤
      2 * ConditionalExpectation.squaredError w F G +
        2 * ConditionalExpectation.squaredError w G H := by
  unfold ConditionalExpectation.squaredError
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have h : (F a - H a)^2 ≤ 2 * (F a-G a)^2 + 2 * (G a-H a)^2 := by
    nlinarith [sq_nonneg (F a - 2*G a + H a)]
  have hm := mul_le_mul_of_nonneg_left h (hw a)
  nlinarith

end Generic









/-- Step IV's projection/triangle argument, before substituting the analytic estimates. -/
private theorem final_residual_le_two_errors {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → ℝ) (retained : Finset (Finset ι)) :
    ConditionalExpectation.squaredError (weight p) f (adaptiveConditional p J f) ≤
      2 * ConditionalExpectation.squaredError (weight p) f (truncated p f retained) +
      2 * ConditionalExpectation.squaredError (weight p) (truncated p f retained)
        (approxTruncated p J f retained) := by
  apply le_trans (ConditionalExpectation.squaredError_minimal_of_measurable
    (ConditionalExpectation.adaptiveCode J) (weight p) f (approxTruncated p J f retained)
    (weight_pos hp0 hp1) (fun x y hxy => approxTruncated_measurable p J f retained x y
      ((ConditionalExpectation.adaptiveCode_eq_iff J x y).mp hxy)))
  exact squaredError_triangle_two _ _ _ _ (weight_nonneg hp0.le hp1.le)

/-- The exact Step IV numerical implication. Its two norm hypotheses are explicit
and must be discharged for the same retained family and the same activation family. -/
private theorem final_residual_le_ten {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → ℝ) (retained : Finset (Finset ι)) (ε0 : ℝ)
    (htrunc : ConditionalExpectation.squaredError (weight p) f (truncated p f retained) ≤ 2*ε0)
    (happrox : ConditionalExpectation.squaredError (weight p) (truncated p f retained)
      (approxTruncated p J f retained) ≤ 3*ε0) :
    ConditionalExpectation.squaredError (weight p) f (adaptiveConditional p J f) ≤ 10*ε0 := by
  have h := final_residual_le_two_errors hp0 hp1 J f retained
  linarith






section GenericBound
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]



end GenericBound





















section GenericMeanBound
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]







end GenericMeanBound











end NarrowDNF.HatamiResidual




end

end

section


/-!
# Hatami's quantitative activation input

Assembly of the actual Fourier truncation, the reconstructed Bourgain estimate,
the repaired adaptive residual proof, and threshold decoding for Lemma 2.1.
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.HatamiInput
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Nonnegativity of the actual total resampling influence. -/
private theorem totalInfluence_nonneg {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube ι → Bool) : 0 ≤ Influence.totalInfluence p f := by
  rw [Fourier.totalInfluence_spectral_finset hp0 hp1]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun S _ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))











/-- Empty activations have zero load and satisfy every arity cap. -/
private theorem emptyActivation_properties (p : ℝ) (d : ℕ) :
    (emptyActivation : Activation ι).Increasing ∧
      (emptyActivation : Activation ι).ArityLE d ∧
      (emptyActivation : Activation ι).load p = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro S x y hxy hx
    exact False.elim hx
  · intro S hS x hx
    exact hx
  · simp [Activation.load, emptyActivation, ProductMeasure.probability]

/-- Zero total influence is handled without dividing by its ceiling. -/
private theorem zero_influence_input {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (f : Cube ι → Bool) (hI : Influence.totalInfluence p f = 0)
    (d : ℕ) :
    ∃ (J : Activation ι) (h : Cube ι → Bool), J.Increasing ∧
      ProductMeasure.error p f h ≤ a ∧ J.Measurable h ∧ J.ArityLE d ∧ J.load p ≤ 1 := by
  refine ⟨emptyActivation, f, (emptyActivation_properties p d).1, ?_, ?_,
    (emptyActivation_properties p d).2.1, ?_⟩
  · simpa only [ProductMeasure.error_self] using ha.le
  · intro x y _
    exact Fourier.constant_of_totalInfluence_zero hp0 hp1 f hI x y
  · rw [(emptyActivation_properties p d).2.2]
    norm_num









/-- The complete conditional-variance estimate for exactly the paper's
activation family. All Fourier and adaptive estimates have been discharged. -/
private theorem paper_conditional_variance_le {p a : ℝ} (hp0 : 0 < p) (hp : p ≤ 1/2)
    (ha : 0 < a) (ha1 : a ≤ 1) (f : Cube ι → Bool) (C : ℕ)
    (hC : 1 ≤ C) (hI : Influence.totalInfluence p f ≤ C) :
    ConditionalExpectation.squaredError (ProductMeasure.weight p)
      (fun x => Influence.boolValue (f x))
      (HatamiResidual.adaptiveConditional p (HatamiActivation.paperActivation a C p f)
        (fun x => Influence.boolValue (f x))) ≤ 10*(a/1000) := by
  apply HatamiResidual.final_residual_le_ten hp0 (by linarith)
    (HatamiActivation.paperActivation a C p f) (fun x => Influence.boolValue (f x))
    (HatamiActivation.significantSets p (fun x => Influence.boolValue (f x))
      (1000*(C : ℝ)/a) (HatamiParameters.epsilonOne (1000*(C : ℝ)/a) (a/1000)))
    (a/1000)
  · exact paper_truncation_error_le hp0 (by linarith) ha ha1 f C hC hI
  · exact paper_approxTruncated_error_le hp0 hp ha ha1 f C hC hI

/-- The actual threshold decoder for the exact source activation family has
error at most the requested a. -/
private theorem paper_decoder_error_le {p a : ℝ} (hp0 : 0 < p) (hp : p ≤ 1/2)
    (ha : 0 < a) (ha1 : a ≤ 1) (f : Cube ι → Bool) (C : ℕ)
    (hC : 1 ≤ C) (hI : Influence.totalInfluence p f ≤ C) :
    ProductMeasure.error p f
      (ConditionalExpectation.adaptiveDecoder p (HatamiActivation.paperActivation a C p f) f) ≤ a := by
  have hvariance := paper_conditional_variance_le hp0 hp ha ha1 f C hC hI
  have hround := ConditionalExpectation.adaptiveDecoder_error_le_four hp0.le (by linarith)
    (HatamiActivation.paperActivation a C p f) f
  change ProductMeasure.error p f
    (ConditionalExpectation.adaptiveDecoder p (HatamiActivation.paperActivation a C p f) f) ≤
      4 * ConditionalExpectation.squaredError (ProductMeasure.weight p)
        (fun x => Influence.boolValue (f x))
        (HatamiResidual.adaptiveConditional p (HatamiActivation.paperActivation a C p f)
          (fun x => Influence.boolValue (f x))) at hround
  linarith



end NarrowDNF.HatamiInput

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiInput
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Lemma 2.1 of the target paper, with its exact simultaneous approximation,
increasing activation, arity and multiplicity-counted load conclusions. -/
theorem solution : NarrowDNF.HatamiArityLoad := by
  classical
  intro n p hp0 hp f a ha ha1
  dsimp only
  have hp1 : p < 1 := by linarith
  by_cases hI0 : Influence.totalInfluence p f = 0
  · obtain ⟨J,h,hJ,he,hm,hd,hL⟩ := zero_influence_input hp0 hp1 ha f hI0
      (Nat.ceil (1000*(Nat.ceil (Influence.totalInfluence p f) : ℝ)/a))
    refine ⟨J,h,hJ,he,hm,hd,hL.trans ?_⟩
    exact Real.one_le_exp_iff.mpr (by positivity)
  · have hIpos : 0 < Influence.totalInfluence p f :=
      lt_of_le_of_ne (totalInfluence_nonneg hp0 hp1 f) (Ne.symm hI0)
    let C := Nat.ceil (Influence.totalInfluence p f)
    have hC : 1 ≤ C := Nat.ceil_pos.mpr hIpos
    have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC
    have hI : Influence.totalInfluence p f ≤ C := Nat.le_ceil _
    let J := HatamiActivation.paperActivation a C p f
    have hprops := HatamiActivation.paperActivation_properties ha ha1 hCr hp0 hp f
    refine ⟨J, ConditionalExpectation.adaptiveDecoder p J f, hprops.1, ?_,
      ConditionalExpectation.adaptiveDecoder_measurable p J f, hprops.2.1, hprops.2.2⟩
    exact paper_decoder_error_le hp0 hp ha ha1 f C hC hI
