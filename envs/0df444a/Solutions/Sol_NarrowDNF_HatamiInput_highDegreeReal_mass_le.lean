-- Prove2me | solution 1 for NarrowDNF.HatamiInput.highDegreeReal_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:32:38.024604+00:00
-- url     : https://prove2.me/submissions/da842e6f-9e82-4ca1-9ad0-34c744617876

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
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_FiberShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Fourier_inner_parseval
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.HatamiInput
end NarrowDNF.HatamiInput

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














@[simp] private theorem degree_maskEquivFinset_symm (S : Finset ι) :
    degree (maskEquivFinset.symm S) = S.card :=
  congrArg Finset.card (maskEquivFinset.apply_symm_apply S)


























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

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiInput
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Real-cutoff high-frequency bound with the exact factor two from
resampling influence. -/
theorem solution {p k : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hk : 0 < k) (f : Cube ι → Bool) :
    (∑ S : Finset ι, if k < (S.card : ℝ) then
      Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2 else 0) ≤
        Influence.totalInfluence p f / (2*k) := by
  classical
  have hweighted : k * (∑ S : Finset ι, if k < (S.card : ℝ) then
      Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2 else 0) ≤
      ∑ S : Finset ι, (S.card : ℝ) *
        Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S _
    split_ifs with hS
    · exact mul_le_mul_of_nonneg_right hS.le (sq_nonneg _)
    · simpa only [mul_zero] using mul_nonneg (Nat.cast_nonneg S.card)
        (sq_nonneg (Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S))
  apply (le_div_iff₀ (by positivity : 0 < 2*k)).mpr
  rw [Fourier.totalInfluence_spectral_finset hp0 hp1]
  nlinarith
