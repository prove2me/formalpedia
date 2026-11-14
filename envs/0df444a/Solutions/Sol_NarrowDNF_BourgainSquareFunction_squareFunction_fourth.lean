-- Prove2me | solution 1 for NarrowDNF.BourgainSquareFunction.squareFunction_fourth
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:26:28.077589+00:00
-- url     : https://prove2.me/submissions/d6de8865-8dd1-4f4f-b6ae-96e64cd115f3

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_BourgainNoise
import Definitions.Def_NarrowDNF_BourgainSquareFunction
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_BourgainNoise_finite_negative_fourth_contraction
import Theorems.Thm_NarrowDNF_BourgainNoise_finite_positive_fourth_contraction
import Theorems.Thm_NarrowDNF_BourgainSquareFunction_low_degree_le_damped
import Theorems.Thm_NarrowDNF_Fourier_expansion
import Theorems.Thm_NarrowDNF_Fourier_inner_parseval
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split

namespace NarrowDNF.BourgainNoise
end NarrowDNF.BourgainNoise

namespace NarrowDNF.BourgainSquareFunction
end NarrowDNF.BourgainSquareFunction

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



















private theorem expectation_sum {κ : Type*} [Fintype κ] (p : ℝ)
    (F : κ → (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => ∑ i, F i x) =
      ∑ i, ProductMeasure.expectation p (F i) := by
  simp only [ProductMeasure.expectation, Finset.mul_sum]
  exact Finset.sum_comm



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
# Signed noise contraction for Bourgain's square-function argument

These are actual finite fourth-moment contraction theorems, uniform in the
Bernoulli bias. They do not assume a hypercontractive inequality. The negative
noise parameter is `-1/3`; using this slightly weaker parameter avoids any
unproved sharp-constant assertion from the cited appendix.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.BourgainNoise











section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem coordinate_negative_fourth_contraction {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → ℝ) (i : ι) :
    ProductMeasure.expectation p (fun x => coordinateNoise p (-1/3) f i x ^ 4) ≤
      ProductMeasure.expectation p (fun x => f x ^ 4) := by
  rw [Influence.expectation_split_inside p i, Influence.expectation_split_inside p i]
  apply ProductMeasure.expectation_mono hp0 hp1
  intro z
  have h := finite_negative_fourth_contraction
    (ProductMeasure.bitWeight p) (fun b => f (ProductMeasure.insertBit i b z))
    (ProductMeasure.bitWeight_nonneg hp0 hp1) (by simp)
  simp only [Fintype.sum_bool, ProductMeasure.bitWeight_true,
    ProductMeasure.bitWeight_false] at h
  simp only [coordinateNoise, Fourier.coordinateMean, Fourier.coordinateResidual,
    Influence.update_insertBit]
  convert h using 1 <;> ring

private theorem coordinate_positive_fourth_contraction {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → ℝ) (i : ι) :
    ProductMeasure.expectation p (fun x => coordinateNoise p (1/3) f i x ^ 4) ≤
      ProductMeasure.expectation p (fun x => f x ^ 4) := by
  rw [Influence.expectation_split_inside p i, Influence.expectation_split_inside p i]
  apply ProductMeasure.expectation_mono hp0 hp1
  intro z
  have h := finite_positive_fourth_contraction
    (ProductMeasure.bitWeight p) (fun b => f (ProductMeasure.insertBit i b z))
    (ProductMeasure.bitWeight_nonneg hp0 hp1) (by simp)
  simp only [Fintype.sum_bool, ProductMeasure.bitWeight_true,
    ProductMeasure.bitWeight_false] at h
  simp only [coordinateNoise, Fourier.coordinateMean, Fourier.coordinateResidual,
    Influence.update_insertBit]
  convert h using 1 <;> ring



/-- Tensorization of the signed-noise fourth-moment estimate, including
arbitrary repeated coordinates. -/
private theorem noiseList_fourth_contraction {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : ι → ℝ) (hρ : ∀ i, ρ i = 1/3 ∨ ρ i = -1/3)
    (L : List ι) (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => noiseList p ρ L f x ^ 4) ≤
      ProductMeasure.expectation p (fun x => f x ^ 4) := by
  induction L with
  | nil => exact le_rfl
  | cons i L ih =>
    simp only [noiseList]
    refine le_trans ?_ ih
    rcases hρ i with h | h <;> rw [h]
    · exact coordinate_positive_fourth_contraction hp0 hp1 _ i
    · exact coordinate_negative_fourth_contraction hp0 hp1 _ i

/-- The exact coordinate-noise multiplier on the biased Fourier transform. -/
private theorem coefficient_coordinateNoise (p ρ : ℝ) (f : (ι → Bool) → ℝ)
    (i : ι) (s : ι → Bool) :
    Fourier.coefficient p (coordinateNoise p ρ f i) s =
      (if s i then ρ else 1) * Fourier.coefficient p f s := by
  unfold coordinateNoise Fourier.coefficient
  simp_rw [add_mul, mul_assoc]
  rw [ProductMeasure.expectation_add, ProductMeasure.expectation_const_mul,
    Fourier.coordinateMean_selfAdjoint]
  simp_rw [Fourier.coordinateMean_character]
  change ProductMeasure.expectation p
      (fun x => f x * (if s i then 0 else Fourier.character p s x)) +
      ρ * Fourier.coefficient p (Fourier.coordinateResidual p f i) s = _
  rw [Fourier.coefficient_coordinateResidual]
  cases s i <;> simp [Fourier.coefficient]

/-- Fourier multipliers of a finite sequence multiply. -/
private theorem coefficient_noiseList (p : ℝ) (ρ : ι → ℝ) (L : List ι)
    (f : (ι → Bool) → ℝ) (s : ι → Bool) :
    Fourier.coefficient p (noiseList p ρ L f) s =
      (L.map (fun i => if s i then ρ i else 1)).prod * Fourier.coefficient p f s := by
  induction L with
  | nil => simp [noiseList]
  | cons i L ih =>
    simp only [noiseList, coefficient_coordinateNoise, ih, List.map_cons, List.prod_cons]
    ring



/-- The spectral expression is the composition of the actual coordinate operators. -/
private theorem tensorNoise_eq_noiseList {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : ι → ℝ) (f : (ι → Bool) → ℝ) :
    tensorNoise p ρ f = noiseList p ρ Finset.univ.toList f := by
  funext x
  rw [← Fourier.expansion hp0 hp1 (noiseList p ρ Finset.univ.toList f) x]
  unfold tensorNoise
  apply Finset.sum_congr rfl
  intro s _
  rw [coefficient_noiseList]
  simp

/-- Full arbitrary-dimensional signed-noise L4 contraction. -/
private theorem tensorNoise_fourth_contraction {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : ι → ℝ) (hρ : ∀ i, ρ i = 1/3 ∨ ρ i = -1/3)
    (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => tensorNoise p ρ f x ^ 4) ≤
      ProductMeasure.expectation p (fun x => f x ^ 4) := by
  rw [tensorNoise_eq_noiseList hp0 hp1]
  exact noiseList_fourth_contraction hp0.le hp1.le ρ hρ _ f











end Cube
end NarrowDNF.BourgainNoise

end

end

section


/-!
# Dimension-free low-degree square functions

This file derives the square functions needed in Bourgain's argument from
actual signed-noise contractions and the proved uniform-cube Bonami theorem.
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.BourgainSquareFunction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



/-- Fourier coefficients of a synthesized expansion are its actual coefficients. -/
private theorem coefficient_synthesis {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (a : (ι → Bool) → ℝ) (s : ι → Bool) :
    Fourier.coefficient p (synthesis p a) s = a s := by
  unfold Fourier.coefficient synthesis
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Influence.expectation_sum]
  simp_rw [ProductMeasure.expectation_const_mul, Fourier.orthogonality hp0 hp1]
  simp



omit [DecidableEq ι] in
/-- Constant-coordinate multipliers are degree powers. -/
private theorem product_constant_mask (ρ : ℝ) (s : ι → Bool) :
    (∏ i, if s i then ρ else 1) = ρ ^ Fourier.degree s := by
  simp [Fourier.degree, ← Finset.prod_filter]

/-- The normalized unbiased bit takes the values minus and plus one. -/
private theorem standardBit_half (b : Bool) : Fourier.standardBit (1/2) b = if b then 1 else -1 := by
  cases b <;> norm_num [Fourier.standardBit]



omit [DecidableEq ι] in
/-- Factor the signed multiplier into its degree decay and a Walsh character. -/
private theorem signed_multiplier (s y : ι → Bool) :
    (∏ i, if s i then Fourier.standardBit (1/2) (y i) / 3 else 1) =
      (1/3 : ℝ) ^ Fourier.degree s * Fourier.character (1/2) s y := by
  rw [← product_constant_mask]
  unfold Fourier.character
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> simp [Fourier.bitBasis]; ring

/-- In the sign coordinates, the signed-noise expansion has explicit
coefficients equal to the original pointwise components times the decay. -/
private theorem signedNoise_eq_synthesis (p : ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    (fun y => signedNoise p f y x) = synthesis (1/2)
      (fun s => (1/3 : ℝ) ^ Fourier.degree s *
        (Fourier.coefficient p f s * Fourier.character p s x)) := by
  funext y
  unfold signedNoise BourgainNoise.tensorNoise synthesis
  apply Finset.sum_congr rfl
  intro s _
  rw [signed_multiplier]
  ring

private theorem signedNoise_coefficient (p : ℝ) (f : (ι → Bool) → ℝ) (s x : ι → Bool) :
    Fourier.coefficient (1/2) (fun y => signedNoise p f y x) s =
      (1/3 : ℝ) ^ Fourier.degree s *
        (Fourier.coefficient p f s * Fourier.character p s x) := by
  rw [signedNoise_eq_synthesis]
  exact coefficient_synthesis (by norm_num) (by norm_num) _ _

/-- For every fixed choice of the signs, the fourth moment contracts. -/
private theorem signedNoise_fourth_contraction {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (y : ι → Bool) :
    ProductMeasure.expectation p (fun x => signedNoise p f y x ^ 4) ≤
      ProductMeasure.expectation p (fun x => f x ^ 4) := by
  apply BourgainNoise.tensorNoise_fourth_contraction hp0 hp1
  intro i
  rw [standardBit_half]
  cases y i <;> norm_num





private theorem squareFunction_nonneg (p : ℝ) (f : (ι → Bool) → ℝ) (k : ℕ) (x : ι → Bool) :
    0 ≤ squareFunction p f k x := Finset.sum_nonneg fun _ _ => sq_nonneg _



/-- Second sign moment of signed noise, exactly. -/
private theorem signedNoise_second_moment (p : ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    ProductMeasure.expectation (1/2) (fun y => signedNoise p f y x ^ 2) =
      ∑ s, (Fourier.coefficient p f s * Fourier.character p s x)^2 /
        (3 : ℝ)^(2 * Fourier.degree s) := by
  rw [Fourier.parseval (by norm_num) (by norm_num)]
  apply Finset.sum_congr rfl
  intro s _
  rw [signedNoise_coefficient]
  simp only [mul_pow, div_pow, one_pow]
  rw [← pow_mul, Nat.mul_comm (Fourier.degree s) 2]
  ring



/-- A finite-probability Jensen inequality, derived by Cauchy–Schwarz. -/
private theorem secondMoment_sq_le_fourthMoment {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → ℝ) :
    (ProductMeasure.expectation p (fun x => f x ^ 2))^2 ≤
      ProductMeasure.expectation p (fun x => f x ^ 4) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (r := fun x : ι → Bool => ProductMeasure.weight p x * f x^2)
    (f := fun x => ProductMeasure.weight p x * f x^4)
    (g := fun x => ProductMeasure.weight p x)
    (fun x _ => mul_nonneg (ProductMeasure.weight_nonneg hp0 hp1 x) (by positivity))
    (fun x _ => ProductMeasure.weight_nonneg hp0 hp1 x)
    (fun x _ => by ring)
  simpa only [ProductMeasure.expectation, ProductMeasure.sum_weight, mul_one] using h

/-- Finite Fubini for independent cubes with possibly different biases. -/
private theorem expectation_comm (p q : ℝ) (F : (ι → Bool) → (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => ProductMeasure.expectation q (F x)) =
      ProductMeasure.expectation q (fun y => ProductMeasure.expectation p (fun x => F x y)) := by
  unfold ProductMeasure.expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring





























end NarrowDNF.BourgainSquareFunction

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainSquareFunction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Dimension-free fourth moment of the low-degree square function. This is
an actual theorem for every real-valued function, uniform in the bias. -/
theorem solution {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (k : ℕ) :
    ProductMeasure.expectation p (fun x => squareFunction p f k x ^ 2) ≤
      (3 : ℝ)^(4*k) * ProductMeasure.expectation p (fun x => f x ^ 4) := by
  have hpoint (x : ι → Bool) : squareFunction p f k x ^ 2 ≤
      (3 : ℝ)^(4*k) * ProductMeasure.expectation (1/2) (fun y => signedNoise p f y x ^ 4) := by
    have hd := low_degree_le_damped
      (fun s => Fourier.coefficient p f s * Fourier.character p s x) k 2
    rw [← signedNoise_second_moment] at hd
    have hs := pow_le_pow_left₀ (squareFunction_nonneg p f k x) hd 2
    rw [mul_pow, ← pow_mul] at hs
    have hpow : 2*k*2 = 4*k := by omega
    rw [hpow] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left
      (secondMoment_sq_le_fourthMoment (by norm_num) (by norm_num) _)
      (by positivity))
  calc
    _ ≤ ProductMeasure.expectation p (fun x =>
        (3 : ℝ)^(4*k) * ProductMeasure.expectation (1/2) (fun y => signedNoise p f y x ^ 4)) :=
      ProductMeasure.expectation_mono hp0.le hp1.le hpoint
    _ = (3 : ℝ)^(4*k) * ProductMeasure.expectation (1/2)
        (fun y => ProductMeasure.expectation p (fun x => signedNoise p f y x ^ 4)) := by
      rw [ProductMeasure.expectation_const_mul, expectation_comm]
    _ ≤ (3 : ℝ)^(4*k) * ProductMeasure.expectation (1/2)
        (fun _ : ι → Bool => ProductMeasure.expectation p (fun x => f x ^ 4)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact ProductMeasure.expectation_mono (by norm_num) (by norm_num)
        (signedNoise_fourth_contraction hp0 hp1 f)
    _ = _ := by rw [ProductMeasure.expectation_const]
