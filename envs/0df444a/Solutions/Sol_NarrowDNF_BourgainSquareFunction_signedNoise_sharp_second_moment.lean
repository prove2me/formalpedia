-- Prove2me | solution 1 for NarrowDNF.BourgainSquareFunction.signedNoise_sharp_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:26:20.763811+00:00
-- url     : https://prove2.me/submissions/e7c7fb27-e183-49f8-95e8-c0f65ac00586

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
import Definitions.Def_NarrowDNF_UniformHypercontractivity
import Theorems.Thm_NarrowDNF_Fourier_inner_parseval

namespace NarrowDNF.BourgainSquareFunction
end NarrowDNF.BourgainSquareFunction

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.Hypercontractivity
end NarrowDNF.Hypercontractivity

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
# Finite L2-to-L4 hypercontractivity and its uniform-cube specialization

The moment formulation avoids fractional powers during tensorization.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.Hypercontractivity

attribute [local instance] Classical.decEq

variable {α β : Type*} [Fintype α] [Fintype β]













































private theorem sharpRho_sq : sharpRho^2 = (1/3 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)









end NarrowDNF.Hypercontractivity

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

/-- Fourier coefficients of spectral noise have the advertised multiplier. -/
private theorem coefficient_tensorNoise {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : ι → ℝ) (f : (ι → Bool) → ℝ) (s : ι → Bool) :
    Fourier.coefficient p (BourgainNoise.tensorNoise p ρ f) s =
      (∏ i, if s i then ρ i else 1) * Fourier.coefficient p f s :=
  coefficient_synthesis hp0 hp1 _ s

omit [DecidableEq ι] in
/-- Constant-coordinate multipliers are degree powers. -/
private theorem product_constant_mask (ρ : ℝ) (s : ι → Bool) :
    (∏ i, if s i then ρ else 1) = ρ ^ Fourier.degree s := by
  simp [Fourier.degree, ← Finset.prod_filter]





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















































end NarrowDNF.BourgainSquareFunction

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainSquareFunction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Sharp uniform Bonami adds one more factor of 1/3 per coordinate to the
second moment in the sign variables. -/
theorem solution (p : ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    ProductMeasure.expectation (1/2) (fun y =>
      BourgainNoise.tensorNoise (1/2) (fun _ => Hypercontractivity.sharpRho)
        (fun z => signedNoise p f z x) y ^ 2) =
      ∑ s, (Fourier.coefficient p f s * Fourier.character p s x)^2 /
        (3 : ℝ)^(3 * Fourier.degree s) := by
  rw [Fourier.parseval (by norm_num) (by norm_num)]
  apply Finset.sum_congr rfl
  intro s _
  rw [coefficient_tensorNoise (by norm_num) (by norm_num), product_constant_mask,
    signedNoise_coefficient, mul_pow, mul_pow]
  have hrho : (Hypercontractivity.sharpRho ^ Fourier.degree s)^2 =
      (1/3 : ℝ)^Fourier.degree s := by
    rw [← pow_mul, Nat.mul_comm (Fourier.degree s) 2, pow_mul,
      Hypercontractivity.sharpRho_sq]
  rw [hrho]
  simp only [div_pow, one_pow]
  have hpow : (3 : ℝ)^(3 * Fourier.degree s) =
      (3 : ℝ)^Fourier.degree s * ((3 : ℝ)^Fourier.degree s)^2 := by
    rw [Nat.mul_comm 3, pow_mul]
    ring
  rw [hpow]
  field_simp
