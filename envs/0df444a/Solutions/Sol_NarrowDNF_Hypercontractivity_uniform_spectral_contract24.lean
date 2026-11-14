-- Prove2me | solution 1 for NarrowDNF.Hypercontractivity.uniform_spectral_contract24
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:34:50.945037+00:00
-- url     : https://prove2.me/submissions/6e77fbed-9f0c-4607-90ba-9b709830a979

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_BourgainNoise
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure
import Definitions.Def_NarrowDNF_UniformHypercontractivity
import Theorems.Thm_NarrowDNF_BourgainNoise_tensorNoise_eq_productKernel
import Theorems.Thm_NarrowDNF_Hypercontractivity_contract24_product

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









private theorem bitWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bitWeight p b := by
  cases b <;> simp only [bitWeight_false, bitWeight_true]
  · exact sub_nonneg.mpr hp1
  · exact hp0







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
# Finite L2-to-L4 hypercontractivity and its uniform-cube specialization

The moment formulation avoids fractional powers during tensorization.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.Hypercontractivity

attribute [local instance] Classical.decEq

variable {α β : Type*} [Fintype α] [Fintype β]











/-- The sharp one-bit L2-to-L4 estimate at every |ρ|≤1/sqrt(3), stated
polynomially as 3ρ²≤1. -/
private theorem uniform_bit_contract24 (ρ : ℝ) (hρ : 3 * ρ^2 ≤ 1) :
    Contract24 (fun _ : Bool => (1/2 : ℝ)) (uniformBitNoise ρ) := by
  intro f
  have hρ4 : ρ^4 ≤ 1 := by
    nlinarith [sq_nonneg (ρ^2 - 1), sq_nonneg ρ]
  have hcross : (0:ℝ) ≤ ((f false + f true)/2)^2 * ((f true-f false)/2)^2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h1 := mul_le_mul_of_nonneg_right hρ hcross
  have h2 := mul_le_mul_of_nonneg_right hρ4 (by positivity :
    (0:ℝ) ≤ ((f true-f false)/2)^4)
  simp only [Fintype.sum_bool, uniformBitNoise, Bool.false_eq_true, if_false, if_true]
  nlinarith [sq_nonneg (((f true-f false)/2)^2)]























private theorem standardKernelOperator_half (ρ : ℝ) :
    kernelOperator (ProductMeasure.bitWeight (1/2)) (standardKernel (1/2) ρ) =
      uniformBitNoise ρ := by
  funext f b
  cases b <;>
    norm_num [kernelOperator, Fintype.sum_bool, standardKernel, Fourier.standardBit,
      ProductMeasure.bitWeight, uniformBitNoise] <;> ring

private theorem uniform_kernel_contract24 (ρ : ℝ) (hρ : 3 * ρ^2 ≤ 1) :
    Contract24 (ProductMeasure.bitWeight (1/2))
      (kernelOperator (ProductMeasure.bitWeight (1/2)) (standardKernel (1/2) ρ)) := by
  rw [standardKernelOperator_half]
  have hw : ProductMeasure.bitWeight (1/2) = fun _ : Bool => (1/2 : ℝ) := by
    funext b
    cases b <;> norm_num [ProductMeasure.bitWeight]
  rw [hw]
  exact uniform_bit_contract24 ρ hρ

private theorem productOperator_standardKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p ρ : ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    productOperator (ProductMeasure.bitWeight p) (standardKernel p ρ) f x =
      BourgainNoise.tensorNoise p (fun _ => ρ) f x := by
  convert (BourgainNoise.tensorNoise_eq_productKernel p (fun _ => ρ) f x).symm using 1
  simp only [productOperator, standardKernel]
  congr 1
  ext y
  simp















end NarrowDNF.Hypercontractivity

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.Hypercontractivity
attribute [local instance] Classical.decEq
variable {α β : Type*} [Fintype α] [Fintype β]
/-- Arbitrary-dimensional sharp uniform-cube L2-to-L4 hypercontractivity, in
fourth-moment form, for the actual Fourier-defined noise operator. -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : 3 * ρ^2 ≤ 1) (f : (ι → Bool) → ℝ) :
    ProductMeasure.expectation (1/2)
      (fun x => BourgainNoise.tensorNoise (1/2) (fun _ => ρ) f x ^ 4) ≤
        (ProductMeasure.expectation (1/2) (fun x => f x ^ 2))^2 := by
  have h := contract24_product (ProductMeasure.bitWeight (1/2))
    (ProductMeasure.bitWeight_nonneg (by norm_num) (by norm_num))
    (standardKernel (1/2) ρ) (uniform_kernel_contract24 ρ hρ) ι f
  simp only [productOperator_standardKernel, productWeight] at h
  unfold ProductMeasure.expectation ProductMeasure.weight
  convert h using 1
  · congr 1
    ext x
    simp
  · congr 2
    ext x
    simp
