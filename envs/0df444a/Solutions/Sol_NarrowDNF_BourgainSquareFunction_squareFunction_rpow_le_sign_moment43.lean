-- Prove2me | solution 1 for NarrowDNF.BourgainSquareFunction.squareFunction_rpow_le_sign_moment43
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:45:48.939238+00:00
-- url     : https://prove2.me/submissions/c53a1654-96f2-48ae-ab1d-9c32d02d1711

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
import Definitions.Def_NarrowDNF_BourgainDuality
import Definitions.Def_NarrowDNF_BourgainNoise
import Definitions.Def_NarrowDNF_BourgainSquareFunction
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure
import Definitions.Def_NarrowDNF_UniformHypercontractivity
import Theorems.Thm_NarrowDNF_BourgainDuality_dual_contract24
import Theorems.Thm_NarrowDNF_BourgainNoise_tensorNoise_selfAdjoint
import Theorems.Thm_NarrowDNF_BourgainSquareFunction_low_degree_le_damped
import Theorems.Thm_NarrowDNF_BourgainSquareFunction_signedNoise_sharp_second_moment
import Theorems.Thm_NarrowDNF_Hypercontractivity_uniform_spectral_contract24

namespace NarrowDNF.BourgainDuality
end NarrowDNF.BourgainDuality

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
# Finite fourth-moment duality

Weighted Hölder and finite self-adjoint operator duality used by the Bourgain
square-function proof. Every weight is explicit; zero weights are allowed.
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.BourgainDuality

variable {α : Type*} [Fintype α]



private theorem moment43_nonneg (w f : α → ℝ) (hw : ∀ x, 0 ≤ w x) : 0 ≤ moment43 w f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (Real.rpow_nonneg (abs_nonneg _) _)















end NarrowDNF.BourgainDuality

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













































private theorem sharpRho_sq : sharpRho^2 = (1/3 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)





/-- The dual L(4/3)-to-L2 Bonami inequality. Squaring the second moment avoids
outer fractional powers while giving the identical sharp inequality. -/
private theorem uniform_spectral_contract43 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (hρ : 3 * ρ^2 ≤ 1) (f : (ι → Bool) → ℝ) :
    (ProductMeasure.expectation (1/2)
      (fun x => BourgainNoise.tensorNoise (1/2) (fun _ => ρ) f x ^ 2))^2 ≤
        (BourgainDuality.moment43 (ProductMeasure.weight (1/2)) f)^3 := by
  apply BourgainDuality.dual_contract24
    (ProductMeasure.weight (1/2))
    (ProductMeasure.weight_nonneg (by norm_num) (by norm_num))
    (BourgainNoise.tensorNoise (1/2) (fun _ => ρ))
  · intro g h
    simpa only [ProductMeasure.expectation, mul_assoc] using
      BourgainNoise.tensorNoise_selfAdjoint (1/2) (fun _ => ρ) g h
  · exact fun g => uniform_spectral_contract24 ρ hρ g

private theorem uniform_spectral_sharp43 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) :
    (ProductMeasure.expectation (1/2)
      (fun x => BourgainNoise.tensorNoise (1/2) (fun _ => sharpRho) f x ^ 2))^2 ≤
        (BourgainDuality.moment43 (ProductMeasure.weight (1/2)) f)^3 := by
  apply uniform_spectral_contract43
  rw [sharpRho_sq]
  norm_num

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

























private theorem squareFunction_nonneg (p : ℝ) (f : (ι → Bool) → ℝ) (k : ℕ) (x : ι → Bool) :
    0 ≤ squareFunction p f k x := Finset.sum_nonneg fun _ _ => sq_nonneg _







































end NarrowDNF.BourgainSquareFunction

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainSquareFunction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Pointwise sign-space Bonami estimate for the low-degree square function. -/
theorem solution
    (p : ℝ) (f : (ι → Bool) → ℝ) (k : ℕ) (x : ι → Bool) :
    squareFunction p f k x ^ (2/3 : ℝ) ≤ (3 : ℝ)^(2*k) *
      BourgainDuality.moment43 (ProductMeasure.weight (1/2)) (fun y => signedNoise p f y x) := by
  let A := BourgainDuality.moment43 (ProductMeasure.weight (1/2))
    (fun y => signedNoise p f y x)
  let L := ∑ s, (Fourier.coefficient p f s * Fourier.character p s x)^2 /
    (3 : ℝ)^(3 * Fourier.degree s)
  have hA : 0 ≤ A := BourgainDuality.moment43_nonneg _ _
    (ProductMeasure.weight_nonneg (by norm_num) (by norm_num))
  have hd := low_degree_le_damped
    (fun s => Fourier.coefficient p f s * Fourier.character p s x) k 3
  have hs := pow_le_pow_left₀ (squareFunction_nonneg p f k x) hd 2
  have hb := Hypercontractivity.uniform_spectral_sharp43 (fun y => signedNoise p f y x)
  rw [signedNoise_sharp_second_moment] at hb
  have hbound : squareFunction p f k x ^ 2 ≤ (3 : ℝ)^(6*k) * A^3 := by
    rw [mul_pow, ← pow_mul] at hs
    have he : 3*k*2 = 6*k := by omega
    rw [he] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  apply le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (mul_nonneg (by positivity) hA)
  rw [← Real.rpow_mul_natCast (squareFunction_nonneg p f k x), mul_pow,
    ← pow_mul]
  have he : 2*k*3 = 6*k := by omega
  rw [he]
  norm_num only at *
  simpa only [Real.rpow_two] using hbound
