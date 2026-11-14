-- Prove2me | solution 1 for NarrowDNF.HatamiActivation.sum_componentTailMass_le
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:32:53.894465+00:00
-- url     : https://prove2.me/submissions/2f39c7f0-5219-45d0-aa58-a68bf559d389

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
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Fourier_inner_parseval
import Theorems.Thm_NarrowDNF_HatamiActivation_probability_abs_ge_le_sq

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

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

/-- Total squared coefficient mass of a Boolean function is at most one. -/
private theorem boolean_energy_le_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    (∑ S : Finset ι, setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2) ≤ 1 := by
  rw [← parseval_finset hp0 hp1]
  calc
    _ ≤ ProductMeasure.expectation (ι := ι) p (fun _ => 1) := by
      apply ProductMeasure.expectation_mono hp0.le hp1.le
      intro x
      cases f x <;> norm_num [Influence.boolValue]
    _ = 1 := ProductMeasure.expectation_one p



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



































































private theorem componentTailMass_le {p η : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hη : 0 < η) (f : Cube ι → ℝ) (S : Finset ι) :
    componentTailMass p f η S ≤ Fourier.setCoefficient p f S ^ 2 / η^2 := by
  have h := probability_abs_ge_le_sq hp0.le hp1.le hη (Fourier.component p f S)
  rw [Fourier.component_sq_mean hp0 hp1] at h
  exact h





















end NarrowDNF.HatamiActivation

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiActivation
open ProductMeasure
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Parseval and Markov give the retained tail-mass bound, without an
assumption about the number or distribution of retained subsets. -/
theorem solution {p η : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hη : 0 < η) (f : Cube ι → Bool) (retained : Finset (Finset ι)) :
    (∑ S ∈ retained, componentTailMass p (fun x => Influence.boolValue (f x)) η S) ≤
      1 / η^2 := by
  calc
    _ ≤ ∑ S ∈ retained, Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2 / η^2 := by
      apply Finset.sum_le_sum
      intro S _
      exact componentTailMass_le hp0 hp1 hη _ S
    _ = (∑ S ∈ retained, Fourier.setCoefficient p (fun x => Influence.boolValue (f x)) S ^ 2) / η^2 :=
      (Finset.sum_div _ _ _).symm
    _ ≤ 1 / η^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg η)
      apply le_trans _ (Fourier.boolean_energy_le_one hp0 hp1 f)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ retained)
      intro S _ _
      exact sq_nonneg _
