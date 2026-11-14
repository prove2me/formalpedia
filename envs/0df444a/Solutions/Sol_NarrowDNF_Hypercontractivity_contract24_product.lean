-- Prove2me | solution 1 for NarrowDNF.Hypercontractivity.contract24_product
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:32:31.017666+00:00
-- url     : https://prove2.me/submissions/087f4a58-a1a3-481c-bf4c-ef7f8ab473f2

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
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure
import Definitions.Def_NarrowDNF_UniformHypercontractivity
import Theorems.Thm_NarrowDNF_Hypercontractivity_contract24_tensor
import Theorems.Thm_NarrowDNF_Hypercontractivity_productOperator_option

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













/-- Transport a finite moment inequality across an exact relabeling. -/
private theorem contract24_transfer (e : α ≃ β) {w : α → ℝ} {v : β → ℝ}
    {T : (α → ℝ) → α → ℝ} {U : (β → ℝ) → β → ℝ}
    (hw : ∀ a, w a = v (e a))
    (hTU : ∀ f a, T (fun a => f (e a)) a = U f (e a))
    (hT : Contract24 w T) : Contract24 v U := by
  intro f
  have h4 := Fintype.sum_equiv e (fun a => w a * (T (fun a => f (e a)) a)^4)
    (fun b => v b * (U f b)^4) (fun a => by rw [hw, hTU])
  have h2 := Fintype.sum_equiv e (fun a => w a * (f (e a))^2)
    (fun b => v b * (f b)^2) (fun a => by rw [hw])
  rw [← h4, ← h2]
  exact hT _









private theorem productWeight_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : Bool → ℝ) (x : ι → Bool) :
    productWeight w x = productWeight w (cubeEquiv e x) := by
  unfold productWeight
  simpa [cubeEquiv] using e.prod_comp (fun j => w (x (e.symm j)))

private theorem productOperator_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : Bool → ℝ) (K : Bool → Bool → ℝ)
    (f : (κ → Bool) → ℝ) (x : ι → Bool) :
    productOperator w K (fun y => f (cubeEquiv e y)) x =
      productOperator w K f (cubeEquiv e x) := by
  unfold productOperator
  apply Fintype.sum_equiv (cubeEquiv e)
  intro y
  congr 1
  simpa [cubeEquiv] using
    e.prod_comp (fun j => w (y (e.symm j)) * K (x (e.symm j)) (y (e.symm j)))

private theorem productWeight_option {ι : Type*} [Fintype ι] (w : Bool → ℝ)
    (x : Option ι → Bool) :
    productWeight w x = w (x none) * productWeight w (fun i => x (some i)) := by
  exact Fintype.prod_option (fun i => w (x i))



























end NarrowDNF.Hypercontractivity

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.Hypercontractivity
attribute [local instance] Classical.decEq
variable {α β : Type*} [Fintype α] [Fintype β]
/-- Dimension-free tensorization: every scalar two-point L2-to-L4 kernel
inequality extends to arbitrary finite coordinate products. -/
theorem solution (w : Bool → ℝ) (hw : ∀ b, 0 ≤ w b)
    (K : Bool → Bool → ℝ) (hK : Contract24 w (kernelOperator w K))
    (ι : Type*) [Fintype ι] :
    Contract24 (productWeight (ι := ι) w) (productOperator w K) := by
  classical
  refine Fintype.induction_empty_option
    (P := fun ι _ => Contract24 (productWeight (ι := ι) w) (productOperator w K))
    ?_ ?_ ?_ ι
  · intro α β _ e hα
    letI : Fintype α := Fintype.ofEquiv β e.symm
    exact contract24_transfer (cubeEquiv e) (productWeight_equiv e w)
      (productOperator_equiv e w K) hα
  · intro f
    have hconstant (x : PEmpty → Bool) : productOperator w K f x = f x := by
      simp [productOperator]
      exact congrArg f (Subsingleton.elim _ _)
    simp [productWeight, hconstant, ← pow_mul]
  · intro α _ hα
    have hwα : ∀ x : α → Bool, 0 ≤ productWeight w x := by
      intro x
      exact Finset.prod_nonneg fun i _ => hw (x i)
    have h := contract24_transfer
      ((Equiv.piOptionEquivProd (α := α) (β := fun _ => Bool)).symm)
      (w := fun z => w z.1 * productWeight w z.2)
      (v := productWeight (ι := Option α) w)
      (T := fun f z => kernelOperator w K
        (fun b => productOperator w K (fun y => f (b,y)) z.2) z.1)
      (U := productOperator (ι := Option α) w K)
      (by intro z; simp [productWeight_option, Equiv.piOptionEquivProd])
      (by intro f z; rw [productOperator_option]; rfl)
      (contract24_tensor hw hwα hK hα)
    convert h using 1
