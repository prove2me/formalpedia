-- Prove2me | solution 1 for NarrowDNF.HatamiCrossTerms.pair_cross_le_kernel
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:35:21.310775+00:00
-- url     : https://prove2.me/submissions/6a0a2a1f-56c8-4097-842b-9e02c06edef7

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
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_HatamiCrossTerms
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Activation_sameAtom_of_active_subset_of_agree
import Theorems.Thm_NarrowDNF_ConditionalExpectation_adaptiveCode_eq_iff
import Theorems.Thm_NarrowDNF_ConditionalExpectation_local_conditional_independence
import Theorems.Thm_NarrowDNF_HatamiResidual_approxComponent_abs_mean_le
import Theorems.Thm_NarrowDNF_HatamiResidual_approxComponent_conditional_zero_of_fires

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

namespace NarrowDNF.HatamiCrossTerms
end NarrowDNF.HatamiCrossTerms

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

















omit [DecidableEq ι] in
/-- Product weights factor over a coordinate predicate and its complement. -/
private theorem weight_partition (p : ℝ) (P : ι → Prop) [DecidablePred P] (x : ι → Bool) :
    weight p x = weight p (fun i : {i // P i} => x i) *
      weight p (fun i : {i // ¬ P i} => x i) := by
  exact (Fintype.prod_subtype_mul_prod_subtype P (fun i => bitWeight p (x i))).symm





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























section Adaptive
variable {ι : Type*} [Fintype ι] [DecidableEq ι]













end Adaptive

section CoordinatePartition
variable {ι : Type*} [Fintype ι] [DecidableEq ι]





/-- Exact probability of a coordinate restriction. -/
private theorem mass_restriction (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (z : {i // P i} → Bool) :
    mass (fun x : Cube ι => fun i : {i // P i} => x i) (ProductMeasure.weight p) z =
      ProductMeasure.weight p z := by
  unfold mass
  rw [Fintype.sum_equiv (restrictionFiberEquiv P z)
    (fun x => ProductMeasure.weight p x.val)
    (fun y => ProductMeasure.weight p z * ProductMeasure.weight p y)
    (fun x => by
      change ProductMeasure.weight p x.val = ProductMeasure.weight p z *
        ProductMeasure.weight p (fun i : {i // ¬ P i} => x.val i)
      rw [ProductMeasure.weight_partition p P x.val, x.property])]
  rw [← Finset.mul_sum, ProductMeasure.sum_weight, mul_one]













end CoordinatePartition
section Localization



omit [Fintype β] in
/-- Fiber first moments written as ordinary finite sums with indicators. -/
private theorem moment_eq_indicator_sum (φ : α → β) (w F : α → ℝ) (b : β) :
    moment φ w F b = ∑ a, if φ a = b then w a * F a else 0 := by
  classical
  unfold moment
  simpa only [Finset.sum_filter] using
    (Finset.sum_subtype (Finset.univ.filter (fun a => φ a = b)) (by simp)
      (fun a => w a * F a)).symm

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
private theorem restrict_active_subset (J : Activation ι) (S : Finset ι) (x : Cube ι) :
    (restrict J S).active x ⊆ (S : Set ι) := by
  rintro i ⟨T,hi,hT⟩
  exact hT.1 hi





omit [Fintype ι] [DecidableEq ι] in
/-- Agreement on `S` fixes the entire `J_S` adaptive atom. -/
private theorem restrict_sameAtom_of_agree (J : Activation ι) (S : Finset ι) {x y : Cube ι}
    (hxy : ∀ i ∈ S, x i = y i) : (restrict J S).SameAtom x y :=
  Activation.sameAtom_of_active_subset_of_agree
    (restrict_active_subset J S x) (restrict_active_subset J S y) hxy











private theorem approxComponent_locality (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (S : Finset ι) (x y : Cube ι) (hxy : ∀ i ∈ S, x i = y i) :
    approxComponent p J f S x = approxComponent p J f S y := by
  apply ConditionalExpectation.conditional_eq_of_atom_eq
  exact (ConditionalExpectation.adaptiveCode_eq_iff _ x y).mpr
    (restrict_sameAtom_of_agree J S hxy)







section Generic
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]





end Generic


















section GenericBound
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]



end GenericBound





















section GenericMeanBound
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

omit [Fintype β] in
/-- The absolute numerator of an atom average is bounded by the global L1 mass. -/
private theorem abs_moment_le_abs_sum (φ : α → β) (w F : α → ℝ) (hw : ∀ a, 0 ≤ w a) (b : β) :
    |ConditionalExpectation.moment φ w F b| ≤ ∑ a, w a * |F a| := by
  rw [ConditionalExpectation.moment_eq_indicator_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : φ a = b
  · simp [ha, abs_mul, abs_of_nonneg (hw a)]
  · simpa [ha] using mul_nonneg (hw a) (abs_nonneg (F a))

omit [Fintype β] in
/-- A local atom's positive mass converts a global L1 bound into a conditional bound. -/
private theorem abs_mean_le_div (φ : α → β) (w F : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (b : β) (hmass : 0 < ConditionalExpectation.mass φ w b) :
    |ConditionalExpectation.mean φ w F b| ≤
      (∑ a, w a * |F a|) / ConditionalExpectation.mass φ w b := by
  unfold ConditionalExpectation.mean
  rw [abs_div, abs_of_pos hmass]
  exact div_le_div_of_nonneg_right (abs_moment_le_abs_sum φ w F hw b) hmass.le



end GenericMeanBound

/-- The repaired bound (15), retaining the necessary factor `2^(3|S|)`. -/
private theorem approxComponent_conditional_abs_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → Bool) (S T : Finset ι) (z : T → Bool) :
    |ConditionalExpectation.mean (fun x : Cube ι => fun i : T => x i) (weight p)
      (approxComponent p J (fun y => Influence.boolValue (f y)) S) z| ≤
      ((2:ℝ)^(3*S.card) * p^S.card) / weight p z := by
  have hmass : ConditionalExpectation.mass (fun x : Cube ι => fun i : T => x i) (weight p) z =
      weight p z := by
    have hm := ConditionalExpectation.mass_restriction (ι := ι) p (fun i => i ∈ T) z
    rw [Subsingleton.elim (Subtype.fintype (fun i => i ∈ T)) (Finset.Subtype.fintype T)] at hm
    exact hm
  apply (abs_mean_le_div _ _ _ (weight_nonneg hp0.le hp1.le) z
    (by rw [hmass]; exact weight_pos hp0 hp1 z)).trans
  rw [hmass]
  apply div_le_div_of_nonneg_right _ (weight_pos hp0 hp1 z).le
  exact approxComponent_abs_mean_le hp0 hp1 J f S









end NarrowDNF.HatamiResidual




end

end

section


/-!
# Hatami's corrected cross-term estimate

Finite cross-term estimates for the exact restricted-activation conditional
components. The repaired coefficient factor is retained explicitly.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.HatamiCrossTerms

open ProductMeasure HatamiResidual HatamiActivation
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]





/-- Distinct supports have a proper intersection in at least one component;
a fired intersection therefore kills their product of conditional means. -/
private theorem conditional_product_zero_of_fires {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → ℝ) (S R : Finset ι) (hSR : S ≠ R)
    (x : Cube ι) (hx : J.fires (S ∩ R) x) :
    ConditionalExpectation.mean (restriction (S ∩ R)) (weight p) (approxComponent p J f S)
      (restriction (S ∩ R) x) *
    ConditionalExpectation.mean (restriction (S ∩ R)) (weight p) (approxComponent p J f R)
      (restriction (S ∩ R) x) = 0 := by
  by_cases hS : S ⊆ S ∩ R
  · have hR : ¬ R ⊆ S ∩ R := by
      intro hR
      apply hSR
      exact Finset.Subset.antisymm (hS.trans Finset.inter_subset_right)
        (hR.trans Finset.inter_subset_left)
    rw [approxComponent_conditional_zero_of_fires hp0 hp1 J f R (S ∩ R)
      Finset.inter_subset_right hR x hx, mul_zero]
  · rw [approxComponent_conditional_zero_of_fires hp0 hp1 J f S (S ∩ R)
      Finset.inter_subset_left hS x hx, zero_mul]













































end NarrowDNF.HatamiCrossTerms





end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiCrossTerms
open ProductMeasure HatamiResidual HatamiActivation
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Exact pairwise cross bound before bounding the degrees by a common cutoff. -/
theorem solution {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → Bool) (S R : Finset ι) (hSR : S ≠ R) :
    expectation p (fun x => approxComponent p J (fun y => Influence.boolValue (f y)) S x *
      approxComponent p J (fun y => Influence.boolValue (f y)) R x) ≤
      ((2:ℝ)^(3*S.card) * p^S.card) * ((2:ℝ)^(3*R.card) * p^R.card) *
        inactiveKernel p J (S ∩ R) := by
  let F := fun x => Influence.boolValue (f x)
  rw [ConditionalExpectation.local_conditional_independence hp0 hp1 S R _ _
    (approxComponent_locality p J F S) (approxComponent_locality p J F R)]
  unfold inactiveKernel
  rw [← expectation_const_mul]
  apply expectation_mono hp0.le hp1.le
  intro x
  change ConditionalExpectation.mean (restriction (S ∩ R)) (weight p) (approxComponent p J F S)
      (restriction (S ∩ R) x) *
    ConditionalExpectation.mean (restriction (S ∩ R)) (weight p) (approxComponent p J F R)
      (restriction (S ∩ R) x) ≤ _
  by_cases hx : J.fires (S ∩ R) x
  · rw [conditional_product_zero_of_fires hp0 hp1 J F S R hSR x hx]
    simp [hx]
  · simp only [if_neg hx]
    have ha := approxComponent_conditional_abs_le hp0 hp1 J f S (S ∩ R) (restriction (S ∩ R) x)
    have hb := approxComponent_conditional_abs_le hp0 hp1 J f R (S ∩ R) (restriction (S ∩ R) x)
    have hmass : 0 < weight p (restriction (S ∩ R) x) := weight_pos hp0 hp1 _
    calc
      _ ≤ |ConditionalExpectation.mean (restriction (S ∩ R)) (weight p) (approxComponent p J F S)
          (restriction (S ∩ R) x)| *
        |ConditionalExpectation.mean (restriction (S ∩ R)) (weight p) (approxComponent p J F R)
          (restriction (S ∩ R) x)| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ (((2:ℝ)^(3*S.card) * p^S.card) / weight p (restriction (S ∩ R) x)) *
          (((2:ℝ)^(3*R.card) * p^R.card) / weight p (restriction (S ∩ R) x)) :=
        mul_le_mul ha hb (abs_nonneg _) (div_nonneg (by positivity) hmass.le)
      _ = _ := by
        change _ = _ * (1 / weight p (restriction (S ∩ R) x)^2)
        field_simp
