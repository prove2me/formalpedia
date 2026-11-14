-- Prove2me | solution 1 for NarrowDNF.HatamiResidual.approxComponent_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:21:45.31121+00:00
-- url     : https://prove2.me/submissions/02f6d3bc-0411-4316-8948-80b4f1b8051e

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
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Activation_sameAtom_of_active_subset_of_agree
import Theorems.Thm_NarrowDNF_ConditionalExpectation_adaptiveCode_eq_iff
import Theorems.Thm_NarrowDNF_HatamiResidual_conditional_abs_le_card_mul
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_restrict

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

/-- A local observable may be integrated over only the coordinates it reads. -/
private theorem expectation_local (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (F : (ι → Bool) → ℝ)
    (hF : ∀ x y, (∀ i, P i → x i = y i) → F x = F y) :
    expectation p F = expectation p (fun z => F (extendFalse P z)) := by
  calc
    expectation p F =
        expectation p (fun x : ι → Bool => F (extendFalse P (fun i => x i))) := by
      apply congrArg (expectation p)
      funext x
      apply hF
      intro i hi
      simp [extendFalse, hi]
    _ = expectation p (fun z => F (extendFalse P z)) :=
      expectation_restrict p P (fun z => F (extendFalse P z))

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



















































section Adaptive
variable {ι : Type*} [Fintype ι] [DecidableEq ι]













end Adaptive

section CoordinatePartition
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



















end CoordinatePartition
section Localization

omit [Fintype β] in
/-- Fiber masses written as ordinary finite sums with indicators. -/
private theorem mass_eq_indicator_sum (φ : α → β) (w : α → ℝ) (b : β) :
    mass φ w b = ∑ a, if φ a = b then w a else 0 := by
  classical
  unfold mass
  simpa only [Finset.sum_filter] using
    (Finset.sum_subtype (Finset.univ.filter (fun a => φ a = b)) (by simp) w).symm

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

omit [Fintype β] in
private theorem mass_eq_expectation (p : ℝ) (φ : Cube ι → β) (b : β) :
    mass φ (ProductMeasure.weight p) b =
      ProductMeasure.expectation p (fun x => if φ x = b then 1 else 0) := by
  simp [mass_eq_indicator_sum, ProductMeasure.expectation, mul_ite]

omit [Fintype β] in
private theorem moment_eq_expectation (p : ℝ) (φ : Cube ι → β) (F : Cube ι → ℝ) (b : β) :
    moment φ (ProductMeasure.weight p) F b =
      ProductMeasure.expectation p (fun x => if φ x = b then F x else 0) := by
  simp [moment_eq_indicator_sum, ProductMeasure.expectation, mul_ite]

omit [Fintype β] in
/-- A local partition has the same atom masses in the global and restricted cubes. -/
private theorem mass_localization (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (φ : Cube ι → β) (hφ : ∀ x y, (∀ i, P i → x i = y i) → φ x = φ y) (b : β) :
    mass φ (ProductMeasure.weight p) b =
      mass (fun z => φ (ProductMeasure.extendFalse P z)) (ProductMeasure.weight p) b := by
  rw [mass_eq_expectation, mass_eq_expectation]
  apply ProductMeasure.expectation_local
  intro x y hxy
  rw [hφ x y hxy]

omit [Fintype β] in
/-- A local observable and local partition have the same conditional moment
when computed only on the coordinates they read. -/
private theorem moment_localization (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (φ : Cube ι → β) (hφ : ∀ x y, (∀ i, P i → x i = y i) → φ x = φ y)
    (F : Cube ι → ℝ) (hF : ∀ x y, (∀ i, P i → x i = y i) → F x = F y) (b : β) :
    moment φ (ProductMeasure.weight p) F b =
      moment (fun z => φ (ProductMeasure.extendFalse P z)) (ProductMeasure.weight p)
        (fun z => F (ProductMeasure.extendFalse P z)) b := by
  rw [moment_eq_expectation, moment_eq_expectation]
  apply ProductMeasure.expectation_local
  intro x y hxy
  rw [hφ x y hxy, hF x y hxy]

omit [Fintype β] in
/-- Exact localization of conditional expectation for a local observable and
local partition. This is the restricted-atom interface used by Hatami's proof. -/
private theorem conditional_localization (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (φ : Cube ι → β) (hφ : ∀ x y, (∀ i, P i → x i = y i) → φ x = φ y)
    (F : Cube ι → ℝ) (hF : ∀ x y, (∀ i, P i → x i = y i) → F x = F y)
    (x : Cube ι) :
    conditional φ (ProductMeasure.weight p) F x =
      conditional (fun z => φ (ProductMeasure.extendFalse P z)) (ProductMeasure.weight p)
        (fun z => F (ProductMeasure.extendFalse P z)) (fun i => x i) := by
  unfold conditional mean
  rw [moment_localization p P φ hφ F hF, mass_localization p P φ hφ]
  have hx : φ x = φ (ProductMeasure.extendFalse P (fun i => x i)) := by
    apply hφ
    intro i hi
    simp [ProductMeasure.extendFalse, hi]
  rw [hx]

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

/-- The subset-indexed character is the usual product of centered normalized bits. -/
private theorem setCharacter_eq_prod (p : ℝ) (S : Finset ι) (x : ι → Bool) :
    setCharacter p S x = ∏ i ∈ S, standardBit p (x i) := by
  simp [setCharacter, character, maskEquivFinset, bitBasis]










/-- A subset-indexed basis function depends only on its indexing coordinates. -/
private theorem setCharacter_locality (p : ℝ) (S : Finset ι) (x y : ι → Bool)
    (hxy : ∀ i ∈ S, x i = y i) : setCharacter p S x = setCharacter p S y := by
  rw [setCharacter_eq_prod, setCharacter_eq_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hxy i hi]

/-- Each generalized Walsh component is local to its indexing subset. -/
private theorem component_locality (p : ℝ) (f : (ι → Bool) → ℝ) (S : Finset ι)
    (x y : ι → Bool) (hxy : ∀ i ∈ S, x i = y i) :
    component p f S x = component p f S y := by
  unfold component
  rw [setCharacter_locality p S x y hxy]











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



















section Generic
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]





end Generic














/-- The Bernoulli mass times the absolute normalized bit is independent of that bit. -/
private theorem bitWeight_abs_standardBit {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (b : Bool) :
    bitWeight p b * |Fourier.standardBit p b| = Real.sqrt (p * (1-p)) := by
  have hspos := Real.sqrt_pos.mpr (mul_pos hp0 (sub_pos.mpr hp1))
  have hs := ne_of_gt hspos
  have hs2 := Real.sq_sqrt (le_of_lt (mul_pos hp0 (sub_pos.mpr hp1)))
  cases b <;>
    simp only [bitWeight, Fourier.standardBit, Bool.false_eq_true, ↓reduceIte,
      abs_div, abs_neg, abs_of_pos hp0, abs_of_pos (sub_pos.mpr hp1), abs_of_pos hspos]
  all_goals field_simp
  all_goals nlinarith

/-- The local mass times the absolute component is constant throughout its local cube. -/
private theorem component_mass_abs {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube ι → ℝ) (S : Finset ι) (x : Cube ι) :
    HatamiActivation.localMass p S x * |Fourier.component p f S x| =
      Real.sqrt (p * (1-p)) ^ S.card * |Fourier.setCoefficient p f S| := by
  unfold HatamiActivation.localMass weight Fourier.component
  rw [abs_mul, Fourier.setCharacter_eq_prod, Finset.abs_prod]
  dsimp only
  rw [Finset.prod_coe_sort S (fun i => bitWeight p (x i))]
  calc
    _ = (∏ i ∈ S, bitWeight p (x i) * |Fourier.standardBit p (x i)|) *
        |Fourier.setCoefficient p f S| := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by simp_rw [bitWeight_abs_standardBit hp0 hp1]; simp

section GenericBound
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]



end GenericBound





















section GenericMeanBound
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]







end GenericMeanBound











end NarrowDNF.HatamiResidual




end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiResidual
open ProductMeasure
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Hatami's pointwise `2^|S|` conditional-component bound, proved for the actual
restricted adaptive atoms and the local Bernoulli marginal. -/
theorem solution {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → ℝ) (S : Finset ι) (x : Cube ι) :
    |approxComponent p J f S x| ≤ (2 : ℝ)^S.card * |Fourier.component p f S x| := by
  have hφ : ∀ x y : Cube ι, (∀ i, i ∈ S → x i = y i) →
      ConditionalExpectation.adaptiveCode (restrict J S) x =
      ConditionalExpectation.adaptiveCode (restrict J S) y := by
    intro x y hxy
    exact (ConditionalExpectation.adaptiveCode_eq_iff _ x y).mpr
      (restrict_sameAtom_of_agree J S hxy)
  unfold approxComponent adaptiveConditional
  rw [ConditionalExpectation.conditional_localization p (fun i => i ∈ S) _ hφ _
    (Fourier.component_locality p f S) x]
  have h := conditional_abs_le_card_mul
    (fun z : S → Bool => ConditionalExpectation.adaptiveCode (restrict J S)
      (extendFalse (fun i => i ∈ S) z))
    (weight p) (fun z : S → Bool => Fourier.component p f S (extendFalse (fun i => i ∈ S) z))
    (weight_pos hp0 hp1)
    (Real.sqrt (p * (1-p)) ^ S.card * |Fourier.setCoefficient p f S|)
    (fun z => by
      have hm : HatamiActivation.localMass p S (extendFalse (fun i => i ∈ S) z) = weight p z := by
        unfold HatamiActivation.localMass
        congr 1
        funext i
        simp [extendFalse, i.property]
      simpa only [hm] using component_mass_abs hp0 hp1 f S (extendFalse (fun i => i ∈ S) z))
    (fun i => x i)
  have hlocal : Fourier.component p f S (extendFalse (fun i => i ∈ S) (fun i => x i)) =
      Fourier.component p f S x := by
    apply Fourier.component_locality
    intro i hi
    simp [extendFalse, hi]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Nat.cast_pow,
    Nat.cast_ofNat, hlocal] at h
  rw [Subsingleton.elim (Finset.Subtype.fintype S) (Subtype.fintype (fun i => i ∈ S))] at h
  exact h
