-- Prove2me | solution 1 for NarrowDNF.HatamiCrossTerms.rank_group_residual_le
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:21:53.182658+00:00
-- url     : https://prove2.me/submissions/1233262a-5bed-4467-a654-5d4586fbbeed

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
import Definitions.Def_NarrowDNF_ResidualGram
import Theorems.Thm_NarrowDNF_Activation_sameAtom_of_active_subset_of_agree
import Theorems.Thm_NarrowDNF_ConditionalExpectation_adaptiveCode_eq_iff
import Theorems.Thm_NarrowDNF_HatamiResidual_coordinateMean_eq_of_local
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split
import Theorems.Thm_NarrowDNF_ResidualGram_residual_square_sum

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












/-- A generalized Walsh component averages to zero in each coordinate of its support. -/
private theorem coordinateMean_component_zero (p : ℝ) (f : Cube ι → ℝ) (S : Finset ι)
    (i : ι) (hi : i ∈ S) (x : Cube ι) :
    Fourier.coordinateMean p (Fourier.component p f S) i x = 0 := by
  calc
    _ = Fourier.setCoefficient p f S * Fourier.coordinateMean p (Fourier.setCharacter p S) i x := by
      unfold Fourier.coordinateMean Fourier.component
      ring
    _ = 0 := by
      unfold Fourier.setCharacter
      rw [Fourier.coordinateMean_character]
      simp [Fourier.maskEquivFinset, hi]

/-- A component is orthogonal to every local function missing one of its coordinates. -/
private theorem component_orthogonal_of_not_subset (p : ℝ) (f : Cube ι → ℝ) (S T : Finset ι)
    (hST : ¬ S ⊆ T) (G : Cube ι → ℝ)
    (hG : ∀ x y, (∀ j ∈ T, x j = y j) → G x = G y) :
    expectation p (fun x => Fourier.component p f S x * G x) = 0 := by
  obtain ⟨i,hiS,hiT⟩ := Finset.not_subset.mp hST
  have h := Fourier.coordinateMean_selfAdjoint p (Fourier.component p f S) G i
  simp_rw [coordinateMean_component_zero p f S i hiS,
    coordinateMean_eq_of_local p T G hG i hiT] at h
  simpa using h.symm

/-- The cross component/conditional-component terms vanish for incomparable supports. -/
private theorem component_approx_orthogonal (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (S T : Finset ι) (hST : ¬ S ⊆ T) :
    expectation p (fun x => Fourier.component p f S x * approxComponent p J f T x) = 0 :=
  component_orthogonal_of_not_subset p f S T hST _ (approxComponent_locality p J f T)




section GenericMeanBound
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]







end GenericMeanBound











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




































omit [Fintype ι] [DecidableEq ι] in
/-- Equal-cardinality distinct supports are incomparable. -/
private theorem not_subset_of_card_eq {S R : Finset ι} (hcard : S.card = R.card) (hne : S ≠ R) : ¬ S ⊆ R := by
  intro hsub
  exact hne (Finset.eq_of_subset_of_card_le hsub hcard.ge)














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
/-- The Gram expansion of a fixed rank is controlled by the diagonal plus
its rows in the nonnegative global cross envelope. -/
theorem solution (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (A : Finset (Finset ι)) (r : ℕ) :
    expectation p (fun x => (∑ S ∈ A with S.card = r,
      (Fourier.component p f S x - approxComponent p J f S x))^2) ≤
    ∑ S ∈ A with S.card = r,
      (ConditionalExpectation.squaredError (weight p) (Fourier.component p f S) (approxComponent p J f S) +
      ∑ R ∈ A, if S = R then 0 else
        max 0 (expectation p (fun x => approxComponent p J f S x * approxComponent p J f R x))) := by
  let B := A.filter (fun S => S.card = r)
  have hff : ∀ S ∈ B, ∀ R ∈ B, S ≠ R →
      ResidualGram.inner (weight p) (Fourier.component p f S) (Fourier.component p f R) = 0 := by
    intro S hS R hR hne
    have hcard : S.card = R.card := (Finset.mem_filter.mp hS).2.trans (Finset.mem_filter.mp hR).2.symm
    have h := component_orthogonal_of_not_subset p f S R (not_subset_of_card_eq hcard hne)
      (Fourier.component p f R) (Fourier.component_locality p f R)
    simpa only [ResidualGram.inner, expectation, mul_assoc] using h
  have hfg : ∀ S ∈ B, ∀ R ∈ B, S ≠ R →
      ResidualGram.inner (weight p) (Fourier.component p f S) (approxComponent p J f R) = 0 := by
    intro S hS R hR hne
    have hcard : S.card = R.card := (Finset.mem_filter.mp hS).2.trans (Finset.mem_filter.mp hR).2.symm
    have h := component_approx_orthogonal p J f S R (not_subset_of_card_eq hcard hne)
    simpa only [ResidualGram.inner, expectation, mul_assoc] using h
  change (∑ x, weight p x * (∑ S ∈ B, (Fourier.component p f S x - approxComponent p J f S x))^2) ≤ _
  rw [ResidualGram.residual_square_sum (weight p) B (Fourier.component p f) (approxComponent p J f) hff hfg]
  rw [Finset.sum_add_distrib]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro S hS
  calc
    _ ≤ ∑ R ∈ B.erase S, if S = R then 0 else
        max 0 (expectation p (fun x => approxComponent p J f S x * approxComponent p J f R x)) := by
      apply Finset.sum_le_sum
      intro R hR
      have hne : S ≠ R := Ne.symm (Finset.mem_erase.mp hR).1
      rw [if_neg hne]
      simpa only [ResidualGram.inner, expectation, mul_assoc] using
        (le_max_right 0 (expectation p (fun x => approxComponent p J f S x * approxComponent p J f R x)))
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg ((Finset.erase_subset _ _).trans (Finset.filter_subset _ _))
      intro R _ _
      split_ifs <;> positivity
