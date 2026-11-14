-- Prove2me | solution 1 for NarrowDNF.HatamiResidual.sum_diagonal_le_small_mass
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:24:59.832207+00:00
-- url     : https://prove2.me/submissions/b4d6d7f0-7575-4476-aba3-50f7fd8302ba

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
import Theorems.Thm_NarrowDNF_ConditionalExpectation_adaptiveCode_eq_iff
import Theorems.Thm_NarrowDNF_ConditionalExpectation_squaredError_decomposition
import Theorems.Thm_NarrowDNF_HatamiActivation_localMass_le_componentTailMass
import Theorems.Thm_NarrowDNF_HatamiResidual_fires_congr_atom

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


/-! Local activation families and their adaptive atoms. The global-input encoding
of a local activation carries an explicit locality proof, so it does not grant
an activation access to coordinates outside its indexing set. -/
namespace NarrowDNF





namespace Activation
variable {ι : Type*} [DecidableEq ι]











omit [DecidableEq ι] in
private theorem mem_active_of_fires {J : Activation ι} {S : Finset ι} {x : Cube ι}
    (h : J.fires S x) {i : ι} (hi : i ∈ S) : i ∈ J.active x := ⟨S, hi, h⟩









end Activation
end NarrowDNF


end

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







private theorem expectation_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F : (ι → Bool) → ℝ} (hF : ∀ x, 0 ≤ F x) : 0 ≤ expectation p F :=
  Finset.sum_nonneg fun x _ => mul_nonneg (weight_nonneg hp0 hp1 x) (hF x)

private theorem expectation_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F G : (ι → Bool) → ℝ} (hFG : ∀ x, F x ≤ G x) :
    expectation p F ≤ expectation p G :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hFG x) (weight_nonneg hp0 hp1 x)

private theorem probability_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : (ι → Bool) → Prop) [DecidablePred P] : 0 ≤ probability p P := by
  apply expectation_nonneg hp0 hp1
  intro x
  split_ifs <;> norm_num





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



































/-- Conditional expectation is a least-squares projection onto atom readouts. -/
private theorem squaredError_minimal (φ : α → β) (w F : α → ℝ)
    (hw : ∀ a, 0 < w a) (G : β → ℝ) :
    squaredError w F (conditional φ w F) ≤ squaredError w F (fun a => G (φ a)) := by
  rw [squaredError_decomposition φ w F hw G]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun a _ => mul_nonneg (hw a).le (sq_nonneg _))











omit [Fintype β] in
/-- A real function constant on partition fibers has a global readout map. -/
private theorem exists_readout (φ : α → β) (G : α → ℝ)
    (hG : ∀ x y, φ x = φ y → G x = G y) :
    ∃ g : β → ℝ, ∀ x, G x = g (φ x) := by
  classical
  let g : β → ℝ := fun b => if h : ∃ a, φ a = b then G h.choose else 0
  refine ⟨g, ?_⟩
  intro x
  have h : ∃ a, φ a = φ x := ⟨x,rfl⟩
  simp only [g, dif_pos h]
  exact (hG h.choose x h.choose_spec).symm

/-- Least-squares optimality for any fiber-measurable function, without requiring
its readout map as an additional argument. -/
private theorem squaredError_minimal_of_measurable (φ : α → β) (w F G : α → ℝ)
    (hw : ∀ a, 0 < w a) (hG : ∀ x y, φ x = φ y → G x = G y) :
    squaredError w F (conditional φ w F) ≤ squaredError w F G := by
  obtain ⟨g,hg⟩ := exists_readout φ G hG
  have heq : G = fun a => g (φ a) := funext hg
  rw [heq]
  exact squaredError_minimal φ w F hw g

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























private theorem significantSets_card (p : ℝ) (f : Cube ι → ℝ) (k η : ℝ)
    (S : Finset ι) (hS : S ∈ significantSets p f k η) : (S.card : ℝ) ≤ k :=
  (Finset.mem_filter.mp hS).2.1

private theorem componentTailMass_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Cube ι → ℝ) (η : ℝ) (S : Finset ι) : 0 ≤ componentTailMass p f η S :=
  probability_nonneg hp0 hp1 _







omit [Fintype ι] in
private theorem mass_le_bMass (retained : Finset (Finset ι)) (m : Finset ι → ℝ)
    (hm : ∀ S ∈ retained, 0 ≤ m S) (S : Finset ι) (hS : S ∈ retained) :
    m S ≤ bMass retained m S := by
  have h := Finset.single_le_sum (s := retained)
    (f := fun T => if S ⊆ T then m T else 0)
    (by intro T hT; split_ifs <;> simp_all) hS
  simpa only [bMass, ite_true, Finset.Subset.refl] using h

/-- A retained component above the threshold activates its entire support.
This supplies the source-specific coverage used in the residual argument. -/
private theorem fourierActivation_fires_of_component_large {k p δ η : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : δ ≤ 1) (f : Cube ι → ℝ)
    (S : Finset ι) (x : Cube ι) (hS : S ∈ significantSets p f k η)
    (hx : η ≤ |Fourier.component p f S x|) :
    (fourierActivation k p δ η f).fires S x := by
  refine ⟨significantSets_card p f k η S hS, ?_⟩
  calc
    δ * localMass p S x ≤ localMass p S x := by
      simpa only [localMass, one_mul] using
        mul_le_mul_of_nonneg_right hδ (weight_nonneg hp0 hp1 (fun i : S => x i))
    _ ≤ componentTailMass p f η S := localMass_le_componentTailMass hp0 hp1 f η S x hx
    _ ≤ bMass (significantSets p f k η) (componentTailMass p f η) S :=
      mass_le_bMass _ _ (fun T _ => componentTailMass_nonneg hp0 hp1 f η T) S hS

private theorem component_lt_of_not_fires {k p δ η : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : δ ≤ 1) (f : Cube ι → ℝ)
    (S : Finset ι) (x : Cube ι) (hS : S ∈ significantSets p f k η)
    (hx : ¬ (fourierActivation k p δ η f).fires S x) :
    |Fourier.component p f S x| < η := by
  by_contra h
  exact hx (fourierActivation_fires_of_component_large hp0 hp1 hδ f S x hS (le_of_not_gt h))

























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





























section Generic
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]





end Generic





private theorem revealedComponent_measurable (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (S : Finset ι) (x y : Cube ι) (hxy : (restrict J S).SameAtom x y) :
    revealedComponent p J f S x = revealedComponent p J f S y := by
  have hfire : J.fires S x ↔ J.fires S y := by
    simpa only [restrict, Finset.Subset.refl, true_and] using fires_congr_atom (restrict J S) S hxy
  unfold revealedComponent
  by_cases hx : J.fires S x
  · rw [if_pos hx, if_pos (hfire.mp hx)]
    apply Fourier.component_locality
    intro i hi
    exact hxy.2 i (Activation.mem_active_of_fires
      (show (restrict J S).fires S x from ⟨Finset.Subset.refl S,hx⟩) hi)
  · rw [if_neg hx, if_neg (fun hy => hx (hfire.mpr hy))]

/-- The diagonal residual is bounded by component energy where its support does not fire. -/
private theorem diagonal_residual_le_inactive {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (J : Activation ι) (f : Cube ι → ℝ) (S : Finset ι) :
    ConditionalExpectation.squaredError (weight p) (Fourier.component p f S)
      (approxComponent p J f S) ≤
      expectation p (fun x => if J.fires S x then 0 else Fourier.component p f S x ^ 2) := by
  have h := ConditionalExpectation.squaredError_minimal_of_measurable
    (ConditionalExpectation.adaptiveCode (restrict J S)) (weight p)
    (Fourier.component p f S) (revealedComponent p J f S) (weight_pos hp0 hp1)
    (fun x y hxy => revealedComponent_measurable p J f S x y
      ((ConditionalExpectation.adaptiveCode_eq_iff (restrict J S) x y).mp hxy))
  apply h.trans_eq
  unfold ConditionalExpectation.squaredError expectation
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : J.fires S x <;> simp [revealedComponent, hx]










section GenericBound
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]



end GenericBound




/-- The exact activation coverage converts diagonal error into the small-component mass. -/
private theorem diagonal_residual_le_small_component {p k δ η : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hδ : δ ≤ 1) (f : Cube ι → ℝ)
    (S : Finset ι) (hS : S ∈ HatamiActivation.significantSets p f k η) :
    ConditionalExpectation.squaredError (weight p) (Fourier.component p f S)
      (approxComponent p (HatamiActivation.fourierActivation k p δ η f) f S) ≤
      expectation p (fun x => if |Fourier.component p f S x| ≤ η then
        Fourier.component p f S x ^ 2 else 0) := by
  apply (diagonal_residual_le_inactive hp0 hp1 _ f S).trans
  apply expectation_mono hp0.le hp1.le
  intro x
  by_cases hx : (HatamiActivation.fourierActivation k p δ η f).fires S x
  · simp only [if_pos hx]
    split_ifs <;> positivity
  · have hsmall := HatamiActivation.component_lt_of_not_fires hp0.le hp1.le hδ f S x hS hx
    simp [hx, hsmall.le]

/-- Finite-subfamily linearity of product expectation. -/
private theorem expectation_finset_sum {κ : Type*} (p : ℝ) (s : Finset κ)
    (F : κ → Cube ι → ℝ) :
    expectation p (fun x => ∑ j ∈ s, F j x) = ∑ j ∈ s, expectation p (F j) := by
  unfold expectation
  simp only [Finset.mul_sum]
  exact Finset.sum_comm














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
/-- All diagonal terms are controlled by the exact low-degree small-component quantity
which appears in Bourgain's Step II; its analytic estimate remains a separate input. -/
theorem solution {p k δ η : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hδ : δ ≤ 1) (f : Cube ι → ℝ) :
    (∑ S ∈ HatamiActivation.significantSets p f k η,
      ConditionalExpectation.squaredError (weight p) (Fourier.component p f S)
        (approxComponent p (HatamiActivation.fourierActivation k p δ η f) f S)) ≤
      expectation p (fun x =>
        ∑ S ∈ Finset.univ.filter (fun S : Finset ι => (S.card : ℝ) ≤ k),
          if |Fourier.component p f S x| ≤ η then Fourier.component p f S x ^ 2 else 0) := by
  rw [expectation_finset_sum]
  calc
    _ ≤ ∑ S ∈ HatamiActivation.significantSets p f k η,
        expectation p (fun x => if |Fourier.component p f S x| ≤ η then
          Fourier.component p f S x ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro S hS
      exact diagonal_residual_le_small_component hp0 hp1 hδ f S hS
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro S hS
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, HatamiActivation.significantSets_card p f k η S hS⟩
      · intro S _ _
        apply expectation_nonneg hp0.le hp1.le
        intro x
        split_ifs <;> positivity
