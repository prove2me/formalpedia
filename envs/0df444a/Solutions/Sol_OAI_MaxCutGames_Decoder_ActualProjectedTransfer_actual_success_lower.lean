-- Prove2me | solution 1 for OAI.MaxCutGames.Decoder.ActualProjectedTransfer.actual_success_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:02:35.592991+00:00
-- url     : https://prove2.me/submissions/43984393-5014-4ffe-9a2d-37fd4d61b873

import Mathlib
import Definitions.Def_OAIQ087A018
import Definitions.Def_OAIQ087A019
import Definitions.Def_OAIQ087A021

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_LabelBound
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Per-label diagonal lower bounds for the actual finite shared sampler.
These bounds retain the output label, which is necessary for comparing the
sampler's output distribution with a prescribed diagonal distribution. -/

/-!
Finite real probability vectors and information inequalities.

`relativeEntropy` uses the natural logarithm and a real-valued finite sum.
Its theorems require support containment, so a positive numerator is never
silently assigned finite divergence against a zero denominator.
-/

/-! Exact finite total variation and its event-probability bound. -/

namespace MaxCutGames.Foundations.Games.FiniteDistribution

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem totalVariation_comm (μ ν : FiniteDistribution Ω) :
    μ.totalVariation ν = ν.totalVariation μ := by
  unfold totalVariation
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm _ _

end MaxCutGames.Foundations.Games.FiniteDistribution

/-!
Conditioning of actual finite distributions and the selected-coordinate chain
rule used in parallel repetition. A normalized conditional distribution is only
constructed when the conditioning event has strictly positive probability.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RowErasureSliceQuotient
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Every nonempty affine row/column slice is an affine copy of the full space of
linear maps from the column quotient into the row kernel. This gives exact
uniform-law transport and preserves the affine evaluation offset.
-/

namespace MaxCutGames.Inverse.RowErasureSliceQuotient

noncomputable section

variable {R E K L : Type*} [Field R]
  [AddCommGroup E] [AddCommGroup K] [AddCommGroup L]
  [Module R E] [Module R K] [Module R L]

/-- Exact uniform-law transport through the affine parametrization. -/
theorem expect_equiv (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K)
    [Fintype ((E ⧸ Q) →ₗ[R] A.ker)] [Fintype (AffineSlice A Q M₀)]
    (f : AffineSlice A Q M₀ → ℝ) :
    Finset.univ.expect (fun N => f (equiv A Q M₀ N)) = Finset.univ.expect f := by
  exact Fintype.expect_equiv (equiv A Q M₀) _ _ (fun _ => rfl)

end
end MaxCutGames.Inverse.RowErasureSliceQuotient

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_PartnerProjection
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite cardinality of the concrete projection kernel. This packages the explicit
bit parametrization of Lemma 6.1 as a genuine equivalence, then counts its points.
No vector-space dimension formula is assumed.
-/

/-!
# Exact kernel counts for binary linear maps

The last paragraph of Theorem 3.4 uses the fact that a uniform vector in a
binary vector space lands in the kernel of a rank-k map with probability
2⁻ᵏ. These theorems prove its exact integer-count form from mathlib's
rank-nullity and finite-vector-space cardinality theorems. The target space
does not have to be finite, and no injectivity of any factor map is assumed.
-/

namespace MaxCutGames.Soundness.PartnerLinear

open PartnerProjection
open MaxCutGames.Integration.BinaryLinear (F2 ofBit toBit scalar_cases ofBit_toBit
  toBit_ofBit ofBit_xor)

variable {P : Type} (rhs active : P → Bool) (slot : P → Slot)

theorem projection_apply (x : SourcePoint rhs) :
    projection rhs active slot x = project rhs active slot x := rfl

end MaxCutGames.Soundness.PartnerLinear

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Information
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Every partner linear map has independent raw coefficient coordinates

The coefficient index is exactly `ConditionalIncidences.RawSlot`: one global
coefficient, two coefficients at every full position, and one at every single
position.  The coordinate bijection below is for every actual partner linear
map, and its finite-uniform-law theorem has no distributional hypothesis.
-/

open scoped BigOperators

namespace MaxCutGames.Soundness.PartnerMapCoordinates

open PartnerProjection
open ConditionalIncidences (PositionInside PositionOutside RawSlot RawCoefficients )
open MaxCutGames.Integration.BinaryLinear (F2 ofBit toBit)

variable {P : Type} [DecidableEq P] (rhs : P → Bool) (J : Finset P)

variable [Fintype P]

variable (R : Type) [AddCommGroup R] [Module F2 R]

/-- The raw-coefficient formula for every partner point. -/
theorem mapEquiv_expansion (gamma : RawCoefficients J R) (y : PartnerPoint rhs (activeOf J)) :
    mapEquiv rhs J R gamma y =
      ofBit y.homogeneous • gamma none +
        (∑ j : PositionOutside J,
          (ofBit (y.full j.val).first • gamma (some (.inl (j, 0))) +
            ofBit (y.full j.val).second • gamma (some (.inl (j, 1))))) +
        ∑ j : PositionInside J, ofBit (y.single j.val) • gamma (some (.inr j)) := by
  rw [mapEquiv_apply, Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, pointEquiv_none, pointEquiv_full_first,
    pointEquiv_full_second, pointEquiv_single]
  simp only [add_assoc]

theorem pullback_expansion (gamma : RawCoefficients J R) (slot : P → Slot)
    (x : SourcePoint rhs) :
    mapEquiv rhs J R gamma (PartnerLinear.projection rhs (activeOf J) slot x) =
      ofBit x.homogeneous • gamma none +
        (∑ j : PositionOutside J,
          (ofBit (x.coordinates j.val).first • gamma (some (.inl (j, 0))) +
            ofBit (x.coordinates j.val).second • gamma (some (.inl (j, 1))))) +
        ∑ j : PositionInside J,
          ofBit (retained (slot j.val) (x.coordinates j.val)) • gamma (some (.inr j)) := by
  rw [mapEquiv_expansion]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp [PartnerLinear.projection_apply, project, activeOf, j.property]
  · apply Finset.sum_congr rfl
    intro j _
    simp [PartnerLinear.projection_apply, project, activeOf, j.property]

end MaxCutGames.Soundness.PartnerMapCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_IncidenceExtraction
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
This bridge connects the concrete partner projection to the actual equation/name
predicate of the incidence game. It uses no probabilistic or analytic hypotheses.
-/

namespace MaxCutGames.Reduction.ActualCanonical

open Integration.BinaryLinear ActualHomogeneous
open scoped BigOperators

universe u v w
variable {k : Nat}
variable {Name : Type u} {Id : Type v} {R : Type w}
variable [AddCommGroup R] [Module F2 R] [DecidableEq R]

omit [DecidableEq R] in
theorem add_both (x y t : R) : (x + t) + (y + t) = x + y := by
  calc
    _ = (x + y) + (t + t) := by abel
    _ = _ := by rw [add_self, add_zero]

omit [Module F2 R] in
theorem pivot_translate (a : Fin 3 → R) (t : R) :
    pivot (translate a t) = pivot a + t := by
  classical
  by_cases h1 : a 0 = a 1 <;> by_cases h2 : a 0 = a 2 <;>
    simp [pivot, translate, h1, h2]

theorem normalize_translate (a : Fin 3 → R) (t : R) :
    normalize (translate a t) = normalize a := by
  unfold normalize
  rw [pivot_translate]
  funext i
  exact add_both _ _ _

theorem record_translate (names : Id → Fin 3 → Name) (e : Id) (a : Fin 3 → R) (t : R) :
    record names e (translate a t) = record names e a := by
  classical
  have hs (i : Fin 3) : translate a t i = a i + t := rfl
  simp only [record, hs, add_right_cancel_iff, add_both, normalize_translate]

theorem data_gauge (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (z : R) (a : Fin k → Fin 3 → R) (t : Fin k → R) :
    data occ names rhs (z + ∑ j, rhs (occ j) • t j) (fun j => translate (a j) (t j)) =
      data occ names rhs z a := by
  apply Prod.ext
  · simp only [data, pivot_translate, smul_add, Finset.sum_add_distrib]
    exact add_both _ _ _
  · funext j
    exact record_translate names (occ j) (a j) (t j)

omit [DecidableEq R] in
/-- Equality on the homogeneous space forces the free-coordinate identities. -/
theorem extension_coefficients (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R)
    (X : E k →ₗ[F2] R) (h : Represents b z a X) :
    X (hBasis k) = z + ∑ j, b j • a j 2 ∧
      ∀ j, X (firstBasis j) = a j 0 + a j 2 ∧
        X (secondBasis j) = a j 1 + a j 2 := by
  constructor
  · simpa only [ambientEval_hBasis] using (h (hBasis k)).symm
  · intro j
    exact ⟨by simpa only [ambientEval_firstBasis] using (h (firstBasis j)).symm,
      by simpa only [ambientEval_secondBasis] using (h (secondBasis j)).symm⟩

/-- Every ambient extension of a genuine map gives the same canonical data. -/
theorem canonical_eq_of_extension (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (z : R) (a : Fin k → Fin 3 → R) (X : E k →ₗ[F2] R)
    (h : Represents (fun j => rhs (occ j)) z a X) :
    canonical occ names rhs X = data occ names rhs z a := by
  obtain ⟨hz, ha⟩ := extension_coefficients _ z a X h
  have ht : standardTriple X = fun j => translate (a j) (a j 2) := by
    funext j i
    fin_cases i
    · exact (ha j).1
    · exact (ha j).2
    · exact (add_self (a j 2)).symm
  unfold canonical
  rw [hz, ht]
  exact data_gauge occ names rhs z a (fun j => a j 2)

omit [Module F2 R] in
theorem pivot_singleton (i : Fin 3) (c : R) : pivot (singletonTriple i c) = 0 := by
  classical
  by_cases hc : c = 0 <;> fin_cases i <;> simp [singletonTriple, pivot, hc]

omit [Module F2 R] in
theorem record_singleton (names : Id → Fin 3 → Name) (e : Id) (i : Fin 3) (c : R) :
    record names e (singletonTriple i c) =
      (if c = 0 then Record.blank else Record.single (names e i) c) := by
  classical
  by_cases hc : c = 0 <;> fin_cases i <;>
    simp [record, singletonTriple, hc, eq_comm]

theorem singleton_global_adjustment (rhs : Id → F2) (e : Id) (i : Fin 3) (c : R) :
    rhs e • pivot (singletonTriple i c) = 0 := by rw [pivot_singleton, smul_zero]

omit [Module F2 R] in
/-- The hidden occurrence and its internal slot cannot affect a retained
single-variable record. The occurrence need not differ from other positions. -/
theorem singleton_locality (names : Id → Fin 3 → Name) (e e' : Id)
    (i i' : Fin 3) (c : R) (hname : names e i = names e' i') :
    record names e (singletonTriple i c) = record names e' (singletonTriple i' c) := by
  simp only [record_singleton, hname]

end MaxCutGames.Reduction.ActualCanonical

/-! Canonical-row descent for every actual partner linear map. -/

namespace MaxCutGames.Soundness.ActualCanonicalPullback

open scoped BigOperators
open PartnerProjection PartnerMapCoordinates
open ConditionalIncidences
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction

noncomputable section

variable {k : Nat} (rhsB : Fin k → Bool) (J : Finset (Fin k))
variable (R : Type) [AddCommGroup R] [Module F2 R]

theorem ofBit_and (a b : Bool) : ofBit (a && b) = ofBit a * ofBit b := by
  cases a <;> cases b <;> decide

theorem inverse_homogeneous (v : ActualHomogeneous.E k) :
    ofBit (((PartnerLinear.sourceLinearEquiv rhsB).symm v).homogeneous) = v.1 :=
  ofBit_toBit _

theorem inverse_first (v : ActualHomogeneous.E k) (j : Fin k) :
    ofBit ((((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j).first) =
      (v.2 j).1 := ofBit_toBit _

theorem inverse_second (v : ActualHomogeneous.E k) (j : Fin k) :
    ofBit ((((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j).second) =
      (v.2 j).2 := ofBit_toBit _

theorem inverse_retained_free (v : ActualHomogeneous.E k) (j : Fin k)
    (slot : Fin k → Slot) :
    ofBit (retained (slot j)
      (((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j)) =
        selectedFree (fun j => ofBit (rhsB j)) slot v j := by
  unfold selectedFree
  cases hslot : slot j with
  | first => exact ofBit_toBit _
  | second => exact ofBit_toBit _
  | third =>
    change ofBit (((rhsB j && toBit v.1).xor (toBit (v.2 j).1)).xor
      (toBit (v.2 j).2)) = ofBit (rhsB j) * v.1 + (v.2 j).1 + (v.2 j).2
    rw [ofBit_xor, ofBit_xor, ofBit_and, ofBit_toBit, ofBit_toBit, ofBit_toBit]

theorem freePullback_expansion (gamma : RawCoefficients J R)
    (slot : Fin k → Slot) (v : ActualHomogeneous.E k) :
    freePullback rhsB J R gamma slot v =
      v.1 • gamma none +
        (∑ j : PositionOutside J, ((v.2 j.val).1 • gamma (some (.inl (j,0))) +
          (v.2 j.val).2 • gamma (some (.inl (j,1))))) +
        ∑ j : PositionInside J, selectedFree (fun j => ofBit (rhsB j)) slot v j.val •
          gamma (some (.inr j)) := by
  change mapEquiv rhsB J R gamma
    (PartnerLinear.projection rhsB (activeOf J) slot
      ((PartnerLinear.sourceLinearEquiv rhsB).symm v)) = _
  rw [pullback_expansion]
  simp only [inverse_homogeneous, inverse_first, inverse_second, inverse_retained_free]

omit [Module F2 R] in
theorem sum_outside_inside (f : PositionOutside J → R) (g : PositionInside J → R) :
    (∑ j, f j) + (∑ j, g j) =
      ∑ j : Fin k, if hj : j ∈ J then g ⟨j,hj⟩ else f ⟨j,hj⟩ := by
  rw [← (outsideInsideEquiv J).sum_comp]
  rw [Fintype.sum_sum_type]
  congr 1 <;> apply Finset.sum_congr rfl
  · intro j _
    simp [outsideInsideEquiv, j.property]
  · intro j _
    simp [outsideInsideEquiv, j.property]

theorem raw_represents (gamma : RawCoefficients J R) (slot : Fin k → Slot) :
    ActualCanonical.Represents (fun j => ofBit (rhsB j)) (gamma none)
      (ambientCoefficients J R gamma slot) (freePullback rhsB J R gamma slot) := by
  intro v
  let f : PositionOutside J → R := fun j =>
    (v.2 j.val).1 • gamma (some (.inl (j,0))) +
      (v.2 j.val).2 • gamma (some (.inl (j,1)))
  let g : PositionInside J → R := fun j =>
    selectedFree (fun j => ofBit (rhsB j)) slot v j.val • gamma (some (.inr j))
  have hs : (∑ j, f j) + (∑ j, g j) =
      ∑ j : Fin k, ((v.2 j).1 • ambientCoefficients J R gamma slot j 0 +
        (v.2 j).2 • ambientCoefficients J R gamma slot j 1 +
        (ofBit (rhsB j) * v.1 + (v.2 j).1 + (v.2 j).2) •
          ambientCoefficients J R gamma slot j 2) := by
    rw [sum_outside_inside]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · cases hslot : slot j <;>
        simp [g, ambientCoefficients, selectedFree, hj, hslot, ConcreteExtraction.slotIndex]
    · simp [f, ambientCoefficients, hj]
  calc
    ActualCanonical.ambientEval _ _ _ v = v.1 • gamma none + ((∑ j, f j) + (∑ j, g j)) :=
      congrArg (fun z : R => v.1 • gamma none + z) hs.symm
    _ = (v.1 • gamma none + (∑ j, f j)) + (∑ j, g j) := (add_assoc _ _ _).symm
    _ = freePullback rhsB J R gamma slot v :=
      (freePullback_expansion rhsB J R gamma slot v).symm

theorem canonical_raw_pullback [DecidableEq R] {Id Name : Type} [DecidableEq Id] [DecidableEq Name]
    (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (gamma : RawCoefficients J R) (slot : Fin k → Slot) :
    ActualCanonical.canonical occ names rhs
      (freePullback (fun j => toBit (rhs (occ j))) J R gamma slot) =
    ActualCanonical.data occ names rhs (gamma none) (ambientCoefficients J R gamma slot) := by
  apply ActualCanonical.canonical_eq_of_extension
  simpa only [ofBit_toBit] using raw_represents (fun j => toBit (rhs (occ j))) J R gamma slot

omit [Module F2 R] in
theorem ambientCoefficients_single (gamma : RawCoefficients J R) (slot : Fin k → Slot)
    (j : Fin k) (hj : j ∈ J) :
    ambientCoefficients J R gamma slot j =
      ActualCanonical.singletonTriple (ConcreteExtraction.slotIndex (slot j))
        (gamma (some (.inr ⟨j,hj⟩))) := by
  funext i
  simp [ambientCoefficients, hj, ActualCanonical.singletonTriple, Pi.single_apply]

omit [Module F2 R] in
theorem ambientCoefficients_full_eq (gamma : RawCoefficients J R)
    (slot slot' : Fin k → Slot) (j : Fin k) (hj : j ∉ J) :
    ambientCoefficients J R gamma slot j = ambientCoefficients J R gamma slot' j := by
  funext i
  simp [ambientCoefficients, hj]

/-- Raw canonical data is determined by the full displayed occurrences and
    retained variable names. Hidden single occurrences and slot indices vanish. -/
theorem raw_data_locality [DecidableEq R] {Id Name : Type}
    (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot)
    (gamma : RawCoefficients J R)
    (hfull : ∀ j, j ∉ J → occ j = occ' j)
    (hsingle : ∀ j, j ∈ J → names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
      names (occ' j) (ConcreteExtraction.slotIndex (slot' j))) :
    ActualCanonical.data occ names rhs (gamma none) (ambientCoefficients J R gamma slot) =
      ActualCanonical.data occ' names rhs (gamma none) (ambientCoefficients J R gamma slot') := by
  apply Prod.ext
  · change gamma none + _ = gamma none + _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · rw [ambientCoefficients_single J R gamma slot j hj,
        ambientCoefficients_single J R gamma slot' j hj]
      simp only [ActualCanonical.singleton_global_adjustment]
    · rw [hfull j hj, ambientCoefficients_full_eq J R gamma slot slot' j hj]
  · funext j
    change ActualCanonical.record names (occ j) (ambientCoefficients J R gamma slot j) =
      ActualCanonical.record names (occ' j) (ambientCoefficients J R gamma slot' j)
    by_cases hj : j ∈ J
    · rw [ambientCoefficients_single J R gamma slot j hj,
        ambientCoefficients_single J R gamma slot' j hj]
      exact ActualCanonical.singleton_locality names _ _ _ _ _ (hsingle j hj)
    · rw [hfull j hj, ambientCoefficients_full_eq J R gamma slot slot' j hj]

/-- Lemma 6.2 for the actual pullbacks in the shared F₂ coordinate model. -/
theorem canonical_private_input_locality [DecidableEq R]
    {Id Name : Type} [DecidableEq Id] [DecidableEq Name]
    (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot)
    (gamma : RawCoefficients J R)
    (hfull : ∀ j, j ∉ J → occ j = occ' j)
    (hsingle : ∀ j, j ∈ J → names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
      names (occ' j) (ConcreteExtraction.slotIndex (slot' j))) :
    ActualCanonical.canonical occ names rhs
      (freePullback (fun j => toBit (rhs (occ j))) J R gamma slot) =
    ActualCanonical.canonical occ' names rhs
      (freePullback (fun j => toBit (rhs (occ' j))) J R gamma slot') := by
  rw [canonical_raw_pullback, canonical_raw_pullback]
  exact raw_data_locality J R names rhs occ occ' slot slot' gamma hfull hsingle

end
end MaxCutGames.Soundness.ActualCanonicalPullback

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RawPartnerTarget
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A partner target whose coordinates depend only on the displayed full/single
positions. It does not contain hidden occurrence identities or right-hand sides. -/

namespace MaxCutGames.Soundness.RawPartnerTarget
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open PartnerProjection PartnerMapCoordinates ConditionalIncidences

attribute [local instance] Classical.propDecidable

variable {k : Nat} {R : Type} [AddCommGroup R] [Module F2 R]

theorem rawMap_pullback (rhsB : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) (Y : RawPoint J →ₗ[F2] R) :
    Y.comp (rawProjection rhsB J slot) =
      ActualCanonicalPullback.freePullback rhsB J R (gammaOfRawMap J Y) slot := by
  apply LinearMap.ext
  intro x
  change Y (pointEquiv rhsB J
      (PartnerLinear.projection rhsB (activeOf J) slot
        ((PartnerLinear.sourceLinearEquiv rhsB).symm x))) =
    mapEquiv rhsB J R (gammaOfRawMap J Y)
      (PartnerLinear.projection rhsB (activeOf J) slot
        ((PartnerLinear.sourceLinearEquiv rhsB).symm x))
  exact rawMap_on_partner rhsB J Y _

end MaxCutGames.Soundness.RawPartnerTarget

/-!
# Complete local private inputs after fixing H

The constructors here consume only the appropriate zero-set question tuple:
occurrences for the first player, names for the second. A single reference sample
from the positive observation fibre is fixed once as part of H-dependent advice.
It supplies arbitrary padding at hidden positions and never depends on the actual
remaining sample. The reconstruction theorems prove equality of the complete
question-plus-row input, and the row maps restrict to the actual equation spaces
as shown in `ZeroInformation.supplied_map_pullback`.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RawPrivateTable
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The private Fourier table is defined from displayed data alone. Compatibility
with every hidden extension follows from the proved canonical locality theorem. -/

namespace MaxCutGames.Soundness.RawPrivateTable
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open PartnerProjection RawPartnerTarget

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} {Id Name : Type}

theorem full_occurrence_eq_of_displayed_eq
    {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    {occ occ' : Fin k → Id} {slot slot' : Fin k → Slot}
    (h : displayed J names occ slot = displayed J names occ' slot')
    (j : Fin k) (hj : j ∉ J) : occ j = occ' j := by
  simpa [displayed, hj] using congrFun h j

theorem single_name_eq_of_displayed_eq
    {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    {occ occ' : Fin k → Id} {slot slot' : Fin k → Slot}
    (h : displayed J names occ slot = displayed J names occ' slot')
    (j : Fin k) (hj : j ∈ J) :
    names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
      names (occ' j) (ConcreteExtraction.slotIndex (slot' j)) := by
  simpa [displayed, hj] using congrFun h j

theorem representative_display {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    (V : SupportedV J names) :
    displayed J names (representative V).1 (representative V).2 = V.val :=
  Classical.choose_spec V.property

variable (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
  {R D C Label : Type} [AddCommGroup R] [Module F2 R] [DecidableEq R]
  [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]
  [DecidableEq Id] [DecidableEq Name]

theorem canonical_same_display (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot)
    (Y : RawPoint J →ₗ[F2] R)
    (h : displayed J names occ slot = displayed J names occ' slot') :
    ActualCanonical.canonical occ names rhs (Y.comp (projection J rhs occ slot)) =
      ActualCanonical.canonical occ' names rhs (Y.comp (projection J rhs occ' slot')) := by
  unfold projection
  rw [rawMap_pullback, rawMap_pullback]
  exact ActualCanonicalPullback.canonical_private_input_locality J R names rhs
    occ occ' slot slot' (gammaOfRawMap J Y)
    (full_occurrence_eq_of_displayed_eq h) (single_name_eq_of_displayed_eq h)

end
end MaxCutGames.Soundness.RawPrivateTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_AdviceFibers
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact visible row advice and private matrix coordinates

Every nonempty fiber of `M ↦ A ∘ M` is an affine copy of
`Hom(E, ker A)`, whether or not `A` is surjective.  Choosing one base matrix
for each attainable row gives a product decomposition of the complete matrix
space.  Uniform sampling therefore makes visible row advice and the hidden
kernel-valued matrix independent.
-/

noncomputable section
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear

namespace MaxCutGames.Decoder.AdviceFibers

variable {E K R : Type*}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup K] [Module F2 K]
  [AddCommGroup R] [Module F2 R]

/-- Affine target intercepts are retained in the private coordinates. -/
theorem assemble_affine_target (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K)
    (N : E →ₗ[F2] A.ker) (z : E) (u : K) :
    assemble A M₀ N z + u = (N z : K) + (M₀ z + u) := by
  rw [assemble_apply]
  ac_rfl

end MaxCutGames.Decoder.AdviceFibers
end

/-! The finite set of realizable orbit records.  Vertices are the image of the
actual canonical-data map, so equal retained data from different questions
become one vertex.  The two sides remain distinct. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Deletion
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Fourier.MatrixRestrictions

open MaxCutGames.Integration.BinaryLinear
open scoped BigOperators

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup C] [Module F2 C]

theorem quotientKernel_card (W : Submodule F2 E)
    [Fintype {T : C →ₗ[F2] E // W.mkQ.comp T = 0}]
    [Fintype (C →ₗ[F2] W)] :
    Fintype.card {T : C →ₗ[F2] E // W.mkQ.comp T = 0} =
      Fintype.card (C →ₗ[F2] W) :=
  Fintype.card_congr (quotientKernelEquiv W)

end MaxCutGames.Fourier.MatrixRestrictions

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_SparseLaw
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite calculation behind v2 Lemma `projected-tv`. The three singleton
lines are averaged before the divergence is taken; projection choices are
not part of the compared sample space. Coordinates are independently sampled
occurrences, irrespective of whether their equation IDs coincide.
-/

namespace MaxCutGames.Decoder.SparseLaw

open scoped BigOperators
open MaxCutGames.Foundations.Information

noncomputable section

variable {α : Type*} [Fintype α]

section Singleton

variable (V : Type*) [Fintype V] [Zero V] [DecidableEq V]

theorem singletonSamplerWeights_eq (z : V × V) :
    singletonSamplerWeights V z = singletonPairWeights V z := by
  classical
  rcases z with ⟨x, y⟩
  have hleft : (∑ a : V, if (a, 0) = (x, y) then uniformWeights V a else 0) =
      if y = 0 then 1 / (Fintype.card V : ℝ) else 0 := by
    by_cases hy : y = 0
    · simp [hy, uniformWeights]
    · simp [Prod.mk.injEq, Ne.symm hy, hy]
  have hright : (∑ a : V, if (0, a) = (x, y) then uniformWeights V a else 0) =
      if x = 0 then 1 / (Fintype.card V : ℝ) else 0 := by
    by_cases hx : x = 0
    · simp [hx, uniformWeights]
    · simp [Prod.mk.injEq, Ne.symm hx, hx]
  have hdiag : (∑ a : V, if (a, a) = (x, y) then uniformWeights V a else 0) =
      if x = y then 1 / (Fintype.card V : ℝ) else 0 := by
    by_cases hxy : x = y
    · simp [hxy, uniformWeights]
    · have hnone (a : V) : (a, a) ≠ (x, y) := by
        intro ha
        have he := Prod.mk.inj ha
        exact hxy (he.1.symm.trans he.2)
      simp [hnone, hxy]
  simp only [singletonSamplerWeights, hleft, hright, hdiag,
    singletonPairWeights, lineCount]
  split_ifs <;> ring

end Singleton

variable {V : Type*} [Fintype V] [AddGroup V] [DecidableEq V]

theorem uniform_intercept_pushforward (shift z : V) :
    (∑ t : V, if t + shift = z then uniformWeights V t else 0) =
      uniformWeights V z := by
  classical
  simp [← eq_sub_iff_add_eq, uniformWeights]

omit [Fintype α] in
theorem joint_intercept_pushforward (p : α → ℝ) (shift : α → V) (a : α) (z : V) :
    (∑ t : V, if t + shift a = z then p a * uniformWeights V t else 0) =
      p a * uniformWeights V z := by
  classical
  calc
    _ = p a * (∑ t : V, if t + shift a = z then uniformWeights V t else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      split <;> simp_all
    _ = _ := by rw [uniform_intercept_pushforward]

end
end MaxCutGames.Decoder.SparseLaw

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_PaddedLaw
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual linear-map realization of the sparse padded-table experiment.
The finite sample has one independent full pair or singleton coefficient at
each occurrence position and one independent homogeneous intercept. Its map
is formed by composing a genuine map on the raw projected target with the
actual parity projection. The third position contributes its parity-dependent
intercept; it is not treated as a homogeneous two-coordinate projection.
-/

namespace MaxCutGames.Decoder.PaddedLaw

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open ConditionalIncidences PartnerProjection RawPartnerTarget RawMapLaw
open ActualCanonicalPullback
open SparseLaw

noncomputable section
attribute [local instance] Classical.propDecidable

section FinitePushforward

variable {α B : Type*} [Fintype α]

theorem pushforwardWeight_pi (p : α → ℝ) (f : α → B) (k : ℕ)
    (ys : Fin k → B) :
    pushforwardWeight (independentWeights p k) (fun xs i => f (xs i)) ys =
      independentWeights (pushforwardWeight p f) k ys := by
  classical
  simp only [pushforwardWeight, independentWeights]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro xs _
  simp only [Fintype.prod_ite_zero, funext_iff]
  split_ifs <;> rfl

theorem pushforwardWeight_joint_uniform_intercept {W : Type*} [Fintype W] [AddGroup W]
    (p : α → ℝ) (f : α → B) (shift : α → W) (z : W) (b : B) :
    pushforwardWeight (fun az : α × W => p az.1 * uniformWeights W az.2)
      (fun az => (az.2 + shift az.1, f az.1)) (z, b) =
        uniformWeights W z * pushforwardWeight p f b := by
  classical
  simp only [pushforwardWeight, Fintype.sum_prod_type]
  calc
    (∑ a : α, ∑ t : W,
        if (t + shift a, f a) = (z, b) then p a * uniformWeights W t else 0) =
      ∑ a : α, if f a = b then p a * uniformWeights W z else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : f a = b
        · simp only [Prod.mk.injEq, h, and_true, ite_true, if_true]
          exact joint_intercept_pushforward p shift a z
        · simp [Prod.mk.injEq, h]
    _ = uniformWeights W z * (∑ a : α, if f a = b then p a else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : f a = b <;> simp [h, mul_comm]

end FinitePushforward

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V]

theorem slotIndex_decodeSlot (i : Fin 3) : ConcreteExtraction.slotIndex (decodeSlot i) = i := by
  fin_cases i <;> rfl

omit [Module F2 V] in
theorem ambientCoefficients_draw (d : Fin k → BlockDraw V) (z : V) :
    ambientCoefficients (singletonPositions d) V (drawCoefficients d z) (drawSlots d) =
      fun j => blockAmbient (d j) := by
  funext j i
  cases hd : d j with
  | inl ab =>
      fin_cases i <;>
        simp [ambientCoefficients, singletonPositions, drawCoefficients, blockAmbient, hd]
  | inr ia =>
      simp [ambientCoefficients, singletonPositions, drawCoefficients, drawSlots,
        blockAmbient, hd, slotIndex_decodeSlot, Pi.single_apply]

theorem paddedMap_toCoefficients (rhs : Fin k → Bool) (d : Fin k → BlockDraw V)
    (z : V) :
    ActualEnumeration.toCoefficients k V (paddedMap rhs d z) =
      (z + interceptShift rhs d, fun j => blockSlopes (d j)) := by
  have hrep := raw_represents rhs (singletonPositions d) V (drawCoefficients d z) (drawSlots d)
  rw [ambientCoefficients_draw] at hrep
  have hc := ActualCanonical.extension_coefficients _ _ _ _ hrep
  have hmap : paddedMap rhs d z =
      freePullback rhs (singletonPositions d) V (drawCoefficients d z) (drawSlots d) := by
    unfold paddedMap
    rw [rawMap_pullback, coefficients_rawMap]
  rw [hmap]
  apply Prod.ext
  · exact hc.1
  · funext j
    exact Prod.ext (hc.2 j).1 (hc.2 j).2

omit [Module F2 V] in
theorem tupleDraw_ambient (J : Finset (Fin k)) (slot : Fin k → Slot)
    (a : RawTuple J V) :
    (fun j => blockAmbient (tupleDraw J slot a j)) =
      ambientCoefficients J V (rawTupleEquiv J a) slot := by
  funext j i
  by_cases hj : j ∈ J
  · simp [tupleDraw, hj, blockAmbient, ambientCoefficients, rawTupleEquiv, Pi.single_apply]
  · fin_cases i <;>
      simp [tupleDraw, hj, blockAmbient, ambientCoefficients, rawTupleEquiv]

theorem paddedMap_tupleDraw (rhs : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) (a : RawTuple J V) :
    paddedMap rhs (tupleDraw J slot a) a.1 =
      (rawMap J V (rawTupleEquiv J a)).comp (rawProjection rhs J slot) := by
  have hr := raw_represents rhs J V (rawTupleEquiv J a) slot
  rw [← tupleDraw_ambient] at hr
  have hc := ActualCanonical.extension_coefficients _ _ _ _ hr
  apply (ActualEnumeration.coefficientEquiv k V).symm.injective
  change ActualEnumeration.toCoefficients k V _ = ActualEnumeration.toCoefficients k V _
  rw [paddedMap_toCoefficients, rawMap_pullback, coefficients_rawMap]
  apply Prod.ext
  · exact hc.1.symm
  · funext j
    exact Prod.ext (hc.2 j).1.symm (hc.2 j).2.symm

/-- Conditional on every fixed mask and position choice, independently
uniform full pairs/singletons and intercept give the uniform law on genuine
projected-target maps followed by the actual projection. -/
theorem uniform_fixed_projection_tuple [Fintype V] (rhs : Fin k → Bool)
    (J : Finset (Fin k)) (slot : Fin k → Slot)
    (H : (ActualHomogeneous.E k →ₗ[F2] V) → ℝ) :
    (𝔼 a : RawTuple J V, H (paddedMap rhs (tupleDraw J slot a) a.1)) =
      𝔼 Y : RawPoint J →ₗ[F2] V, H (Y.comp (rawProjection rhs J slot)) := by
  simp_rw [paddedMap_tupleDraw]
  exact Fintype.expect_equiv ((rawTupleEquiv J).trans (rawMapEquiv J V)) _ _ (fun _ => rfl)

variable [Fintype V]

omit [Module F2 V] in
theorem blockWeights_slopes (β : ℝ) (ab : V × V) :
    pushforwardWeight (blockWeights (V := V) β) blockSlopes ab =
      mixture β (singletonPairWeights V) ab := by
  have hfull : (∑ x : V × V, if blockSlopes (.inl x) = ab then
        blockWeights β (.inl x) else 0) = (1 - β) * uniformWeights (V × V) ab := by
    simp [blockWeights]
  have hsingle : (∑ ia : Fin 3 × V, if blockSlopes (.inr ia) = ab then
        blockWeights β (.inr ia) else 0) = β * singletonSamplerWeights V ab := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_three]
    simp only [blockSlopes_first, blockSlopes_second,
      blockSlopes_third, blockWeights]
    have hfactor (f : V → V × V) :
        (∑ a : V, if f a = ab then β / 3 * uniformWeights V a else 0) =
          (β / 3) * ∑ a : V, if f a = ab then uniformWeights V a else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split <;> simp_all
    simp only [hfactor, singletonSamplerWeights]
    ring
  unfold pushforwardWeight
  rw [Fintype.sum_sum_type]
  calc
    _ = (∑ x : V × V, if blockSlopes (.inl x) = ab then blockWeights β (.inl x) else 0) +
        (∑ ia : Fin 3 × V, if blockSlopes (.inr ia) = ab then blockWeights β (.inr ia) else 0) := by
      congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> split_ifs <;> rfl
    _ = _ := by rw [hfull, hsingle, singletonSamplerWeights_eq]; rfl

theorem paddedWeights_eq (rhs : Fin k → Bool) (β : ℝ)
    (a : ActualEnumeration.Coefficients k V) :
    paddedWeights rhs β a = uniformWeights V a.1 *
      independentWeights (mixture β (singletonPairWeights V)) k a.2 := by
  rcases a with ⟨z, slopes⟩
  unfold paddedWeights
  simp_rw [paddedMap_toCoefficients]
  unfold drawWeights
  have hj := pushforwardWeight_joint_uniform_intercept
    (independentWeights (blockWeights (V := V) β) k)
    (fun d j => blockSlopes (d j)) (interceptShift rhs) z slopes
  calc
    _ = uniformWeights V z * pushforwardWeight
        (independentWeights (blockWeights (V := V) β) k)
        (fun d j => blockSlopes (d j)) slopes := by
      convert hj using 1
      all_goals try with_reducible_and_instances rfl
    _ = _ := by
      rw [pushforwardWeight_pi]
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      exact blockWeights_slopes β (slopes j)

theorem uniformWeights_prod {A B : Type*} [Fintype A] [Fintype B] (ab : A × B) :
    uniformWeights (A × B) ab = uniformWeights A ab.1 * uniformWeights B ab.2 := by
  simp [uniformWeights, Fintype.card_prod, Nat.cast_mul, one_div, mul_comm]

theorem totalVariation_uniform_front {A B : Type*} [Fintype A] [Nonempty A] [Fintype B]
    (p q : B → ℝ) :
    MaxCutGames.Foundations.Information.totalVariation
      (fun ab : A × B => uniformWeights A ab.1 * p ab.2)
      (fun ab : A × B => uniformWeights A ab.1 * q ab.2) =
        MaxCutGames.Foundations.Information.totalVariation p q := by
  unfold MaxCutGames.Foundations.Information.totalVariation
  rw [Fintype.sum_prod_type]
  simp only [← mul_sub, abs_mul, abs_of_nonneg (uniformWeights_pos _).le,
    ← Finset.mul_sum, ← Finset.sum_mul, (uniformWeights_isProbability (α := A)).2, one_mul]

theorem paddedWeights_totalVariation_eq_slope (rhs : Fin k → Bool) (β : ℝ) :
    MaxCutGames.Foundations.Information.totalVariation (paddedWeights (V := V) rhs β)
      (uniformWeights (ActualEnumeration.Coefficients k V)) =
        MaxCutGames.Foundations.Information.totalVariation
          (independentWeights (mixture β (singletonPairWeights V)) k)
          (uniformWeights (Fin k → V × V)) := by
  have hp : paddedWeights (V := V) rhs β = fun a => uniformWeights V a.1 *
      independentWeights (mixture β (singletonPairWeights V)) k a.2 := by
    funext a
    exact paddedWeights_eq rhs β a
  have hu : uniformWeights (ActualEnumeration.Coefficients k V) =
      fun a => uniformWeights V a.1 * uniformWeights (Fin k → V × V) a.2 := by
    funext a
    exact uniformWeights_prod a
  rw [hp, hu, totalVariation_uniform_front]

omit [AddCommGroup V] [Module F2 V] in
theorem blockWeights_choice_mixture (β : ℝ) (d : BlockDraw V) :
    blockWeights β d = ∑ c : ProjectionChoice, choiceWeight β c * blockKernel c d := by
  cases d <;>
    simp [Fintype.sum_option, choiceWeight, blockKernel, blockWeights, mul_ite]

omit [AddCommGroup V] [Module F2 V] in
theorem independent_blockWeights_mixture (β : ℝ) (d : Fin k → BlockDraw V) :
    independentWeights (blockWeights β) k d =
      ∑ c : Fin k → ProjectionChoice, choiceTupleWeight β c * kernelTupleWeight c d := by
  unfold independentWeights choiceTupleWeight kernelTupleWeight
  simp_rw [blockWeights_choice_mixture]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact Finset.prod_mul_distrib

omit [AddCommGroup V] [Module F2 V] in
theorem drawWeights_choice_mixture (β : ℝ) (dz : (Fin k → BlockDraw V) × V) :
    drawWeights β k dz = ∑ c : Fin k → ProjectionChoice,
      choiceTupleWeight β c * (kernelTupleWeight c dz.1 * uniformWeights V dz.2) := by
  rw [drawWeights, independent_blockWeights_mixture, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

omit [AddCommGroup V] [Module F2 V] in
/-- This is the unconditioned law identity before replacing the coefficient
kernel by uniform projected-target maps. No division by a mask probability. -/
theorem draw_expectation_choice_mixture (β : ℝ)
    (H : ((Fin k → BlockDraw V) × V) → ℝ) :
    (∑ dz, drawWeights β k dz * H dz) =
      ∑ c : Fin k → ProjectionChoice, choiceTupleWeight β c *
        ∑ dz, (kernelTupleWeight c dz.1 * uniformWeights V dz.2) * H dz := by
  simp_rw [drawWeights_choice_mixture, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro dz _
  ring

omit [AddCommGroup V] [Module F2 V] in
theorem blockKernel_uniform_pushforward (c : ProjectionChoice) (d : BlockDraw V) :
    blockKernel c d =
      pushforwardWeight (uniformWeights (ChoiceValue V c)) (choiceEmbed c) d := by
  cases c with
  | none =>
      cases d <;> simp [blockKernel, pushforwardWeight, choiceEmbed, ChoiceValue]
      exact fun h => False.elim (h (Finset.mem_univ _))
  | some i =>
      cases d with
      | inl ab => simp [blockKernel, pushforwardWeight, choiceEmbed, ChoiceValue]
      | inr ja =>
          rcases ja with ⟨j, a⟩
          by_cases h : i = j <;>
            simp [blockKernel, pushforwardWeight, choiceEmbed, ChoiceValue,
              Prod.mk.injEq, h]
          exact fun h => False.elim (h (Finset.mem_univ _))

theorem pushforwardWeight_pi_dep {I B : Type*} [Fintype I]
    {A : I → Type*} [∀ i, Fintype (A i)]
    (p : (i : I) → A i → ℝ) (f : (i : I) → A i → B) (ys : I → B) :
    pushforwardWeight (fun xs : ∀ i, A i => ∏ i, p i (xs i))
      (fun xs : ∀ i, A i => fun i => f i (xs i)) ys =
      ∏ i, pushforwardWeight (p i) (f i) (ys i) := by
  classical
  simp only [pushforwardWeight]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro xs _
  simp only [Fintype.prod_ite_zero, funext_iff]

omit [AddCommGroup V] [Module F2 V] in
theorem kernelTuple_uniform_pushforward (c : Fin k → ProjectionChoice)
    (d : Fin k → BlockDraw V) :
    kernelTupleWeight c d =
      pushforwardWeight (uniformWeights (∀ j, ChoiceValue V (c j)))
        (fun f j => choiceEmbed (c j) (f j)) d := by
  unfold kernelTupleWeight
  simp_rw [blockKernel_uniform_pushforward]
  rw [← pushforwardWeight_pi_dep]
  have hp : (fun f : ∀ j, ChoiceValue V (c j) =>
      ∏ j, uniformWeights (ChoiceValue V (c j)) (f j)) =
      uniformWeights (∀ j, ChoiceValue V (c j)) := by
    funext f
    simp [uniformWeights, Fintype.card_pi, Nat.cast_prod, one_div,
      Finset.prod_inv_distrib]
  rw [hp]
  congr 1 ; exact Subsingleton.elim _ _

theorem sum_pushforwardWeight_mul {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (f : A → B) (H : B → ℝ) :
    (∑ b, pushforwardWeight p f b * H b) = ∑ a, p a * H (f a) := by
  classical
  simp only [pushforwardWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

theorem sum_uniformWeights_mul {A : Type*} [Fintype A] (H : A → ℝ) :
    (∑ a, uniformWeights A a * H a) = 𝔼 a, H a := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [uniformWeights, ← Finset.mul_sum]
  ring

omit [Module F2 V] [Fintype V] in
theorem restoreChoiceDraw (q : ProjectionChoice) (v : ChoiceValue V q) :
    (if q.isSome then
      Sum.inr (ConcreteExtraction.slotIndex (choiceSlot q),
          singleChoiceValue q v)
    else Sum.inl (fullChoiceValue q v)) = choiceEmbed q v := by
  cases q <;> simp [fullChoiceValue, singleChoiceValue, choiceEmbed, choiceSlot,
    slotIndex_decodeSlot]

omit [Module F2 V] [Fintype V] in
theorem tupleDraw_choiceValues (c : Fin k → ProjectionChoice)
    (fz : (∀ j, ChoiceValue V (c j)) × V) :
    tupleDraw (choiceMask c) (choiceSlots c) (choiceValuesRawTupleEquiv c fz) =
      fun j => choiceEmbed (c j) (fz.1 j) := by
  funext j
  change (if j ∈ choiceMask c then
      Sum.inr (ConcreteExtraction.slotIndex (choiceSlot (c j)),
        singleChoiceValue (c j) (fz.1 j))
    else Sum.inl (fullChoiceValue (c j) (fz.1 j))) = choiceEmbed (c j) (fz.1 j)
  simpa only [choiceMask, Finset.mem_filter,
    Finset.mem_univ, true_and] using restoreChoiceDraw (c j) (fz.1 j)

/-- The whole fixed-choice kernel is precisely the uniform actual-map law.
This lemma closes the gap between an arbitrary fixed-mask sampling experiment
and the conditioning kernel that actually occurs in drawWeights. -/
theorem fixed_choice_kernel_map_expectation
    (rhs : Fin k → Bool) (c : Fin k → ProjectionChoice)
    (H : (ActualHomogeneous.E k →ₗ[F2] V) → ℝ) :
    (∑ dz : (Fin k → BlockDraw V) × V,
      (kernelTupleWeight c dz.1 * uniformWeights V dz.2) *
        H (paddedMap rhs dz.1 dz.2)) =
      𝔼 Y : RawPoint (choiceMask c) →ₗ[F2] V,
        H (Y.comp (rawProjection rhs (choiceMask c) (choiceSlots c))) := by
  calc
    _ = ∑ d : Fin k → BlockDraw V, kernelTupleWeight c d *
        ∑ z : V, uniformWeights V z * H (paddedMap rhs d z) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = ∑ f : ∀ j, ChoiceValue V (c j), uniformWeights _ f *
        ∑ z : V, uniformWeights V z *
          H (paddedMap rhs (fun j => choiceEmbed (c j) (f j)) z) := by
      simp_rw [kernelTuple_uniform_pushforward]
      exact sum_pushforwardWeight_mul _ _ _
    _ = 𝔼 fz : (∀ j, ChoiceValue V (c j)) × V,
        H (paddedMap rhs (fun j => choiceEmbed (c j) (fz.1 j)) fz.2) := by
      rw [← sum_uniformWeights_mul, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro f _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [uniformWeights_prod]
      ring
    _ = 𝔼 a : RawTuple (choiceMask c) V,
        H (paddedMap rhs (tupleDraw (choiceMask c) (choiceSlots c) a) a.1) := by
      apply Fintype.expect_equiv (choiceValuesRawTupleEquiv c)
      intro fz
      rw [tupleDraw_choiceValues]
      rfl
    _ = _ := uniform_fixed_projection_tuple rhs (choiceMask c) (choiceSlots c) H

theorem actual_projection_mixture_expectation
    (rhs : Fin k → Bool) (β : ℝ)
    (H : (ActualHomogeneous.E k →ₗ[F2] V) → ℝ) :
    (∑ dz : (Fin k → BlockDraw V) × V,
      drawWeights β k dz * H (paddedMap rhs dz.1 dz.2)) =
      ∑ c : Fin k → ProjectionChoice, choiceTupleWeight β c *
        (𝔼 Y : RawPoint (choiceMask c) →ₗ[F2] V,
          H (Y.comp (rawProjection rhs (choiceMask c) (choiceSlots c)))) := by
  rw [draw_expectation_choice_mixture]
  apply Finset.sum_congr rfl
  intro c _
  rw [fixed_choice_kernel_map_expectation]

variable [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

omit [Fintype (ActualHomogeneous.E k →ₗ[F2] V)] in
theorem paddedMapWeights_eq (rhs : Fin k → Bool) (β : ℝ)
    (X : ActualHomogeneous.E k →ₗ[F2] V) :
    paddedMapWeights rhs β X =
      paddedWeights rhs β (ActualEnumeration.toCoefficients k V X) := by
  unfold paddedMapWeights paddedWeights pushforwardWeight
  apply Finset.sum_congr rfl
  intro dz _
  have he : paddedMap rhs dz.1 dz.2 = X ↔
      ActualEnumeration.toCoefficients k V (paddedMap rhs dz.1 dz.2) =
        ActualEnumeration.toCoefficients k V X :=
    (ActualEnumeration.coefficientEquiv k V).symm.injective.eq_iff.symm
  simp only [he]
  split_ifs <;> rfl

theorem uniform_sourceMap_coordinates (a : ActualEnumeration.Coefficients k V) :
    uniformWeights (ActualHomogeneous.E k →ₗ[F2] V)
      (ActualEnumeration.coefficientEquiv k V a) =
        uniformWeights (ActualEnumeration.Coefficients k V) a := by
  simp only [uniformWeights]
  rw [Fintype.card_congr (ActualEnumeration.coefficientEquiv k V)]

theorem paddedMapWeights_totalVariation_eq_slope (rhs : Fin k → Bool) (β : ℝ) :
    MaxCutGames.Foundations.Information.totalVariation (paddedMapWeights (V := V) rhs β)
      (uniformWeights (ActualHomogeneous.E k →ₗ[F2] V)) =
        MaxCutGames.Foundations.Information.totalVariation
          (independentWeights (mixture β (singletonPairWeights V)) k)
          (uniformWeights (Fin k → V × V)) := by
  have heq : MaxCutGames.Foundations.Information.totalVariation
      (paddedMapWeights (V := V) rhs β)
      (uniformWeights (ActualHomogeneous.E k →ₗ[F2] V)) =
      MaxCutGames.Foundations.Information.totalVariation
        (paddedWeights (V := V) rhs β)
        (uniformWeights (ActualEnumeration.Coefficients k V)) := by
    unfold MaxCutGames.Foundations.Information.totalVariation
    rw [← (ActualEnumeration.coefficientEquiv k V).sum_comp]
    simp only [paddedMapWeights_eq,
      ActualEnumeration.coefficientEquiv, Equiv.coe_fn_mk,
      ActualEnumeration.to_fromCoefficients]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [show uniformWeights (ActualHomogeneous.E k →ₗ[F2] V)
      (ActualEnumeration.fromCoefficients k V a) =
        uniformWeights (ActualEnumeration.Coefficients k V) a from
          uniform_sourceMap_coordinates a]
  rw [heq]
  exact paddedWeights_totalVariation_eq_slope rhs β

end
end MaxCutGames.Decoder.PaddedLaw

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_TableKeys
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact affine-table keys for the v2 outer questions

The retained data has one entry at every original block position.  A full entry
contains the equation *occurrence ID*, a singleton entry contains the actual
variable ID, and the first component is the entire reduced affine intercept.
The common coefficient-normalization implementation below is independent of
every latent-gadget existence or inverse theorem.

The explicit binary slope cases justify its use for the v2 rank-zero, rank-one,
and rank-two rule.  In particular, the third-position pullback adds the parity
intercept twice, so exact sharing preserves the intercept as well as the slopes.
-/

namespace MaxCutGames.Decoder.TableKeys

section

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open scoped BigOperators

universe u v w

variable {Name Id R : Type} [AddCommGroup R] [Module F2 R] [DecidableEq R]
variable {k : Nat}

theorem key_shift (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (P : ActualHomogeneous.E k →ₗ[F2] R) (c : R) :
    key occ names rhs (P + ActualHomogeneous.tau.smulRight c) =
      ((key occ names rhs P).1 + c, (key occ names rhs P).2) :=
  ActualCanonical.canonical_shift occ names rhs P c

variable [DecidableEq Name] [DecidableEq Id]

/-- Every displayed singleton is its actual bit, including the affine parity
intercept in position three.  Hidden occurrence IDs are forgotten precisely
at singleton positions and retained at full positions. -/
theorem projected_key_sharing
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → PartnerProjection.Slot)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R)
    (h : RawPrivateTable.displayed J names occ slot =
      RawPrivateTable.displayed J names occ' slot') :
    key occ names rhs (Y.comp (RawPrivateTable.projection J rhs occ slot)) =
      key occ' names rhs (Y.comp (RawPrivateTable.projection J rhs occ' slot')) :=
  RawPrivateTable.canonical_same_display J names rhs occ occ' slot slot' Y h

theorem projectedKey_pullback
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ : Fin k → Id) (slot : Fin k → PartnerProjection.Slot)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R) :
    projectedKey J names rhs (RawPrivateTable.supported J names occ slot) Y =
      key occ names rhs (Y.comp (RawPrivateTable.projection J rhs occ slot)) := by
  apply projected_key_sharing
  exact RawPrivateTable.representative_display (RawPrivateTable.supported J names occ slot)

end

/-! Surjective affine-coordinate projection and uniqueness of visible tables. -/

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness

variable {Name Id R : Type} [AddCommGroup R] [Module F2 R]
variable {k : Nat}

theorem projection_preserves_homogeneous (J : Finset (Fin k)) (rhs : Id → F2)
    (occ : Fin k → Id) (slot : Fin k → PartnerProjection.Slot)
    (x : ActualHomogeneous.E k) :
    visibleTau J (RawPrivateTable.projection J rhs occ slot x) = ActualHomogeneous.tau x := by
  change ofBit (toBit x.1) = x.1
  exact ofBit_toBit _

theorem pullback_shift (J : Finset (Fin k)) (rhs : Id → F2)
    (occ : Fin k → Id) (slot : Fin k → PartnerProjection.Slot)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R) (c : R) :
    (Y + (visibleTau J).smulRight c).comp (RawPrivateTable.projection J rhs occ slot) =
      Y.comp (RawPrivateTable.projection J rhs occ slot) +
        ActualHomogeneous.tau.smulRight c := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
    projection_preserves_homogeneous]

variable [DecidableEq Name] [DecidableEq Id] [DecidableEq R]

omit [DecidableEq Name] [DecidableEq Id] in
/-- Constant translation commutes with exact sharing at the level of whole
reduced keys, including the removed alphabet component of the intercept. -/
theorem projectedKey_shift (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (Q : RawPrivateTable.SupportedV J names)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R) (c : R) :
    projectedKey J names rhs Q (Y + (visibleTau J).smulRight c) =
      ((projectedKey J names rhs Q Y).1 + c, (projectedKey J names rhs Q Y).2) := by
  unfold projectedKey
  rw [pullback_shift, key_shift]

end MaxCutGames.Decoder.TableKeys

/-!
The concrete observation maps of the v2 projected-advice experiment.

The full hidden draw contains the equation occurrence IDs, singleton positions,
projection choices, public row map, and the two sampled tables. The observations
are precisely `(U,A,Tπ,AMπ)` and `(O,A,T,AM)`. The hidden matrix is absent from
both observation types. Changing its kernel-valued part preserves both inputs
and hence every deterministic witness or strategy chosen from those inputs.
-/

namespace MaxCutGames.Decoder.AdviceExperiment

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness

noncomputable section

variable (k : Nat) (Id K W R : Type)
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup W] [Module F2 W]
variable [AddCommGroup R] [Module F2 R]

variable {k Id K W R}

variable {Name : Type} (names : Id → Fin 3 → Name)

variable (rhs : Id → F2)

theorem right_rows_attainable (d : Draw k Id K W R) :
    ∃ M : RawPartnerTarget.RawPoint d.singletons →ₗ[F2] K,
      d.rowMap.comp M = (rightObservation names d).2.rows :=
  ⟨d.hiddenMatrix, rfl⟩

end
end MaxCutGames.Decoder.AdviceExperiment

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_AdviceLaw
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The actual finite advice law. Uniform independent hidden/complement maps induce
the exact uniform visible-map law, including for rank-deficient public maps.
The whole-table comparison retains an arbitrary common occurrence/public-data
law, so weighted occurrence sampling is not replaced by uniform IDs.
-/

namespace MaxCutGames.Decoder.AdviceLaw

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Soundness
open ConditionalIncidences RawPartnerTarget RawMapLaw
open MaxCutGames.Foundations.Games
open MaxCutGames.Clean

noncomputable section
attribute [local instance] Classical.propDecidable

section WholeTable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]
  [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

/-- Padding adds an independent uniform affine intercept. The full map's
variation is therefore exactly the sparse slope variation used in constants. -/
theorem paddedDistribution_totalVariation_eq_slope (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (paddedDistribution (V := V) rhs β hβ hβ').totalVariation
      (FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V)) =
        MaxCutGames.Foundations.Information.totalVariation
          (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
          (SparseLaw.uniformWeights (Fin k → V × V)) := by
  exact PaddedLaw.paddedMapWeights_totalVariation_eq_slope rhs β

end WholeTable

section CommonLaw

variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

theorem withKernel_totalVariation (μ : FiniteDistribution Ω)
    (p q : Ω → FiniteDistribution Y) :
    (withKernel μ p).totalVariation (withKernel μ q) =
      ∑ x, μ.weight x * (p x).totalVariation (q x) := by
  unfold FiniteDistribution.totalVariation withKernel
  rw [Fintype.sum_prod_type]
  have inner (x : Ω) :
      (∑ y, |μ.weight x * (p x).weight y - μ.weight x * (q x).weight y|) =
        μ.weight x * ∑ y, |(p x).weight y - (q x).weight y| := by
    simp only [← mul_sub, abs_mul, abs_of_nonneg (μ.nonnegative x), ← Finset.mul_sum]
  simp_rw [inner]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

end CommonLaw

/-- Common occurrence/public randomness preserves the exact slope variation. -/
theorem wholeAdvice_totalVariation_eq_slope {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (withKernel (occurrences.product publicLaw)
      (fun ua => paddedDistribution (V := V) (fun j => rhs (ua.1 j)) β hβ hβ')).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) =
      MaxCutGames.Foundations.Information.totalVariation
        (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
        (SparseLaw.uniformWeights (Fin k → V × V)) := by
  rw [withKernel_totalVariation]
  simp_rw [paddedDistribution_totalVariation_eq_slope]
  rw [← Finset.sum_mul, (occurrences.product publicLaw).normalized, one_mul]

section ProjectionSeeds

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]

variable [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

theorem projectionSeed_expectation (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (H : (ActualHomogeneous.E k →ₗ[F2] V) → ℝ) :
    (projectionSeedDistribution β hβ hβ').expectation (fun s => H (projectSeedMap rhs s)) =
      (paddedDistribution rhs β hβ hβ').expectation H := by
  rw [paddedDistribution, FiniteDistribution.expectation_pushforward]
  change (∑ s : ProjectionSeed k V,
      PaddedLaw.choiceTupleWeight β s.1 * SparseLaw.uniformWeights _ s.2 *
        H (projectSeedMap rhs s)) =
    ∑ dz, PaddedLaw.drawWeights β k dz * H (PaddedLaw.paddedMap rhs dz.1 dz.2)
  rw [PaddedLaw.actual_projection_mixture_expectation, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  calc
    _ = PaddedLaw.choiceTupleWeight β c *
        ∑ Y : RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] V,
          SparseLaw.uniformWeights _ Y *
            H (Y.comp (rawProjection rhs (PaddedLaw.choiceMask c) (PaddedLaw.choiceSlots c))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y _
      exact mul_assoc _ _ _
    _ = _ := by rw [PaddedLaw.sum_uniformWeights_mul]

theorem projectionSeed_pushforward (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (projectionSeedDistribution β hβ hβ').pushforward (projectSeedMap (V := V) rhs) =
      paddedDistribution rhs β hβ hβ' := by
  apply FiniteDistribution.eq_of_weight_eq
  intro Y
  have h := projectionSeed_expectation rhs β hβ hβ' (fun X => if X = Y then 1 else 0)
  simpa [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite,
    PaddedLaw.pushforwardWeight] using h

end ProjectionSeeds

section FullSeedLaw

variable {Ω Z Y : Type*} [Fintype Ω] [Fintype Z] [Fintype Y]

theorem product_pushforward_withKernel (μ : FiniteDistribution Ω)
    (ν : FiniteDistribution Z) (f : Ω → Z → Y) :
    (μ.product ν).pushforward (fun xz => (xz.1, f xz.1 xz.2)) =
      withKernel μ (fun x => ν.pushforward (f x)) := by
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨a, b⟩
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product, withKernel]
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x : Ω, if x = a then μ.weight x *
        ∑ z, if f x z = b then ν.weight z else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = a
      · subst x
        simp only [Prod.mk.injEq, true_and, ite_true, if_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        split_ifs <;> simp
      · simp [Prod.mk.injEq, hx]
    _ = _ := by simp

end FullSeedLaw

theorem fullSeed_pad_law {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (fullSeedLaw (V := V) occurrences publicLaw β hβ hβ').pushforward (fullSeedPad rhs) =
      withKernel (occurrences.product publicLaw)
        (fun ua => paddedDistribution (V := V) (fun j => rhs (ua.1 j)) β hβ hβ') := by
  unfold fullSeedLaw fullSeedPad
  rw [product_pushforward_withKernel (occurrences.product publicLaw)
    (projectionSeedDistribution (k := k) (V := V) β hβ hβ')
    (fun ua seed => projectSeedMap (fun j => rhs (ua.1 j)) seed)]
  congr 1
  funext ua
  exact projectionSeed_pushforward (fun j => rhs (ua.1 j)) β hβ hβ'

theorem fullSeed_totalVariation_eq_slope {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((fullSeedLaw (V := V) occurrences publicLaw β hβ hβ').pushforward
      (fullSeedPad rhs)).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) =
      MaxCutGames.Foundations.Information.totalVariation
        (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
        (SparseLaw.uniformWeights (Fin k → V × V)) := by
  rw [fullSeed_pad_law]
  exact wholeAdvice_totalVariation_eq_slope occurrences publicLaw rhs β hβ hβ'

theorem fullSeed_totalVariation_le_slope {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((fullSeedLaw (V := V) occurrences publicLaw β hβ hβ').pushforward
      (fullSeedPad rhs)).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) ≤
      MaxCutGames.Foundations.Information.totalVariation
        (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
        (SparseLaw.uniformWeights (Fin k → V × V)) :=
  (fullSeed_totalVariation_eq_slope occurrences publicLaw rhs β hβ hβ').le

variable {k : ℕ} {Id K W R : Type}
  [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
  [AddCommGroup R] [Module F2 R]

theorem completeDraw_seed (d : CompleteData k Id K W R) (N : PrivateMap d) :
    seedToActualDraw (completeAssemble d N).1.1 (completeAssemble d N).1.2
      (completeAssemble d N).2 = completeDraw d N := rfl

variable [Fintype Id] [Fintype K] [Fintype W] [Fintype R] [Fintype (K →ₗ[F2] R)]

omit [Fintype R] in
/-- The actual law has exactly constant point weights on every fiber of all
observed data, even for arbitrary occurrence and public-map laws. -/
theorem fullSeed_weight_observed (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R)) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) (s : FullSeed k Id K W R) :
    (fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').weight s =
      completeWeight occurrences publicLaw β (completeObserve s) := rfl

omit [Fintype R] in
theorem fullSeed_weight_fiber (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R)) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) (d : CompleteData k Id K W R)
    (s : FullSeed k Id K W R) (hs : completeObserve s = d) :
    (fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').weight s =
      completeWeight occurrences publicLaw β d := by
  rw [fullSeed_weight_observed, hs]

end
end MaxCutGames.Decoder.AdviceLaw

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixCharacters
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace characters on actual finite binary matrix spaces. -/

noncomputable section

namespace MaxCutGames.Fourier.MatrixCharacters

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear

section LinearFunctionals

variable {E : Type*} [AddCommGroup E] [Module F2 E]

theorem linearFunctionalCharacter_injective :
    Function.Injective (linearFunctionalCharacter (E := E)) := by
  intro φ ψ h
  ext x
  apply binarySign_injective
  exact congrArg (fun χ : AddChar E ℂ => χ x) h

theorem linearFunctionalCharacter_eq_zero_iff (φ : E →ₗ[F2] F2) :
    linearFunctionalCharacter φ = 0 ↔ φ = 0 := by
  rw [← linearFunctionalCharacter_zero, linearFunctionalCharacter_injective.eq_iff]

theorem sum_linearFunctionalCharacter [Fintype E] (φ : E →ₗ[F2] F2) :
    ∑ x, linearFunctionalCharacter φ x =
      if φ = 0 then (Fintype.card E : ℂ) else 0 := by
  rw [AddChar.sum_eq_ite]
  simp only [linearFunctionalCharacter_eq_zero_iff]

theorem expect_linearFunctionalCharacter [Fintype E] (φ : E →ₗ[F2] F2) :
    (𝔼 x, linearFunctionalCharacter φ x) = if φ = 0 then 1 else 0 := by
  rw [Fintype.expect_eq_sum_div_card, sum_linearFunctionalCharacter]
  split_ifs <;> simp [Fintype.card_ne_zero]

end LinearFunctionals

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem linearTracePair_add_right (X : E →ₗ[F2] F) (S T : F →ₗ[F2] E) :
    linearTracePair X (S + T) = linearTracePair X S + linearTracePair X T := by
  simp [linearTracePair, LinearMap.comp_add]

theorem linearTraceCharacter_add (S T : F →ₗ[F2] E) :
    linearTraceCharacter (S + T) = linearTraceCharacter S + linearTraceCharacter T := by
  ext X
  simp only [linearTraceCharacter_apply, linearTracePair_add_right, binarySign_add,
    AddChar.add_apply]

end MaxCutGames.Fourier.MatrixCharacters
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixFourier
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace MaxCutGames.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open MaxCutGames.Fourier.MatrixCharacters

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem linear_fourier_inversion (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re = f X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          fourierCoeff (fun Y => (f Y : ℂ)) (linearTraceCharacter S) *
            linearTraceCharacter S X := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E,
        linearCoeff f S * (linearTraceCharacter S X).re) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      change ((linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) = _
      rw [Complex.ofReal_mul, linearCoeff_complex, linearTraceCharacter_real]
    _ = (f X : ℂ) := linear_complex_inversion _ X

end MaxCutGames.Fourier.MatrixFourier
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_MatrixParity
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual binary matrix and linear-map parity used in Lemma 5.3. -/

noncomputable section

namespace MaxCutGames.Fourier.MatrixParity

open MaxCutGames.Integration.BinaryLinear
open scoped Matrix BigOperators Classical

section LinearMaps

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

/-- Generic trace pairing of a rank-one color shift. -/
theorem trace_smulRight_comp [FiniteDimensional F2 C]
    (τ : E →ₗ[F2] F2) (c : C) (S : C →ₗ[F2] E) :
    LinearMap.trace F2 C ((τ.smulRight c).comp S) = τ (S c) := by
  have heq : (τ.smulRight c).comp S = (τ.comp S).smulRight c := by
    ext x
    rfl
  rw [heq, LinearMap.trace_smulRight, LinearMap.comp_apply]

/-- The exact number of binary linear maps, supplying the count in (5.20).
Taking `E` to be the subspace `W` counts precisely maps whose image lies in `W`. -/
theorem card_linearMaps [FiniteDimensional F2 E] [FiniteDimensional F2 C]
    [Fintype (C →ₗ[F2] E)] :
    Fintype.card (C →ₗ[F2] E) =
      2 ^ (Module.finrank F2 C * Module.finrank F2 E) := by
  classical
  let bC := Module.finBasis F2 C
  let bE := Module.finBasis F2 E
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (LinearMap.toMatrix bC bE).toEquiv]
  change Nat.card (Fin (Module.finrank F2 E) → Fin (Module.finrank F2 C) → F2) = _
  rw [Nat.card_fun, Nat.card_fun]
  simp [F2, Integration.BinaryLinear.F2, Nat.card_eq_fintype_card, ← pow_mul,
    Nat.mul_comm]

end LinearMaps

open MatrixCharacters hiding F2

end MaxCutGames.Fourier.MatrixParity
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixNoise
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rank-one averaging operator on finite binary matrix spaces.
The outer weights describe any finite law for `v`; the functional `ℓ` is
uniform. Normalization is needed for eigenvalue bounds, not diagonalization. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace MaxCutGames.Fourier.MatrixNoise

open scoped BigOperators Matrix
open MaxCutGames.Integration.BinaryLinear (Vector)
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem evaluationCharacter_eq_zero_iff (w : E) :
    evaluationCharacter w = 0 ↔ w = 0 := by
  constructor
  · intro h
    apply (Module.forall_dual_apply_eq_zero_iff F2 w).mp
    intro ℓ
    apply binarySign_injective
    have hx := congrArg (fun ψ : AddChar (E →ₗ[F2] F2) ℂ => ψ ℓ) h
    simpa using hx
  · rintro rfl
    ext ℓ
    simp

theorem average_evaluationCharacter [Fintype (E →ₗ[F2] F2)] (w : E) :
    (𝔼 ℓ : E →ₗ[F2] F2, binarySign (ℓ w)) =
      if w = 0 then (1 : ℂ) else 0 := by
  classical
  change (𝔼 ℓ, evaluationCharacter w ℓ) = _
  rw [Fintype.expect_eq_sum_div_card, AddChar.sum_eq_ite]
  simp only [evaluationCharacter_eq_zero_iff]
  split_ifs <;> simp

end MaxCutGames.Fourier.MatrixNoise
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_MatrixParityRow
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier expansion of actual affine restrictions and parity extraction. -/

noncomputable section

namespace MaxCutGames.Fourier.MatrixParityRow

open MatrixCharacters MatrixFourier MatrixParity
open scoped BigOperators Classical

variable {E C V : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C] [AddCommGroup V] [Module F2 V]
  [FiniteDimensional F2 E] [FiniteDimensional F2 C] [FiniteDimensional F2 V]
  [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] [Fintype (V →ₗ[F2] C)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 C] [FiniteDimensional F2 V] [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] [Fintype (V →ₗ[F2] C)] in
theorem traceCharacter_comp (Q : E →ₗ[F2] V) (A : V →ₗ[F2] C)
    (T : C →ₗ[F2] E) :
    linearTraceCharacter T (A.comp Q) = linearTraceCharacter (Q.comp T) A := by
  simp only [linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 C] [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] in
theorem traceCharacter_re_add (T : C →ₗ[F2] E) (X Y : E →ₗ[F2] C) :
    (linearTraceCharacter T (X + Y)).re =
      (linearTraceCharacter T X).re * (linearTraceCharacter T Y).re := by
  rw [AddChar.map_add_eq_mul, Complex.mul_re]
  simp [linearTraceCharacter_apply, binarySign_im]

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] in
/-- Characters restricted to the row vanish unless the dual map lands in the
kernel of `Q`. For `Q = W.mkQ` this is precisely `range T ≤ W`. -/
theorem row_character_average (Q : E →ₗ[F2] V) (T : C →ₗ[F2] E) :
    (𝔼 A : V →ₗ[F2] C, (linearTraceCharacter T (A.comp Q)).re) =
      if Q.comp T = 0 then 1 else 0 := by
  have hcomplex : (𝔼 A : V →ₗ[F2] C,
      linearTraceCharacter T (A.comp Q)) = if Q.comp T = 0 then 1 else 0 := by
    simp only [traceCharacter_comp, Fintype.expect_eq_sum_div_card,
      sum_linearTraceCharacter]
    split <;> simp [Fintype.card_ne_zero]
  have h := congrArg Complex.re hcomplex
  simpa only [Complex.re_expect, apply_ite, Complex.one_re, Complex.zero_re] using h

end MaxCutGames.Fourier.MatrixParityRow
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_PrivateFourier
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Decoder.PrivateFourier

open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixParity
open MaxCutGames.Fourier.MatrixParityRow
open scoped BigOperators Classical

section Signs

theorem sign_add (a b : F2) : sign (a + b) = sign a * sign b := by
  simp [sign, binarySign_add, Complex.mul_re]

theorem sign_add_one (a : F2) : sign (a + 1) = -sign a := by
  rw [sign_add, sign_one]
  ring

end Signs

section CharacterAverages

variable {H K : Type*} [AddCommGroup H] [Module F2 H]
    [AddCommGroup K] [Module F2 K]

theorem binary_neg_eq_self (x : K) : -x = x := by
  have htwo : (1 + 1 : F2) = 0 := by decide
  have hh := congrArg (fun a : F2 => a • x) htwo
  exact neg_eq_iff_add_eq_zero.mpr
    (by simpa only [add_smul, one_smul, zero_smul] using hh)

theorem binary_add_eq_zero_iff (x y : K) : x + y = 0 ↔ x = y := by
  rw [add_eq_zero_iff_eq_neg, binary_neg_eq_self]

theorem average_sign_dual [Fintype (K →ₗ[F2] F2)] (x : K) :
    (𝔼 σ : K →ₗ[F2] F2, sign (σ x)) = if x = 0 then 1 else 0 := by
  have h := congrArg Complex.re
    (MaxCutGames.Fourier.MatrixNoise.average_evaluationCharacter x)
  simpa only [Complex.re_expect, apply_ite, Complex.one_re, Complex.zero_re, sign] using h

theorem average_sign_primal [Fintype H] (σ : H →ₗ[F2] F2) :
    (𝔼 h : H, sign (σ h)) = if σ = 0 then 1 else 0 := by
  have h := congrArg Complex.re (expect_linearFunctionalCharacter σ)
  simpa only [Complex.re_expect, apply_ite, Complex.one_re, Complex.zero_re,
    linearFunctionalCharacter_apply, sign] using h

/-- Exact character expansion of equality in the actual output space. -/
theorem average_sign_equality [Fintype (K →ₗ[F2] F2)] (x y : K) :
    (𝔼 σ : K →ₗ[F2] F2, sign (σ x) * sign (σ y)) =
      if x = y then 1 else 0 := by
  simp_rw [← sign_add, ← map_add]
  rw [average_sign_dual, binary_add_eq_zero_iff]

/-- The ambient uniform character has trivial restriction to `H` with exactly
the reciprocal cardinality of `H`.  No conditioning on the private character
is substituted for the real experiment. -/
theorem trivial_restriction_probability [Fintype H] [Fintype (K →ₗ[F2] F2)]
    (ι : H →ₗ[F2] K) (hι : Function.Injective ι) :
    (𝔼 σ : K →ₗ[F2] F2, if σ.comp ι = 0 then (1 : ℝ) else 0) =
      1 / (Fintype.card H : ℝ) := by
  calc
    _ = 𝔼 σ : K →ₗ[F2] F2, 𝔼 h : H, sign (σ (ι h)) := by
      apply Finset.expect_congr rfl
      intro σ _
      exact (average_sign_primal (σ.comp ι)).symm
    _ = 𝔼 h : H, 𝔼 σ : K →ₗ[F2] F2, sign (σ (ι h)) :=
      Finset.expect_comm _ _ _
    _ = 𝔼 h : H, if h = 0 then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro h _
      rw [average_sign_dual]
      have heq : ι h = 0 ↔ h = 0 := by
        rw [← map_zero ι]
        exact hι.eq_iff
      rw [heq]
    _ = _ := by simp []

end CharacterAverages

section ActualFourier

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
theorem tableSign_antifold (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2) (σ : K →ₗ[F2] F2) (h : H)
    (folded : ∀ N, F (N + τ.smulRight h) = F N + ι h)
    (hσ : σ (ι h) = 1) :
    ∀ N, tableSign F σ (N + τ.smulRight h) = -tableSign F σ N := by
  intro N
  simp only [tableSign, folded, map_add, hσ, sign_add_one]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [Fintype (H →ₗ[F2] E)] in
/-- Translation of the input multiplies a coefficient by its character. -/
theorem linearCoeff_translate (f : (E →ₗ[F2] H) → ℝ)
    (D : E →ₗ[F2] H) (Φ : H →ₗ[F2] E) :
    linearCoeff (fun N => f (N + D)) Φ =
      linearCoeff f Φ * (linearTraceCharacter Φ D).re := by
  have hself : D + D = 0 :=
    (linearMap_add_eq_zero_iff D D).2 rfl
  have hchange := Fintype.expect_equiv (Equiv.addRight D)
    (fun N => f (N + D) * (linearTraceCharacter Φ N).re)
    (fun N => f N * (linearTraceCharacter Φ (N + D)).re)
    (fun N => by simp only [Equiv.coe_addRight, add_assoc, hself, add_zero])
  unfold linearCoeff
  rw [hchange]
  simp only [traceCharacter_re_add, ← mul_assoc]
  exact (Finset.expect_mul _ _ _).symm

omit [FiniteDimensional F2 E] [Fintype (H →ₗ[F2] E)] in
/-- Anti-folding forces every positive-mass frequency to return first bit one. -/
theorem positive_frequency_first_bit (f : (E →ₗ[F2] H) → ℝ)
    (τ : E →ₗ[F2] F2) (h : H) (Φ : H →ₗ[F2] E)
    (folded : ∀ N, f (N + τ.smulRight h) = -f N)
    (positive : 0 < frequencyWeight f Φ) : τ (Φ h) = 1 := by
  have hcoeff : linearCoeff f Φ ≠ 0 := by
    intro hz
    simp [frequencyWeight, hz] at positive
  have heq := linearCoeff_translate f (τ.smulRight h) Φ
  have hneg : linearCoeff (fun N => f (N + τ.smulRight h)) Φ =
      -linearCoeff f Φ := by
    simp only [linearCoeff, folded, neg_mul]
    simp [Fintype.expect_eq_sum_div_card]
  rw [hneg] at heq
  have hchar : (linearTraceCharacter Φ (τ.smulRight h)).re = sign (τ (Φ h)) := by
    simp only [linearTraceCharacter_apply, linearTracePair, trace_smulRight_comp, sign]
  rw [hchar] at heq
  rcases Integration.BinaryLinear.scalar_cases (τ (Φ h)) with hz | hone
  · rw [hz, sign_zero, mul_one] at heq
    exact False.elim (hcoeff (by linarith))
  · exact hone

end ActualFourier

section AffineSlice

variable {E H V : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup V] [Module F2 V]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (V →ₗ[F2] H)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
theorem traceCharacter_re_mul (Φ θ : H →ₗ[F2] E) (N : E →ₗ[F2] H) :
    (linearTraceCharacter Φ N).re * (linearTraceCharacter θ N).re =
      (linearTraceCharacter (Φ + θ) N).re := by
  rw [linearTraceCharacter_add, AddChar.add_apply, Complex.mul_re]
  simp [linearTraceCharacter_apply]

/-- The exact Fourier coset expansion of the affine conditional correlation. -/
theorem sliceCorrelation_eq_coset (q : E →ₗ[F2] V) (N₀ : E →ₗ[F2] H)
    (f : (E →ₗ[F2] H) → ℝ) (θ : H →ₗ[F2] E) :
    sliceCorrelation q N₀ f θ =
      ∑ Φ ∈ frequencyCoset q θ,
        linearCoeff f Φ * (linearTraceCharacter (Φ + θ) N₀).re := by
  unfold sliceCorrelation
  calc
    _ = 𝔼 A : V →ₗ[F2] H, ∑ Φ : H →ₗ[F2] E,
        linearCoeff f Φ * (linearTraceCharacter (Φ + θ) (N₀ + A.comp q)).re := by
      apply Finset.expect_congr rfl
      intro A _
      rw [← linear_fourier_inversion f (N₀ + A.comp q), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Φ _
      rw [mul_assoc, traceCharacter_re_mul]
    _ = ∑ Φ : H →ₗ[F2] E, if q.comp (Φ + θ) = 0 then
        linearCoeff f Φ * (linearTraceCharacter (Φ + θ) N₀).re else 0 := by
      rw [Finset.expect_sum_comm]
      apply Finset.sum_congr rfl
      intro Φ _
      simp only [traceCharacter_re_add, ← mul_assoc]
      rw [← Finset.mul_expect, row_character_average]
      split <;> simp
    _ = _ := by simp [frequencyCoset, Finset.sum_filter]

/-- Cauchy--Schwarz bounds an affine correlation by the actual Fourier mass
in its target coset; no spectral mass is assumed. -/
theorem sliceCorrelation_sq_le_coset_mass (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (f : (E →ₗ[F2] H) → ℝ) (θ : H →ₗ[F2] E) :
    sliceCorrelation q N₀ f θ ^ 2 ≤
      (frequencyCoset q θ).card *
        ∑ Φ ∈ frequencyCoset q θ, frequencyWeight f Φ := by
  rw [sliceCorrelation_eq_coset]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (frequencyCoset q θ)
    (linearCoeff f) (fun Φ => (linearTraceCharacter (Φ + θ) N₀).re)
  have hs : ∀ Φ : H →ₗ[F2] E,
      (linearTraceCharacter (Φ + θ) N₀).re ^ 2 = 1 := by
    intro Φ
    exact sign_sq _
  simpa only [hs, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul,
    frequencyWeight, mul_comm] using hcs

end AffineSlice

section AffineEquality

variable {E H K V : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K] [AddCommGroup V] [Module F2 V]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (V →ₗ[F2] H)] [Fintype (K →ₗ[F2] F2)]

omit [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
/-- The pure-tensor target character is literally evaluation at `z`. -/
theorem target_character (σ : H →ₗ[F2] F2) (z : E) (N : E →ₗ[F2] H) :
    (linearTraceCharacter (σ.smulRight z) N).re = sign (σ (N z)) := by
  simp only [linearTraceCharacter_apply, sign]
  congr 2
  rw [linearTracePair_swap]
  exact trace_smulRight_comp σ z N

omit [FiniteDimensional F2 V] in
omit [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
/-- Affine target equality expands into the correlations with the intercept
phase `sign (σ b)`.  In the projected experiment `b = M₀ z + u`. -/
theorem affine_equality_character_expansion (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (z : E) (b : K) :
    (𝔼 A : V →ₗ[F2] H,
      if F (N₀ + A.comp q) = b + ι ((N₀ + A.comp q) z) then (1 : ℝ) else 0) =
      𝔼 σ : K →ₗ[F2] F2, sign (σ b) *
        sliceCorrelation q N₀ (tableSign F σ) ((σ.comp ι).smulRight z) := by
  calc
    _ = 𝔼 A : V →ₗ[F2] H, 𝔼 σ : K →ₗ[F2] F2,
        sign (σ (F (N₀ + A.comp q))) *
          sign (σ (b + ι ((N₀ + A.comp q) z))) := by
      apply Finset.expect_congr rfl
      intro A _
      exact (average_sign_equality _ _).symm
    _ = 𝔼 σ : K →ₗ[F2] F2, 𝔼 A : V →ₗ[F2] H,
        sign (σ (F (N₀ + A.comp q))) *
          sign (σ (b + ι ((N₀ + A.comp q) z))) := Finset.expect_comm _ _ _
    _ = _ := by
      apply Finset.expect_congr rfl
      intro σ _
      unfold sliceCorrelation
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro A _
      simp only [map_add, sign_add, target_character, tableSign, LinearMap.comp_apply]
      ring

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V] [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] [Fintype (K →ₗ[F2] F2)] in
/-- Every slice correlation has absolute value at most one. -/
theorem sliceCorrelation_tableSign_abs_le_one (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (σ : K →ₗ[F2] F2) (θ : H →ₗ[F2] E) :
    |sliceCorrelation q N₀ (tableSign F σ) θ| ≤ 1 := by
  unfold sliceCorrelation
  calc
    _ ≤ 𝔼 A : V →ₗ[F2] H,
        |tableSign F σ (N₀ + A.comp q) *
          (linearTraceCharacter θ (N₀ + A.comp q)).re| := Finset.abs_expect_le _ _
    _ = 1 := by
      have hp (N : E →ₗ[F2] H) : |(linearTraceCharacter θ N).re| = 1 := sign_abs _
      simp only [abs_mul, tableSign, sign_abs, hp, mul_one]
      exact Fintype.expect_const 1

omit [FiniteDimensional F2 V] in
omit [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
/-- Dropping the unit intercept phase can only increase the average absolute
correlation; the hypothesis is the actual affine-slice agreement probability. -/
theorem agreement_le_average_abs_correlation (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (z : E) (b : K) :
    (𝔼 A : V →ₗ[F2] H,
      if F (N₀ + A.comp q) = b + ι ((N₀ + A.comp q) z) then (1 : ℝ) else 0) ≤
      𝔼 σ : K →ₗ[F2] F2,
        |sliceCorrelation q N₀ (tableSign F σ) ((σ.comp ι).smulRight z)| := by
  rw [affine_equality_character_expansion]
  apply Finset.expect_le_expect
  intro σ _
  calc
    _ ≤ |sign (σ b) *
        sliceCorrelation q N₀ (tableSign F σ) ((σ.comp ι).smulRight z)| := le_abs_self _
    _ = _ := by rw [abs_mul, sign_abs, one_mul]

end AffineEquality

section CosetCardinality

variable {E H : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (H →ₗ[F2] E)]

/-- The exact number of frequencies in the affine coset.  Translation does not
alter the annihilator cardinality, including when the target is nonzero. -/
theorem frequencyCoset_card (Q : Submodule F2 E) [Fintype (H →ₗ[F2] Q)]
    (θ : H →ₗ[F2] E) :
    (frequencyCoset Q.mkQ θ).card =
      2 ^ (Module.finrank F2 H * Module.finrank F2 Q) := by
  classical
  rw [frequencyCoset, ← Fintype.card_subtype]
  calc
    Fintype.card {Φ : H →ₗ[F2] E // Q.mkQ.comp (Φ + θ) = 0} =
        Fintype.card {Φ : H →ₗ[F2] E // Q.mkQ.comp Φ = 0} :=
      Fintype.card_congr (Equiv.subtypeEquiv (Equiv.addRight θ) (fun _ => Iff.rfl))
    _ = Fintype.card (H →ₗ[F2] Q) :=
      MaxCutGames.Fourier.MatrixRestrictions.quotientKernel_card Q
    _ = _ := card_linearMaps

theorem frequencyCoset_card_le (Q : Submodule F2 E) [Fintype (H →ₗ[F2] Q)]
    (θ : H →ₗ[F2] E) (ℓ r : ℕ)
    (hH : Module.finrank F2 H ≤ ℓ) (hQ : Module.finrank F2 Q ≤ r) :
    (frequencyCoset Q.mkQ θ).card ≤ 2 ^ (ℓ * r) := by
  rw [frequencyCoset_card]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul hH hQ)

end CosetCardinality

section Averaging

variable {SigmaChar : Type*} [Fintype SigmaChar] [Nonempty SigmaChar]

omit [Nonempty SigmaChar] in
/-- Discarding a set of characters costs at most its actual uniform mass. -/
theorem remove_bad_characters (C : SigmaChar → ℝ) (good : SigmaChar → Prop)
    (a b : ℝ) (hC : ∀ σ, |C σ| ≤ 1)
    (hcorrelation : a ≤ 𝔼 σ, |C σ|)
    (hbad : (𝔼 σ, if good σ then (0 : ℝ) else 1) ≤ b) :
    a - b ≤ 𝔼 σ, if good σ then |C σ| else 0 := by
  classical
  have hp : (𝔼 σ, |C σ|) ≤
      (𝔼 σ, if good σ then |C σ| else 0) +
      (𝔼 σ, if good σ then (0 : ℝ) else 1) := by
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_le_expect
    intro σ _
    by_cases hg : good σ
    · simp [hg]
    · simpa [hg] using hC σ
  linarith

/-- The second Cauchy--Schwarz step in private decoding.  The first step is
`sliceCorrelation_sq_le_coset_mass`; the mass is the actual sampled Fourier
mass and `good` selects nontrivial output characters. -/
theorem average_coset_mass_lower (C mass : SigmaChar → ℝ) (good : SigmaChar → Prop)
    (N c : ℝ) (hN : 0 < N) (hc : 0 ≤ c)
    (hcorrelation : c ≤ 𝔼 σ, if good σ then |C σ| else 0)
    (hpoint : ∀ σ, good σ → C σ ^ 2 ≤ N * mass σ) :
    c ^ 2 / N ≤ 𝔼 σ, if good σ then mass σ else 0 := by
  classical
  let d : SigmaChar → ℝ := fun σ => if good σ then |C σ| else 0
  have hj := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ d (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Fintype.expect_const] at hj
  have hp : (𝔼 σ, d σ ^ 2) ≤ N * (𝔼 σ, if good σ then mass σ else 0) := by
    rw [Finset.mul_expect]
    apply Finset.expect_le_expect
    intro σ _
    by_cases hg : good σ
    · simpa [d, hg, sq_abs] using hpoint σ hg
    · simp [d, hg]
  have hs : c ^ 2 ≤ (𝔼 σ, d σ) ^ 2 := by
    have hd : c ≤ 𝔼 σ, d σ := hcorrelation
    nlinarith
  apply (div_le_iff₀ hN).2
  nlinarith

end Averaging

section Contraction

variable {E H : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup H] [Module F2 H]

/-- A frequency in the target coset contracts into `z + Q`. -/
theorem contraction_mem_target_coset (Q : Submodule F2 E)
    (σ : H →ₗ[F2] F2) (z : E) (Φ : H →ₗ[F2] E) (h : H)
    (hσ : σ h = 1) (hcoset : Q.mkQ.comp (Φ + σ.smulRight z) = 0) :
    Φ h - z ∈ Q := by
  have hq := LinearMap.congr_fun hcoset h
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
    hσ, one_smul, LinearMap.zero_apply] at hq
  have hmem : Φ h + z ∈ Q := by
    change Q.mkQ (Φ h + z) = 0 at hq
    exact (Submodule.Quotient.mk_eq_zero Q).mp hq
  have hz : -z = z := by
    have htwo : (1 + 1 : F2) = 0 := by decide
    have hzz : z + z = 0 := by
      have hh := congrArg (fun a : F2 => a • z) htwo
      simpa only [add_smul, one_smul, zero_smul] using hh
    exact neg_eq_iff_add_eq_zero.mpr hzz
  simpa only [sub_eq_add_neg, hz] using hmem

end Contraction

variable {U O Ω : Type*} [Fintype Ω]

/-- If the returned projected answer has a preimage in the candidate set, the
uniform, independently sampled candidate finds a preimage with this probability. -/
theorem uniform_preimage_probability (s : Finset U) (π : U → O) (b : O)
    (preimage : ∃ u ∈ s, π u = b) :
    1 / (s.card : ℝ) ≤ 𝔼 u ∈ s, if π u = b then (1 : ℝ) else 0 := by
  classical
  obtain ⟨u, hu, hπ⟩ := preimage
  have hsum : (1 : ℝ) ≤ ∑ v ∈ s, if π v = b then (1 : ℝ) else 0 := by
    have hnonneg : ∀ v ∈ s, (0 : ℝ) ≤ if π v = b then 1 else 0 := by
      intro v _
      split <;> norm_num
    have h := Finset.single_le_sum hnonneg hu
    simpa only [hπ, ite_true, if_true] using h
  rw [Finset.expect_eq_sum_div_card]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

/-- An explicit product sampling law: the left strategy samples uniformly from
`s`, independently of the right strategy's private sample.  Only positive-mass
good samples need a preimage; no private Fourier information is passed left. -/
theorem independent_agreement_lower (s : Finset U) (π : U → O)
    (answer : Ω → O) (weight : Ω → ℝ) (good : Ω → Prop)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (preimage : ∀ ω, good ω → 0 < weight ω → ∃ u ∈ s, π u = answer ω) :
    (∑ ω, if good ω then weight ω else 0) / (s.card : ℝ) ≤
      ∑ ω, weight ω * (𝔼 u ∈ s, if π u = answer ω then (1 : ℝ) else 0) := by
  classical
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro ω _
  have havg : 0 ≤ 𝔼 u ∈ s, if π u = answer ω then (1 : ℝ) else 0 :=
    Finset.expect_nonneg fun _ _ => by positivity
  by_cases hg : good ω
  · simp only [hg, ite_true, if_true]
    by_cases hw : 0 < weight ω
    · have hb := uniform_preimage_probability s π (answer ω) (preimage ω hg hw)
      have := mul_le_mul_of_nonneg_left hb (hweight ω)
      simpa only [div_eq_mul_inv, one_mul] using this
    · have hz : weight ω = 0 := le_antisymm (le_of_not_gt hw) (hweight ω)
      simp [hz]
  · simp only [hg, ite_false, zero_div]
    exact mul_nonneg (hweight ω) havg

end MaxCutGames.Decoder.PrivateFourier

/-!
# Actual private response laws for v2 Fourier decoding

The right response law has only its row-fiber table, the inclusion of its hidden
kernel, a first-bit map, and an actual fallback answer as arguments.  In
particular it has no column slice or witness.  Zero-mass invalid frequencies
are repaired to the fallback so that the response type always consists of
actual answers.  Witness data occur only in the success analysis.
-/

namespace MaxCutGames.Decoder.PrivateStrategy

attribute [local instance] Classical.propDecidable

open PrivateFourier
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Foundations.Games
open scoped BigOperators Classical

section Candidates

variable {E E' : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup E'] [Module F2 E'] [Fintype E]

theorem candidates_nonempty (Z : Submodule F2 E) (z : E)
    (τ : E →ₗ[F2] F2) (hz : τ z = 1) : (candidates Z z τ).Nonempty := by
  exact ⟨z, (mem_candidates Z z z τ).2 ⟨by simp, hz⟩⟩

theorem candidates_card_le (Z : Submodule F2 E) [Fintype Z] (z : E)
    (τ : E →ₗ[F2] F2) : (candidates Z z τ).card ≤ Fintype.card Z := by
  let f : {v // v ∈ candidates Z z τ} → Z := fun v =>
    ⟨v.1 - z, ((mem_candidates Z z v.1 τ).1 v.2).1⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    change x.val - z = y.val - z at he
    exact sub_left_injective he
  simpa using Fintype.card_le_of_injective f hf

theorem candidates_card_le_pow (Z : Submodule F2 E) [Fintype Z]
    [FiniteDimensional F2 Z] (z : E) (τ : E →ₗ[F2] F2)
    (r : ℕ) (hr : Module.finrank F2 Z ≤ r) :
    (candidates Z z τ).card ≤ 2 ^ r := by
  have hc : Fintype.card Z = 2 ^ Module.finrank F2 Z := by
    simpa [F2, MaxCutGames.Integration.BinaryLinear.F2, ZMod.card] using
      Module.card_fintype (Module.finBasis F2 Z)
  calc
    _ ≤ Fintype.card Z := candidates_card_le Z z τ
    _ = 2 ^ Module.finrank F2 Z := hc
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by decide : 0 < 2) hr

/-- First-bit preservation converts a projected coset member into an actual
answer in the left candidate set. -/
theorem candidate_preimage (Z : Submodule F2 E) (z : E)
    (π : E →ₗ[F2] E') (τ : E →ₗ[F2] F2) (τ' : E' →ₗ[F2] F2)
    (hτ : τ'.comp π = τ) (y : E') (hy : y - π z ∈ Z.map π)
    (hybit : τ' y = 1) : ∃ v ∈ candidates Z z τ, π v = y := by
  obtain ⟨w, hw, hwπ⟩ := Submodule.mem_map.mp hy
  have heq : π (z + w) = y := by
    rw [map_add, hwπ]
    rw [add_comm, sub_add_cancel]
  refine ⟨z + w, (mem_candidates Z z (z + w) τ).2 ⟨?_, ?_⟩, heq⟩
  · simpa only [add_sub_cancel_left] using hw
  · rw [← hτ, LinearMap.comp_apply, heq, hybit]

end Candidates

section RightRule

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

omit [FiniteDimensional F2 H] in
theorem chooseUnit_spec (σ : H →ₗ[F2] F2) (hne : σ ≠ 0) :
    σ (chooseUnit σ hne) = 1 := Classical.choose_spec (exists_unit σ hne)

theorem privateSeedLaw_expectation (F : (E →ₗ[F2] H) → K)
    (g : ((K →ₗ[F2] F2) × (H →ₗ[F2] E)) → ℝ) :
    (privateSeedLaw F).expectation g =
      𝔼 σ : K →ₗ[F2] F2, ∑ Φ : H →ₗ[F2] E,
        frequencyWeight (tableSign F σ) Φ * g (σ, Φ) := by
  simp only [FiniteDistribution.expectation, privateSeedLaw, Fintype.sum_prod_type,
    Fintype.expect_eq_sum_div_card]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]

omit [FiniteDimensional F2 E] [Fintype (H →ₗ[F2] E)] [Fintype (K →ₗ[F2] F2)] in
theorem privateOutput_eq_contraction (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ)
    (folded : ∀ N h, F (N + τ.smulRight h) = F N + ι h)
    (σ : K →ₗ[F2] F2) (Φ : H →ₗ[F2] E)
    (hn : σ.comp ι ≠ 0) (hp : 0 < frequencyWeight (tableSign F σ) Φ) :
    (privateOutput ι τ fallback (σ, Φ)).1 = Φ (chooseUnit (σ.comp ι) hn) := by
  have hunit : σ (ι (chooseUnit (σ.comp ι) hn)) = 1 := chooseUnit_spec (σ.comp ι) hn
  have hfold := tableSign_antifold F ι τ σ (chooseUnit (σ.comp ι) hn)
    (fun N => folded N _) hunit
  have hbit := positive_frequency_first_bit (tableSign F σ) τ
    (chooseUnit (σ.comp ι) hn) Φ hfold hp
  simp [privateOutput, hn, hbit]

theorem privateLaw_expectation [Fintype E] (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ)
    (g : ActualAnswer τ → ℝ) :
    (privateLaw F ι τ fallback).expectation g =
      𝔼 σ : K →ₗ[F2] F2, ∑ Φ : H →ₗ[F2] E,
        frequencyWeight (tableSign F σ) Φ * g (privateOutput ι τ fallback (σ, Φ)) := by
  rw [privateLaw, FiniteDistribution.expectation_pushforward, privateSeedLaw_expectation]

end RightRule

section LeftRule

variable {E : Type*} [AddCommGroup E] [Module F2 E] [Fintype E]

theorem candidateLaw_expectation (Z : Submodule F2 E) (z : E)
    (τ : E →ₗ[F2] F2) (hz : τ z = 1) (g : E → ℝ) :
    (candidateLaw Z z τ hz).expectation (fun v => g v.1) =
      𝔼 v ∈ candidates Z z τ, g v := by
  let : Nonempty {v // v ∈ candidates Z z τ} :=
    ⟨⟨z, (mem_candidates Z z z τ).2 ⟨by simp, hz⟩⟩⟩
  unfold candidateLaw
  rw [FiniteDistribution.expectation_pushforward, FiniteDistribution.expectation_uniform,
    Finset.expect_eq_sum_div_card]
  simp only [Fintype.card_coe, Finset.sum_coe_sort]

end LeftRule

section ConditionalAgreement

variable {U E H K : Type*}
variable [AddCommGroup U] [Module F2 U] [Fintype U]
variable [AddCommGroup E] [Module F2 E] [Fintype E]
variable [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

theorem conditionalAgreement_eq_sum (Z : Submodule F2 U) (z : U)
    (τU : U →ₗ[F2] F2) (hz : τU z = 1) (π : U →ₗ[F2] E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ) :
    conditionalAgreement Z z τU hz π F ι τ fallback =
      𝔼 σ : K →ₗ[F2] F2, ∑ Φ : H →ₗ[F2] E,
        frequencyWeight (tableSign F σ) Φ *
          (𝔼 v ∈ candidates Z z τU,
            if π v = (privateOutput ι τ fallback (σ, Φ)).1 then (1 : ℝ) else 0) := by
  unfold conditionalAgreement
  have hp (μ : FiniteDistribution (ActualAnswer τU × ActualAnswer τ)) :
      μ.probability (fun a => decide (π a.1.1 = a.2.1)) =
      μ.expectation (fun a => if π a.1.1 = a.2.1 then (1 : ℝ) else 0) := by
    simp [FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite]
  rw [hp, FiniteDistribution.expectation_product]
  simp_rw [privateLaw_expectation]
  rw [candidateLaw_expectation Z z τU hz (fun v =>
    𝔼 σ : K →ₗ[F2] F2, ∑ Φ : H →ₗ[F2] E,
      frequencyWeight (tableSign F σ) Φ *
        (if π v = (privateOutput ι τ fallback (σ, Φ)).1 then (1 : ℝ) else 0)),
    Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro σ _
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro Φ _
  exact (Finset.mul_expect _ _ _).symm

omit [Fintype E] in
omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] in
theorem goodCosetMass_nonneg (Q : Submodule F2 E) (z' : E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K) :
    0 ≤ goodCosetMass Q z' F ι := by
  apply Finset.expect_nonneg
  intro σ _
  split
  · exact Finset.sum_nonneg fun _ _ => frequencyWeight_nonneg _ _
  · exact le_rfl

omit [Fintype E] in
omit [FiniteDimensional F2 E] [Fintype (K →ₗ[F2] F2)] in
/-- A good sampled frequency has a valid left preimage.  Neither decoder is
given the proof or the witness used here. -/
theorem good_frequency_preimage (Z : Submodule F2 U) (z : U)
    (τU : U →ₗ[F2] F2) (π : U →ₗ[F2] E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ)
    (hτ : τ.comp π = τU)
    (folded : ∀ N h, F (N + τ.smulRight h) = F N + ι h)
    (σ : K →ₗ[F2] F2) (Φ : H →ₗ[F2] E)
    (hn : σ.comp ι ≠ 0)
    (hc : Φ ∈ frequencyCoset (Z.map π).mkQ ((σ.comp ι).smulRight (π z)))
    (hp : 0 < frequencyWeight (tableSign F σ) Φ) :
    ∃ v ∈ candidates Z z τU, π v = (privateOutput ι τ fallback (σ, Φ)).1 := by
  have hout := privateOutput_eq_contraction F ι τ fallback folded σ Φ hn hp
  apply candidate_preimage Z z π τU τ hτ
  · rw [hout]
    apply contraction_mem_target_coset (Z.map π) (σ.comp ι) (π z) Φ
      (chooseUnit (σ.comp ι) hn) (chooseUnit_spec _ _)
    simpa [frequencyCoset] using hc
  · exact (privateOutput ι τ fallback (σ, Φ)).2

/-- The actual independent policies agree with at least the good Fourier mass
divided by the number of left candidates. -/
theorem conditionalAgreement_ge_mass_div_card (Z : Submodule F2 U) (z : U)
    (τU : U →ₗ[F2] F2) (hz : τU z = 1) (π : U →ₗ[F2] E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ)
    (hτ : τ.comp π = τU)
    (folded : ∀ N h, F (N + τ.smulRight h) = F N + ι h) :
    goodCosetMass (Z.map π) (π z) F ι / (candidates Z z τU).card ≤
      conditionalAgreement Z z τU hz π F ι τ fallback := by
  rw [goodCosetMass, Finset.expect_div, conditionalAgreement_eq_sum]
  apply Finset.expect_le_expect
  intro σ _
  have hi := independent_agreement_lower (candidates Z z τU) π
    (fun Φ => (privateOutput ι τ fallback (σ, Φ)).1)
    (frequencyWeight (tableSign F σ))
    (fun Φ => σ.comp ι ≠ 0 ∧
      Φ ∈ frequencyCoset (Z.map π).mkQ ((σ.comp ι).smulRight (π z)))
    (frequencyWeight_nonneg _)
    (fun Φ hΦ hp => good_frequency_preimage Z z τU π F ι τ fallback
      hτ folded σ Φ hΦ.1 hΦ.2 hp)
  by_cases hn : σ.comp ι ≠ 0
  · simpa [hn, Finset.sum_filter] using hi
  · simpa [hn] using hi

end ConditionalAgreement

section SliceBound

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [Fintype E]
variable [AddCommGroup H] [Module F2 H] [Fintype H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

omit [Fintype E] in
/-- The actual transferred affine-slice agreement supplies the sampled good
Fourier mass, including removal of characters trivial on the hidden kernel. -/
theorem goodCosetMass_lower_from_slice (Q : Submodule F2 E)
    [Fintype (H →ₗ[F2] Q)] [Fintype ((E ⧸ Q) →ₗ[F2] H)]
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (hι : Function.Injective ι) (z' : E) (b : K)
    (α : ℝ) (hα : 0 ≤ α) (ℓ r : ℕ)
    (hH : Module.finrank F2 H ≤ ℓ) (hQ : Module.finrank F2 Q ≤ r)
    (hsmall : 1 / (Fintype.card H : ℝ) ≤ α / 8)
    (hagreement : α / 4 ≤ 𝔼 A : (E ⧸ Q) →ₗ[F2] H,
      if F (N₀ + A.comp Q.mkQ) = b + ι ((N₀ + A.comp Q.mkQ) z')
      then (1 : ℝ) else 0) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (ℓ * r) ≤ goodCosetMass Q z' F ι := by
  let good : (K →ₗ[F2] F2) → Prop := fun σ => σ.comp ι ≠ 0
  let : DecidablePred good := fun _ => Classical.propDecidable _
  let C : (K →ₗ[F2] F2) → ℝ := fun σ =>
    sliceCorrelation Q.mkQ N₀ (tableSign F σ) ((σ.comp ι).smulRight z')
  let mass : (K →ₗ[F2] F2) → ℝ := fun σ =>
    ∑ Φ ∈ frequencyCoset Q.mkQ ((σ.comp ι).smulRight z'),
      frequencyWeight (tableSign F σ) Φ
  have habs : α / 4 ≤ 𝔼 σ : K →ₗ[F2] F2, |C σ| :=
    hagreement.trans (agreement_le_average_abs_correlation Q.mkQ N₀ F ι z' b)
  have hbad : (𝔼 σ : K →ₗ[F2] F2,
      if good σ then (0 : ℝ) else 1) ≤ α / 8 := by
    have ht := trivial_restriction_probability ι hι
    have heq : (𝔼 σ : K →ₗ[F2] F2,
        if good σ then (0 : ℝ) else 1) = 1 / (Fintype.card H : ℝ) := by
      calc
        _ = 𝔼 σ : K →ₗ[F2] F2, if σ.comp ι = 0 then (1 : ℝ) else 0 := by
          apply Finset.expect_congr rfl
          intro σ _
          by_cases hn : σ.comp ι = 0 <;> simp [good, hn]
        _ = _ := ht
    exact heq.le.trans hsmall
  have hselected : α / 8 ≤ 𝔼 σ : K →ₗ[F2] F2,
      if good σ then |C σ| else 0 := by
    have hh := remove_bad_characters C good (α / 4) (α / 8)
      (fun σ => sliceCorrelation_tableSign_abs_le_one Q.mkQ N₀ F σ
        ((σ.comp ι).smulRight z')) habs hbad
    linarith
  have hbound := average_coset_mass_lower C mass good
    ((2 : ℝ) ^ (ℓ * r)) (α / 8) (by positivity) (by positivity) hselected
    (by
      intro σ _
      have hcs := sliceCorrelation_sq_le_coset_mass Q.mkQ N₀ (tableSign F σ)
        ((σ.comp ι).smulRight z')
      have hc : ((frequencyCoset Q.mkQ ((σ.comp ι).smulRight z')).card : ℝ) ≤
          (2 : ℝ) ^ (ℓ * r) := by
        exact_mod_cast frequencyCoset_card_le Q ((σ.comp ι).smulRight z') ℓ r hH hQ
      exact hcs.trans (mul_le_mul_of_nonneg_right hc
        (Finset.sum_nonneg fun _ _ => frequencyWeight_nonneg _ _)))
  calc
    _ ≤ 𝔼 σ : K →ₗ[F2] F2, if good σ then mass σ else 0 := hbound
    _ = goodCosetMass Q z' F ι := by
      unfold goodCosetMass
      apply Finset.expect_congr rfl
      intro σ _
      by_cases hn : σ.comp ι = 0 <;> simp [good, mass, hn]

end SliceBound

variable {U E H K : Type*}
variable [AddCommGroup U] [Module F2 U] [Fintype U]
variable [AddCommGroup E] [Module F2 E] [Fintype E]
variable [AddCommGroup H] [Module F2 H] [Fintype H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 U] [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

theorem conditionalAgreement_from_slice (Z : Submodule F2 U) [Fintype Z]
    (z : U) (τU : U →ₗ[F2] F2) (hz : τU z = 1) (π : U →ₗ[F2] E)
    [Fintype (H →ₗ[F2] Z.map π)] [Fintype ((E ⧸ Z.map π) →ₗ[F2] H)]
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (hι : Function.Injective ι)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ) (hτ : τ.comp π = τU)
    (folded : ∀ N h, F (N + τ.smulRight h) = F N + ι h)
    (b : K) (α : ℝ) (hα : 0 ≤ α) (ℓ r : ℕ)
    (hH : Module.finrank F2 H ≤ ℓ) (hZ : Module.finrank F2 Z ≤ r)
    (hsmall : 1 / (Fintype.card H : ℝ) ≤ α / 8)
    (hagreement : α / 4 ≤ 𝔼 A : (E ⧸ Z.map π) →ₗ[F2] H,
      if F (N₀ + A.comp (Z.map π).mkQ) =
        b + ι ((N₀ + A.comp (Z.map π).mkQ) (π z)) then (1 : ℝ) else 0) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (ℓ * r) / (2 : ℝ) ^ r ≤
      conditionalAgreement Z z τU hz π F ι τ fallback := by
  have hQ : Module.finrank F2 (Z.map π) ≤ r :=
    (Submodule.finrank_map_le π Z).trans hZ
  have hmass := goodCosetMass_lower_from_slice (Z.map π) N₀ F ι hι (π z) b
    α hα ℓ r hH hQ hsmall hagreement
  have hcard : ((candidates Z z τU).card : ℝ) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast candidates_card_le_pow Z z τU r hZ
  have hcardpos : (0 : ℝ) < (candidates Z z τU).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (candidates_nonempty Z z τU hz))
  calc
    _ ≤ goodCosetMass (Z.map π) (π z) F ι / (2 : ℝ) ^ r :=
      div_le_div_of_nonneg_right hmass (by positivity)
    _ ≤ goodCosetMass (Z.map π) (π z) F ι / (candidates Z z τU).card :=
      div_le_div_of_nonneg_left (goodCosetMass_nonneg _ _ _ _) hcardpos hcard
    _ ≤ _ := conditionalAgreement_ge_mass_div_card Z z τU hz π F ι τ fallback hτ folded

end MaxCutGames.Decoder.PrivateStrategy
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_TableKeysGame
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Restore actual orbit labels as a total function of the entire reduced key.
The arbitrary value at unrealized orbit bodies is used only to make this
function total; every table queried by the verifier and by the sparse
experiment is proved to be an actual realization.  Folding holds even for
the total extension, because the removed intercept is always restored.
-/

namespace MaxCutGames.Decoder.TableKeysRestoration

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open ActualSource

noncomputable section
attribute [local instance] Classical.propDecidable

section OrbitExtension

variable {Q T : Type} {s d : Nat}

theorem extendedLabel_actual (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (q : Q) :
    extendedLabel can label (ActualOrbit.body can q) = label (ActualOrbit.vertex can q) := by
  rw [extendedLabel, dite_eq_left ⟨q, rfl⟩]
  rfl

theorem restoredData_actual (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (q : Q) :
    restoredData can label (can q) = ActualOrbit.unfold can label q := by
  change extendedLabel can label (ActualOrbit.body can q) + ActualOrbit.offset can q = _
  rw [extendedLabel_actual]
  rfl

theorem restoredData_shift (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (D : Ambient s d × T) (c : Alphabet s) :
    restoredData can label (D.1 + (c, 0), D.2) = restoredData can label D + c := by
  simp only [restoredData, Prod.fst_add, Prod.snd_add, add_zero]
  exact (add_assoc _ _ _).symm

end OrbitExtension

theorem keyAnswer_actual (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (q : TableKeysGame.Query S k s d) :
    keyAnswer S k s d labeling (TableKeysGame.canonical S k s d q) =
      TableKeysGame.unfolded S k s d labeling q :=
  restoredData_actual _ _ q

theorem keyAnswer_shift (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (D : TableKeys.Key k (Fin S.«variables») (Fin S.occurrences) (Ambient s d))
    (c : Alphabet s) :
    keyAnswer S k s d labeling (D.1 + (c, 0), D.2) = keyAnswer S k s d labeling D + c :=
  restoredData_shift _ _ D c

/-- No extra consistency predicate: projected answers equal full-query answers
for every table and every compatible hidden extension. -/
theorem projectedAnswer_pullback (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Ambient s d) :
    projectedAnswer S k s d labeling J
        (RawPrivateTable.supported J (ActualGame.names S) occ slot) Y =
      TableKeysGame.unfolded S k s d labeling
        (occ, Y.comp (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) := by
  unfold projectedAnswer
  rw [TableKeys.projectedKey_pullback]
  exact keyAnswer_actual S k s d labeling
    (occ, Y.comp (RawPrivateTable.projection J (ActualGame.rhs S) occ slot))

/-- The visible table has the exact same affine folding law, with its genuine
homogeneous coordinate rather than an assumed or reconstructed first bit. -/
theorem projectedAnswer_fold (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k)) (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Ambient s d) (c : Alphabet s) :
    projectedAnswer S k s d labeling J O
        (Y + (TableKeys.visibleTau J).smulRight (c, (0 : Vector d))) =
      projectedAnswer S k s d labeling J O Y + c := by
  unfold projectedAnswer
  rw [TableKeys.projectedKey_shift, keyAnswer_shift]

end

end MaxCutGames.Decoder.TableKeysRestoration

/-!
The private row table obtained from an actual single-orbit labeling.  Its
parameters are only the visible question, public row map, visible row value,
and complement table.  Neither a hidden full question nor a selected affine
witness is supplied to its definition.  Affine target intercepts remain
explicit when the matrix is expressed in private kernel coordinates.
-/

namespace MaxCutGames.Decoder.TableKeysPrivateRow

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open ActualSource

noncomputable section

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

theorem assemble_prod_shift (J : Finset (Fin k)) (A : Alphabet s →ₗ[F2] R)
    (M₀ : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d) (h : A.ker) :
    (AdviceFibers.assemble A M₀ (N + (TableKeys.visibleTau J).smulRight h)).prod T =
      (AdviceFibers.assemble A M₀ N).prod T +
        (TableKeys.visibleTau J).smulRight ((h : Alphabet s), (0 : Vector d)) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change M₀ x + ((N x : Alphabet s) + TableKeys.visibleTau J x • (h : Alphabet s)) =
      (M₀ x + (N x : Alphabet s)) + TableKeys.visibleTau J x • (h : Alphabet s)
    exact (add_assoc _ _ _).symm
  · change T x = T x + TableKeys.visibleTau J x • (0 : Vector d)
    simp

/-- Folding on the hidden kernel is a consequence of the exact key action. -/
theorem rowAnswer_fold (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k)) (Q : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker) (h : A.ker) :
    rowAnswer S labeling J Q A rows T (N + (TableKeys.visibleTau J).smulRight h) =
      rowAnswer S labeling J Q A rows T N + (h : Alphabet s) := by
  unfold rowAnswer
  rw [assemble_prod_shift, TableKeysRestoration.projectedAnswer_fold]

theorem affine_target_on_row (J : Finset (Fin k)) (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker)
    (z : RawPartnerTarget.RawPoint J) (u : Alphabet s) :
    AdviceFibers.assemble A (AdviceFibers.observedBase A rows) N z + u =
      (N z : Alphabet s) + targetIntercept J A rows z u :=
  AdviceFibers.assemble_affine_target A (AdviceFibers.observedBase A rows) N z u

end

end MaxCutGames.Decoder.TableKeysPrivateRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_TransferredDecoding
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Decoding an actual transferred column slice

The point `Mstar` used to parametrize a transferred slice is distinct from the
canonical visible row base `observedBase A rows`.  The right strategy uses only
the latter.  Their kernel-valued difference appears solely in the analysis.
The exact quotient equivalence transports uniform slice agreement, including
the affine offset, to the conditional private-decoder theorem.
-/

noncomputable section

namespace MaxCutGames.Decoder.TransferredDecoding

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open ActualSource
open PrivateFourier PrivateStrategy
open scoped BigOperators Classical

open MaxCutGames.Inverse

attribute [local instance] Fintype.ofFinite

/-- Equality indicators depend on their propositions, not on the chosen
computable or classical decision procedures. Both deciders are explicit. -/
theorem indicator_congr (P Q : Prop) (dP : Decidable P) (dQ : Decidable Q)
    (h : P ↔ Q) : @ite ℝ P dP 1 0 = @ite ℝ Q dQ 1 0 := by
  cases propext h
  cases Subsingleton.elim dP dQ
  rfl

section Rebase

variable {E K R : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup K] [Module F2 K] [AddCommGroup R] [Module F2 R]

attribute [local instance] OAI.MaxCutGames.Decoder.TransferredDecoding.homFintype
/-- Rebase the complete quotient parametrization without changing its matrices. -/
theorem assemble_privateOrigin (A : K →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := E) A)
    (Mstar : E →ₗ[F2] K) (hstar : A.comp Mstar = rows.val)
    (Q : Submodule F2 E) (L : (E ⧸ Q) →ₗ[F2] A.ker) :
    AdviceFibers.assemble A (AdviceFibers.observedBase A rows)
      (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) =
        (RowErasureSliceQuotient.equiv A Q Mstar L).val := by
  ext x
  change AdviceFibers.observedBase A rows x +
      ((Mstar x - AdviceFibers.observedBase A rows x) + (L (Q.mkQ x) : K)) =
    Mstar x + (L (Q.mkQ x) : K)
  rw [← add_assoc]
  congr 1
  rw [add_comm, sub_add_cancel]

end Rebase

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

attribute [local instance] OAI.MaxCutGames.Decoder.TransferredDecoding.homFintype
/-- Exact transport from the actual conditional matrix slice to the private
Fourier coordinates.  `targetIntercept` uses the visible base, not `Mstar`. -/
theorem actual_slice_agreement_eq_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (Mstar : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s)
    (hstar : A.comp Mstar = rows.val) (Q : Submodule F2 (RawPartnerTarget.RawPoint J))
    [Fintype ((RawPartnerTarget.RawPoint J ⧸ Q) →ₗ[F2] A.ker)]
    [Fintype (RowErasureSliceQuotient.AffineSlice A Q Mstar)]
    (z' : RawPartnerTarget.RawPoint J) (u : Alphabet s) :
    (𝔼 M : RowErasureSliceQuotient.AffineSlice A Q Mstar,
      if TableKeysRestoration.projectedAnswer S k s d labeling J O (M.val.prod T) =
        M.val z' + u then (1 : ℝ) else 0) =
    𝔼 L : (RawPartnerTarget.RawPoint J ⧸ Q) →ₗ[F2] A.ker,
      if TableKeysPrivateRow.rowAnswer S labeling J O A rows T
          (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) =
        TableKeysPrivateRow.targetIntercept J A rows z' u +
          ((privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z' : Alphabet s)
      then (1 : ℝ) else 0 := by
  rw [← RowErasureSliceQuotient.expect_equiv A Q Mstar]
  apply Finset.expect_congr rfl
  intro L _
  rw [← assemble_privateOrigin A rows Mstar hstar Q L]
  change (if TableKeysPrivateRow.rowAnswer S labeling J O A rows T
      (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) =
    AdviceFibers.assemble A (AdviceFibers.observedBase A rows)
      (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z' + u
    then (1 : ℝ) else 0) = _
  rw [TableKeysPrivateRow.affine_target_on_row J A rows
    (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z' u]
  rw [add_comm (((privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z') : Alphabet s)
    (TableKeysPrivateRow.targetIntercept J A rows z' u)]

/-- Private policies for an actual restored labeling satisfy the conditional
decoding bound on every transferred good slice.  Folding and first-bit
preservation come from their concrete constructions, not additional premises. -/
theorem actual_transferred_decoding (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (Mstar : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s)
    (hstar : A.comp Mstar = rows.val)
    (Z : Submodule F2 (ActualHomogeneous.E k)) [Fintype Z]
    (z : ActualHomogeneous.E k) (hz : ActualHomogeneous.tau z = 1)
    (u : Alphabet s) (α : ℝ) (hα : 0 ≤ α) (ℓ r : ℕ)
    (hH : Module.finrank F2 A.ker ≤ ℓ) (hZ : Module.finrank F2 Z ≤ r)
    [Fintype A.ker]
    [Fintype (RawPartnerTarget.RawPoint J →ₗ[F2] A.ker)]
    [Fintype (A.ker →ₗ[F2] RawPartnerTarget.RawPoint J)]
    [Fintype (A.ker →ₗ[F2] Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot))]
    [Fintype ((RawPartnerTarget.RawPoint J ⧸
      Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) →ₗ[F2] A.ker)]
    [Fintype (RowErasureSliceQuotient.AffineSlice A
      (Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) Mstar)]
    (hsmall : 1 / (Fintype.card A.ker : ℝ) ≤ α / 8)
    (hagreement : α / 4 ≤
      𝔼 M : RowErasureSliceQuotient.AffineSlice A
          (Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) Mstar,
        if TableKeysRestoration.projectedAnswer S k s d labeling J
            (RawPrivateTable.supported J (ActualGame.names S) occ slot) (M.val.prod T) =
          M.val (RawPrivateTable.projection J (ActualGame.rhs S) occ slot z) + u
        then (1 : ℝ) else 0) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (ℓ * r) / (2 : ℝ) ^ r ≤
      PrivateStrategy.conditionalAgreement Z z ActualHomogeneous.tau hz
        (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)
        (TableKeysPrivateRow.rowAnswer S labeling J
          (RawPrivateTable.supported J (ActualGame.names S) occ slot) A rows T)
        A.ker.subtype (TableKeys.visibleTau J) (visibleFallback J) := by
  let π := RawPrivateTable.projection J (ActualGame.rhs S) occ slot
  let O := RawPrivateTable.supported J (ActualGame.names S) occ slot
  have hτ : (TableKeys.visibleTau J).comp π = ActualHomogeneous.tau := by
    apply LinearMap.ext
    intro x
    exact TableKeys.projection_preserves_homogeneous J (ActualGame.rhs S) occ slot x
  apply conditionalAgreement_from_slice Z z ActualHomogeneous.tau hz π
    (privateOrigin A rows Mstar hstar)
    (TableKeysPrivateRow.rowAnswer S labeling J O A rows T)
    A.ker.subtype Subtype.val_injective (TableKeys.visibleTau J) (visibleFallback J) hτ
    (TableKeysPrivateRow.rowAnswer_fold S labeling J O A rows T)
    (TableKeysPrivateRow.targetIntercept J A rows (π z) u)
    α hα ℓ r hH hZ hsmall
  apply hagreement.trans_eq
  calc
    _ = _ := actual_slice_agreement_eq_private S labeling J O A rows T Mstar hstar
      (Z.map π) (π z) u
    _ = _ := by
      apply Finset.expect_congr rfl
      intro L _
      exact indicator_congr _ _ _ _ Iff.rfl

end MaxCutGames.Decoder.TransferredDecoding

namespace MaxCutGames.Decoder.VisiblePolicies

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open MaxCutGames.Foundations.Games
open ActualSource PrivateStrategy
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d : ℕ} {R : Type} [AddCommGroup R] [Module F2 R]

attribute [local instance] OAI.MaxCutGames.Decoder.VisiblePolicies.homFintype
theorem chosenWitness_spec {S : Source}
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (q : LeftInput S k s d R) (h : ∃ w, good q w) :
    good q (chosenWitness good q) := by
  rw [chosenWitness, dite_eq_left h]
  exact Classical.choose_spec h

theorem rightPolicy_on_attainable (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (q : RightInput S J s d R)
    (h : ∃ M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s,
      q.rowMap.comp M = q.rows) :
    rightPolicy S labeling J q =
      privateLaw
        (TableKeysPrivateRow.rowAnswer S labeling J q.question q.rowMap ⟨q.rows, h⟩ q.complement)
        q.rowMap.ker.subtype (TableKeys.visibleTau J) (TransferredDecoding.visibleFallback J) := by
  rw [rightPolicy, dite_eq_left h]

theorem rightPolicy_on_draw (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R) :
    rightPolicy S labeling draw.singletons
      (AdviceExperiment.rightObservation (ActualGame.names S) draw).2 =
      privateLaw
        (TableKeysPrivateRow.rowAnswer S labeling draw.singletons
          (RawPrivateTable.supported draw.singletons (ActualGame.names S)
            draw.occurrences draw.positions)
          draw.rowMap (AdviceFibers.observe draw.rowMap draw.hiddenMatrix) draw.complement)
        draw.rowMap.ker.subtype (TableKeys.visibleTau draw.singletons)
        (TransferredDecoding.visibleFallback draw.singletons) := by
  rw [rightPolicy_on_attainable S labeling draw.singletons
    (AdviceExperiment.rightObservation (ActualGame.names S) draw).2
    (AdviceExperiment.right_rows_attainable (ActualGame.names S) draw)]
  rfl

/-- The private-decoding expression is exactly the actual local-kernel product
probability.  In particular there is no shared decoder random tape. -/
theorem observedAgreement_eq_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R) :
    observedAgreement S labeling good draw =
      let w := chosenWitness good (AdviceExperiment.leftObservation (ActualGame.rhs S) draw)
      PrivateStrategy.conditionalAgreement w.columns w.coefficient
        ActualHomogeneous.tau w.firstBit (AdviceExperiment.projection (ActualGame.rhs S) draw)
        (TableKeysPrivateRow.rowAnswer S labeling draw.singletons
          (RawPrivateTable.supported draw.singletons (ActualGame.names S)
            draw.occurrences draw.positions)
          draw.rowMap (AdviceFibers.observe draw.rowMap draw.hiddenMatrix) draw.complement)
        draw.rowMap.ker.subtype (TableKeys.visibleTau draw.singletons)
        (TransferredDecoding.visibleFallback draw.singletons) := by
  rw [observedAgreement, rightPolicy_on_draw S labeling draw]
  dsimp only [PrivateStrategy.conditionalAgreement, leftPolicy]
  congr 1
  funext answers
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

end MaxCutGames.Decoder.VisiblePolicies
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_SurrogateFibers
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The surrogate perturbation fixes the complementary table exactly. Splitting
the actual uniform matrix law therefore expresses surrogate acceptance as the
mean of the uniform shortcode tests on the `(U,T)` fibers, including zero
perturbation factors. This supplies the sampling identification needed before
applying the inverse theorem to the many useful fibers.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Reduction.ActualSource
open MaxCutGames.Fourier.MatrixNoise

namespace MaxCutGames.Decoder.ActualSpectral

open TableKeysGame PositiveMultiplier NoiseSampler SurrogateFibers

theorem expect_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    (𝔼 p, f p) = 𝔼 a, 𝔼 b, f (a, b) := by
  simpa only [Finset.univ_product_univ] using
    (Finset.expect_product Finset.univ Finset.univ f)

end MaxCutGames.Decoder.ActualSpectral
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AffineWitness
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Agreement counting for a folded action

A function that changes by an injectively encoded group element under a group
action can agree with an invariant target on at most one point per orbit.  The
proof injects the product of the acting group and the agreement set into the
underlying finite space.  Freeness of the action is not an additional premise:
the folding law and injectivity of the encoding force the needed freeness.

Only elementary group and finite-cardinality infrastructure is used here.
-/

/-!
The finite orbit count completing the first-bit witness normalization in v2.
The assumption in `normalize_of_good_count` is precisely that agreement is
strictly greater than the reciprocal of the row-kernel cardinality, expressed
without division. It is a quantitative goodness hypothesis, not an inverse
theorem or a nonlinear rank premise.
-/

/-!
The size bound for the actual simultaneous row/column slices in v2, Section 4.
Starting at any point of a nonempty slice, maps from the quotient by its column
span into the common row kernel give distinct points of that same affine slice.
Rank-nullity gives the dimension lower bound even when equations are dependent.
This argument uses only finite-dimensional linear algebra.
-/

namespace MaxCutGames.Inverse.Shortcode

section

open scoped BigOperators Matrix

namespace Slice

variable {ell m : ℕ}

theorem columnSpan_finrank_le (S : Slice ell m) :
    Module.finrank F2 S.columnSpan ≤ S.columns := by
  have h := finrank_range_le_card (R := F2) (M := Vector m) S.columnCoefficient
  change Module.finrank F2 (Submodule.span F2 (Set.range S.columnCoefficient)) ≤
    Fintype.card (Fin S.columns) at h
  rw [Fintype.card_fin] at h
  exact h

theorem card_directions (S : Slice ell m) :
    Nat.card S.Directions =
      2 ^ (Module.finrank F2 (Vector m ⧸ S.columnSpan) *
        Module.finrank F2 S.rowMap.ker) := by
  rw [Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

end Slice
end

/-! Exact connection between the v2 finite-array shortcode slices and the
linear-map slices used by affine witness normalization. -/

open scoped BigOperators Classical Matrix

end MaxCutGames.Inverse.Shortcode

/-! The probability form of first-bit witness normalization. -/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_MatrixCoordinates
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.MatrixCoordinates

open Integration.BinaryLinear Reduction
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable

attribute [local instance] OAI.MaxCutGames.Decoder.MatrixCoordinates.homFintype
theorem affine_evaluation (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k)) (z : Fin (1 + 2 * k) → F2)
    (u : Fin ell → F2) :
    Inverse.Shortcode.evaluate M z + u =
      (mapEquiv k ell).symm M ((domainCoordinates k).symm z) + u := by
  change Inverse.Shortcode.evaluate M z + u =
    Matrix.toLin' M ((domainCoordinates k) ((domainCoordinates k).symm z)) + u
  rw [LinearEquiv.apply_symm_apply]
  rfl

end
end MaxCutGames.Decoder.MatrixCoordinates

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_ActualGoodRows
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.ConstantSelection

open MaxCutGames.Foundations.Information
open SparseLaw

noncomputable section

theorem conditionalMass_pos {α : ℝ} (hα : 0 < α) (ell r : ℕ) :
    0 < conditionalMass α ell r := by
  unfold conditionalMass
  positivity

theorem variationBudget_suffices {α g₀ ε : ℝ} (hα : 0 < α) (ell r : ℕ)
    (hε : ε ≤ variationBudget α g₀ ell r) :
    (1 + α / 4) * ε ≤ α * g₀ * (1 / (2 : ℝ) ^ (ell * r)) / 8 := by
  have hd : 0 < 1 + α / 4 := by positivity
  have h := (le_div_iff₀ hd).mp hε
  calc
    (1 + α / 4) * ε = ε * (1 + α / 4) := mul_comm _ _
    _ ≤ visibleMass α g₀ ell r := h
    _ = α * g₀ * (1 / (2 : ℝ) ^ (ell * r)) / 8 := by
      unfold visibleMass
      ring

end
end MaxCutGames.Decoder.ConstantSelection

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RowErasureSelection
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Visible selection of a row-erasure witness. The selected description depends
only on the fixed table function, the row map, and the observed row value.
The full sampled matrix enters only the later event testing its membership in
the already selected slice. Classical choice fixes one witness once and for all;
proof irrelevance makes the choice independent of the goodness proof.
-/

namespace MaxCutGames.Inverse.RowErasure

variable {X Y A S D : Type*}

theorem SliceFamily.good_of_selectedDescription (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) {d : D}
    (hselected : F.selectedDescription f α a s = some d) :
    F.GoodAdvice f α a s := by
  classical
  by_contra hgood
  simp only [SliceFamily.selectedDescription, dite_eq_right hgood] at hselected
  cases hselected

theorem SliceFamily.selectedDescription_spec (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) {d : D}
    (hselected : F.selectedDescription f α a s = some d) :
    F.rowMap d = a ∧ F.rowValue d = s ∧ (F.points d).Nonempty ∧
      α / 2 ≤ F.agreement f d := by
  have hgood := F.good_of_selectedDescription f α a s hselected
  rw [F.selectedDescription_of_good f α a s hgood] at hselected
  have hd := Option.some.inj hselected
  rw [← hd]
  exact F.chosenDescription_spec f α a s hgood

theorem SliceFamily.selectedMatch_iff_of_advice (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) (x : X) (hx : F.advice a x = s) :
    F.selectedMatch f α a x ↔
      x ∈ F.points (F.chosenDescription f α a s hgood) ∧
        f x = F.target (F.chosenDescription f α a s hgood) x := by
  unfold SliceFamily.selectedMatch
  rw [hx, F.selectedDescription_of_good f α a s hgood]
  constructor
  · rintro ⟨d, hd, hmem, hmatch⟩
    have he := Option.some.inj hd
    simpa only [he] using And.intro hmem hmatch
  · rintro ⟨hmem, hmatch⟩
    exact ⟨_, rfl, hmem, hmatch⟩

theorem SliceFamily.selectedEvent_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X)
    (hx : F.selectedEvent f α a x) : F.goodAt f α a x := by
  obtain ⟨d, hd, _⟩ := hx
  exact F.good_of_selectedDescription f α a (F.advice a x) hd

theorem SliceFamily.selectedMatch_event (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X)
    (hx : F.selectedMatch f α a x) : F.selectedEvent f α a x := by
  obtain ⟨d, hd, hmem, _⟩ := hx
  exact ⟨d, hd, hmem⟩

end MaxCutGames.Inverse.RowErasure

/-!
Finite partition estimates for a selector fixed by visible data. The observation
fibers need not have equal sizes. Each local counting inequality is summed over
the actual fibers, then divided by the size of the hidden sample space.
-/

namespace MaxCutGames.Inverse.RowErasure.SelectionPartition

open scoped BigOperators Classical

variable {X S : Type*} [Fintype X] [Fintype S]

/-- Arbitrary real summands can be compared fiber by fiber. No uniformity of
the induced observation distribution is asserted or required. -/
theorem expect_le_expect_of_fiber_sum_le (observe : X → S) (f g : X → ℝ)
    (hle : ∀ s, (∑ x ∈ fiber observe s, f x) ≤ ∑ x ∈ fiber observe s, g x) :
    Finset.univ.expect f ≤ Finset.univ.expect g := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Finset.sum_fiberwise Finset.univ observe f,
    ← Finset.sum_fiberwise Finset.univ observe g]
  exact Finset.sum_le_sum fun s _ => hle s

omit [Fintype S] in
/-- On good visible data, the selected event sums exactly over the selected
points, including for arbitrary real weights on the hidden sample. -/
theorem sum_event_mul_fiber (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (s : S) (hgood : good s) (w : X → ℝ) :
    (∑ x ∈ fiber observe s, indicator (event observe good chosen x) * w x) =
      ∑ x ∈ chosen s, w x := by
  have hsub : chosen s ⊆ fiber observe s := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, support s x hx⟩
  calc
    _ = ∑ x ∈ fiber observe s, if x ∈ chosen s then w x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      simp [event, indicator, hobs, hgood, ite_mul]
    _ = ∑ x ∈ chosen s, if x ∈ chosen s then w x else 0 := by
      exact (Finset.sum_subset hsub (fun _ _ hnot => ite_eq_right hnot)).symm
    _ = ∑ x ∈ chosen s, w x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact ite_eq_left hx

omit [Fintype S] in
theorem sum_event_fiber (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (s : S) (hgood : good s) :
    (∑ x ∈ fiber observe s, indicator (event observe good chosen x)) =
      ((chosen s).card : ℝ) := by
  simpa using sum_event_mul_fiber observe good chosen support s hgood (fun _ => 1)

omit [Fintype S] in
theorem sum_match_fiber (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (hit : S → X → Prop) (s : S) (hgood : good s) :
    (∑ x ∈ fiber observe s, indicator (matchEvent observe good chosen hit x)) =
      ∑ x ∈ chosen s, indicator (hit s x) := by
  calc
    _ = ∑ x ∈ fiber observe s,
        indicator (event observe good chosen x) * indicator (hit s x) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      by_cases hevent : event observe good chosen x <;>
        by_cases hhit : hit s x <;>
        simp [matchEvent, indicator, hevent, hobs, hhit]
    _ = ∑ x ∈ chosen s, indicator (hit s x) :=
      sum_event_mul_fiber observe good chosen support s hgood (fun x => indicator (hit s x))

/-- A lower fraction inside every good fiber gives the same lower fraction
of the actual good-advice mass. Empty fibers and empty sample spaces are valid. -/
theorem mass_event_ge (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (c : ℝ)
    (hsize : ∀ s, good s →
      c * ((fiber observe s).card : ℝ) ≤ ((chosen s).card : ℝ)) :
    c * uniformMass (fun x => good (observe x)) ≤
      uniformMass (event observe good chosen) := by
  unfold uniformMass
  rw [Finset.mul_expect]
  apply expect_le_expect_of_fiber_sum_le observe
  intro s
  by_cases hgood : good s
  · rw [sum_event_fiber observe good chosen support s hgood]
    calc
      (∑ x ∈ fiber observe s, c * indicator (good (observe x))) =
          c * ((fiber observe s).card : ℝ) := by
        calc
          _ = ∑ _x ∈ fiber observe s, c := by
            apply Finset.sum_congr rfl
            intro x hx
            have hobs : observe x = s := (Finset.mem_filter.mp hx).2
            simp [indicator, hobs, hgood]
          _ = _ := by simp [mul_comm]
      _ ≤ _ := hsize s hgood
  · have hz : ∀ x ∈ fiber observe s,
        indicator (good (observe x)) = 0 ∧
          indicator (event observe good chosen x) = 0 := by
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      simp [indicator, event, hobs, hgood]
    have hleft : (∑ x ∈ fiber observe s, c * indicator (good (observe x))) = 0 :=
      Finset.sum_eq_zero fun x hx => by rw [(hz x hx).1, mul_zero]
    have hright : (∑ x ∈ fiber observe s, indicator (event observe good chosen x)) = 0 :=
      Finset.sum_eq_zero fun x hx => (hz x hx).2
    rw [hleft, hright]

/-- A matching fraction in every selected good fiber survives averaging over
the hidden sample space, without any equiprobability assumption on fibers. -/
theorem mass_match_ge (observe : X → S) (good : S → Prop)
    (chosen : S → Finset X)
    (support : ∀ s x, x ∈ chosen s → observe x = s)
    (hit : S → X → Prop) (β : ℝ)
    (hmatch : ∀ s, good s →
      β * ((chosen s).card : ℝ) ≤ ∑ x ∈ chosen s, indicator (hit s x)) :
    β * uniformMass (event observe good chosen) ≤
      uniformMass (matchEvent observe good chosen hit) := by
  unfold uniformMass
  rw [Finset.mul_expect]
  apply expect_le_expect_of_fiber_sum_le observe
  intro s
  by_cases hgood : good s
  · rw [← Finset.mul_sum, sum_event_fiber observe good chosen support s hgood,
      sum_match_fiber observe good chosen support hit s hgood]
    exact hmatch s hgood
  · have hz : ∀ x ∈ fiber observe s,
        indicator (event observe good chosen x) = 0 ∧
          indicator (matchEvent observe good chosen hit x) = 0 := by
      intro x hx
      have hobs : observe x = s := (Finset.mem_filter.mp hx).2
      simp [indicator, event, matchEvent, hobs, hgood]
    have hleft : (∑ x ∈ fiber observe s, β * indicator (event observe good chosen x)) = 0 :=
      Finset.sum_eq_zero fun x hx => by rw [(hz x hx).1, mul_zero]
    have hright :
        (∑ x ∈ fiber observe s, indicator (matchEvent observe good chosen hit x)) = 0 :=
      Finset.sum_eq_zero fun x hx => (hz x hx).2
    rw [hleft, hright]

end MaxCutGames.Inverse.RowErasure.SelectionPartition

/-!
Exact mass of a nonempty column slice within a fixed row-advice fiber. A
column span of dimension at most `r` costs at most `ell*r` binary degrees of
freedom. All inhomogeneous values are represented by the chosen base point.
-/

namespace MaxCutGames.Inverse.RowErasureColumnMass

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Decoder.AdviceFibers
open MaxCutGames.Inverse.RowErasureSliceQuotient

variable {E K R : Type*}
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K]
  [AddCommGroup R] [Module F2 R]

theorem card_affineSlice (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    Nat.card (AffineSlice A Q M₀) =
      2 ^ (Module.finrank F2 (E ⧸ Q) * Module.finrank F2 A.ker) := by
  rw [Nat.card_congr (equiv A Q M₀).symm,
    Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

theorem card_rowFiber (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K) :
    Nat.card (RowFiber A (A.comp M₀)) =
      2 ^ (Module.finrank F2 E * Module.finrank F2 A.ker) := by
  rw [Nat.card_congr (rowFiberEquiv A (A.comp M₀) M₀ rfl).symm,
    Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

/-- The exact number of row-fiber points for each compatible specification on
the column span. Dependent column equations cost only their actual rank. -/
theorem card_rowFiber_eq_mul (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    Nat.card (RowFiber A (A.comp M₀)) = Nat.card (AffineSlice A Q M₀) *
      2 ^ (Module.finrank F2 Q * Module.finrank F2 A.ker) := by
  rw [card_rowFiber, card_affineSlice, ← pow_add, ← Nat.add_mul,
    Q.finrank_quotient_add_finrank]

/-- The exact uniform fraction of the row fiber occupied by its compatible
affine column slice. -/
theorem column_fraction_eq (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    (Nat.card (AffineSlice A Q M₀) : ℝ) /
        (Nat.card (RowFiber A (A.comp M₀)) : ℝ) =
      1 / (2 : ℝ) ^ (Module.finrank F2 Q * Module.finrank F2 A.ker) := by
  have hs : (0 : ℝ) < Nat.card (AffineSlice A Q M₀) := by
    rw [card_affineSlice]
    positivity
  rw [card_rowFiber_eq_mul A Q M₀]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_mul_cancel_left₀ hs.ne', one_div]

/-- At most `r` independent column constraints retain at least the fraction
`2^(-ell*r)` of any nonempty row-advice fiber. -/
theorem column_fraction_ge (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) (ell r : ℕ)
    (hQ : Module.finrank F2 Q ≤ r) (hK : Module.finrank F2 K ≤ ell) :
    1 / (2 : ℝ) ^ (ell * r) ≤
      (Nat.card (AffineSlice A Q M₀) : ℝ) /
        (Nat.card (RowFiber A (A.comp M₀)) : ℝ) := by
  rw [column_fraction_eq]
  have hker : Module.finrank F2 A.ker ≤ ell := A.ker.finrank_le.trans hK
  have hexponent : Module.finrank F2 Q * Module.finrank F2 A.ker ≤ ell * r := by
    simpa only [Nat.mul_comm r ell] using Nat.mul_le_mul hQ hker
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent)

end MaxCutGames.Inverse.RowErasureColumnMass

/-!
Exact uniform parametrization of the concrete row/column slice.  The quotient
parameter describes every point, not only a lower-bounding subfamily.  Affine
targets retain the base-point contribution and their original intercept.
-/

namespace MaxCutGames.Inverse.Shortcode.Slice

open scoped BigOperators Matrix

variable {ell m : ℕ}

theorem card_points_eq_directions (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) : S.points.card = Nat.card S.Directions := by
  rw [← Nat.card_eq_finsetCard, Nat.card_congr (S.directionEquiv M₀ h₀).symm]

end MaxCutGames.Inverse.Shortcode.Slice

/-!
The actual finite matrix column event occupies at least `2^(-ell*r)` of its
row-advice fiber. This connects the intrinsic quotient-map count to the padded
descriptions used by the selector, without assuming independent equations.
-/

namespace MaxCutGames.Inverse.RowErasureDescriptionColumnMass

open MaxCutGames.Inverse.Shortcode
open MaxCutGames.Inverse.RowErasureDescriptions
open MaxCutGames.Inverse.RowErasureMatrix
open scoped BigOperators Classical

theorem rowOnly_contains_iff {ell m : ℕ} (S : Slice ell m) (M : Mat ell m) :
    (rowOnly S).Contains M ↔ rowAdvice S.rowCoefficient M = S.rowValue := by
  constructor
  · intro h
    funext i j
    exact h.1 i j
  · intro h
    constructor
    · intro i j
      exact congrFun (congrFun h i) j
    · intro i
      exact Fin.elim0 i

theorem rowOnly_points {ell m : ℕ} (S : Slice ell m) :
    (rowOnly S).points = rowFiber S.rowCoefficient S.rowValue := by
  ext M
  simp only [Slice.points, rowFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    rowOnly_contains_iff]

theorem contains_rowOnly {ell m : ℕ} (S : Slice ell m) {M : Mat ell m}
    (hM : S.Contains M) : (rowOnly S).Contains M := by
  exact ⟨hM.1, fun i => Fin.elim0 i⟩

theorem rowOnly_columnSpan {ell m : ℕ} (S : Slice ell m) :
    (rowOnly S).columnSpan = ⊥ := by
  apply Submodule.span_eq_bot.mpr
  rintro _ ⟨i, _⟩
  exact Fin.elim0 i

theorem rowOnly_quotient_finrank {ell m : ℕ} (S : Slice ell m) :
    Module.finrank F2 (Shortcode.Vector m ⧸ (rowOnly S).columnSpan) = m := by
  have h := (rowOnly S).columnSpan.finrank_quotient_add_finrank
  have hz : Module.finrank F2 (rowOnly S).columnSpan = 0 := by
    rw [rowOnly_columnSpan]
    simp
  have hm : Module.finrank F2 (Shortcode.Vector m) = m := by simp [Shortcode.Vector]
  rw [hz, add_zero, hm] at h
  exact h

/-- The size of an actual nonempty row fiber, in the same coordinates used by
the selector's uniform matrix sample. -/
theorem rowFiber_card {ell m : ℕ} (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) :
    (rowFiber S.rowCoefficient S.rowValue).card =
      2 ^ (m * Module.finrank F2 S.rowMap.ker) := by
  rw [← rowOnly_points S,
    (rowOnly S).card_points_eq_directions M₀ (contains_rowOnly S h₀),
    (rowOnly S).card_directions, rowOnly_quotient_finrank]
  rfl

theorem rowFiber_nonempty {ell m r : ℕ} (d : Description ell m r)
    (hne : d.toSlice.points.Nonempty) : (rowFiber d.1 d.2.1).Nonempty := by
  obtain ⟨M, hM⟩ := hne
  have hc : d.toSlice.Contains M := (Finset.mem_filter.mp hM).2
  refine ⟨M, (mem_rowFiber _ _ _).mpr ?_⟩
  funext i j
  exact hc.1 i j

/-- The chosen nonempty column event has the required mass inside its actual
row-advice fiber. The target coefficient and intercept do not affect its size. -/
theorem column_fraction_ge {ell m r : ℕ} (d : Description ell m r)
    (hne : d.toSlice.points.Nonempty) :
    1 / (2 : ℝ) ^ (ell * r) ≤
      (d.toSlice.points.card : ℝ) / ((rowFiber d.1 d.2.1).card : ℝ) := by
  obtain ⟨M₀, hM₀⟩ := hne
  have h₀ : d.toSlice.Contains M₀ := (Finset.mem_filter.mp hM₀).2
  have hs : d.toSlice.points.card = Nat.card
      (RowErasureSliceQuotient.AffineSlice d.toSlice.rowMap d.toSlice.columnSpan
        (Matrix.toLin' M₀)) := by
    rw [d.toSlice.card_points_eq_directions M₀ h₀, d.toSlice.card_directions,
      RowErasureColumnMass.card_affineSlice]
  have hr : (rowFiber d.1 d.2.1).card = Nat.card
      (MaxCutGames.Decoder.AdviceFibers.RowFiber d.toSlice.rowMap
        (d.toSlice.rowMap.comp (Matrix.toLin' M₀))) := by
    have hm : Module.finrank F2 (Shortcode.Vector m) = m := by simp [Shortcode.Vector]
    rw [RowErasureColumnMass.card_rowFiber, hm]
    exact rowFiber_card d.toSlice M₀ h₀
  have h := RowErasureColumnMass.column_fraction_ge
    d.toSlice.rowMap d.toSlice.columnSpan (Matrix.toLin' M₀) ell r
    d.toSlice.columnSpan_finrank_le (by simp [Shortcode.Vector])
  rwa [← hs, ← hr] at h

end MaxCutGames.Inverse.RowErasureDescriptionColumnMass

/-!
The selected column event under the actual uniform matrix and row-map samples.
The witness is fixed by visible row advice before testing the hidden matrix.
Fiber sizes are retained explicitly; no uniformity of row values is assumed.
The final averaging lemmas also allow arbitrary nonnegative context weights.
-/

namespace MaxCutGames.Inverse.RowErasure

open scoped BigOperators

variable {X Y A S D : Type*}

theorem SliceFamily.selectedPoints_of_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    F.selectedPoints f α a s = F.points (F.chosenDescription f α a s hgood) := by
  unfold SliceFamily.selectedPoints
  rw [F.selectedDescription_of_good f α a s hgood]

theorem SliceFamily.selectedHit_of_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) (x : X) :
    F.selectedHit f α a s x ↔ f x = F.target (F.chosenDescription f α a s hgood) x := by
  unfold SliceFamily.selectedHit
  rw [F.selectedDescription_of_good f α a s hgood]
  constructor
  · rintro ⟨d, hd, hhit⟩
    have he := Option.some.inj hd
    simpa only [he] using hhit
  · intro hhit
    exact ⟨_, rfl, hhit⟩

theorem SliceFamily.selectedPoints_support (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) (x : X)
    (hx : x ∈ F.selectedPoints f α a s) : F.advice a x = s := by
  classical
  cases hd : F.selectedDescription f α a s with
  | none => simp [SliceFamily.selectedPoints, hd] at hx
  | some d =>
    have hspec := F.selectedDescription_spec f α a s hd
    have hmem : x ∈ F.points d := by
      simpa only [SliceFamily.selectedPoints, hd] using hx
    have h := F.points_row d x hmem
    rw [hspec.1, hspec.2.1] at h
    exact h

theorem SliceFamily.selectedEvent_iff_points (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) :
    F.selectedEvent f α a x ↔
      F.GoodAdvice f α a (F.advice a x) ∧
        x ∈ F.selectedPoints f α a (F.advice a x) := by
  classical
  by_cases hg : F.GoodAdvice f α a (F.advice a x)
  · rw [F.selectedEvent_iff_of_advice f α a (F.advice a x) hg x rfl,
      F.selectedPoints_of_good f α a (F.advice a x) hg]
    simp only [hg, true_and]
  · constructor
    · intro hx
      exact (hg (F.selectedEvent_good f α a x hx)).elim
    · intro hx
      exact (hg hx.1).elim

theorem SliceFamily.selectedMatch_iff_points (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) :
    F.selectedMatch f α a x ↔
      (F.GoodAdvice f α a (F.advice a x) ∧
        x ∈ F.selectedPoints f α a (F.advice a x)) ∧
          F.selectedHit f α a (F.advice a x) x := by
  classical
  by_cases hg : F.GoodAdvice f α a (F.advice a x)
  · rw [F.selectedMatch_iff_of_advice f α a (F.advice a x) hg x rfl,
      F.selectedPoints_of_good f α a (F.advice a x) hg,
      F.selectedHit_of_good f α a (F.advice a x) hg x]
    simp only [hg, true_and]
  · constructor
    · intro hx
      exact (hg (F.selectedEvent_good f α a x (F.selectedMatch_event f α a x hx))).elim
    · intro hx
      exact (hg hx.1.1).elim

theorem SliceFamily.selectedPoints_match_sum (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    (α / 2) * ((F.selectedPoints f α a s).card : ℝ) ≤
      ∑ x ∈ F.selectedPoints f α a s, indicator (F.selectedHit f α a s x) := by
  classical
  have hspec := F.chosenDescription_spec f α a s hgood
  have hcard : (0 : ℝ) < (F.points (F.chosenDescription f α a s hgood)).card :=
    Nat.cast_pos.mpr hspec.2.2.1.card_pos
  have hagree := hspec.2.2.2
  rw [SliceFamily.agreement, Finset.expect_eq_sum_div_card] at hagree
  rw [F.selectedPoints_of_good f α a s hgood]
  simp_rw [F.selectedHit_of_good f α a s hgood]
  exact (le_div_iff₀ hcard).mp hagree

end MaxCutGames.Inverse.RowErasure

namespace MaxCutGames.Inverse.RowErasureMatrix

open MaxCutGames.Inverse.Shortcode
open MaxCutGames.Inverse.RowErasure
open MaxCutGames.Inverse.RowErasureDescriptions
open MaxCutGames.Inverse.RowErasureDescriptionColumnMass
open scoped BigOperators

variable {ell m r : ℕ}

theorem selectedPoints_column_mass (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) (s : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A s) :
    (1 / (2 : ℝ) ^ (ell * r)) * ((rowFiber A s).card : ℝ) ≤
      (((family ell m r).selectedPoints f α A s).card : ℝ) := by
  let d := (family ell m r).chosenDescription f α A s hgood
  have hspec := (family ell m r).chosenDescription_spec f α A s hgood
  have hne : d.toSlice.points.Nonempty := hspec.2.2.1
  have hcard : (0 : ℝ) < (rowFiber d.1 d.2.1).card :=
    Nat.cast_pos.mpr (rowFiber_nonempty d hne).card_pos
  have h := (le_div_iff₀ hcard).mp (column_fraction_ge d hne)
  have hA : d.1 = A := hspec.1
  have hs : d.2.1 = s := hspec.2.1
  rw [hA, hs] at h
  rw [(family ell m r).selectedPoints_of_good f α A s hgood]
  exact h

theorem selected_event_mass_ge (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) :
    (1 / (2 : ℝ) ^ (ell * r)) *
      uniformMass ((family ell m r).goodAt f α A) ≤
        uniformMass ((family ell m r).selectedEvent f α A) := by
  have h := SelectionPartition.mass_event_ge
    ((family ell m r).advice A) ((family ell m r).GoodAdvice f α A)
    ((family ell m r).selectedPoints f α A)
    ((family ell m r).selectedPoints_support f α A)
    (1 / (2 : ℝ) ^ (ell * r))
    (fun s hg => by
      have hfiber : SelectionPartition.fiber ((family ell m r).advice A) s =
          rowFiber A s := by
        ext M
        simp only [SelectionPartition.fiber, rowFiber, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rfl
      rw [hfiber]
      exact selectedPoints_column_mass f α A s hg)
  have he : SelectionPartition.event ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A) =
      (family ell m r).selectedEvent f α A := by
    funext M
    exact propext ((family ell m r).selectedEvent_iff_points f α A M).symm
  rw [he] at h
  exact h

theorem selected_match_mass_ge (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) :
    (α / 2) * uniformMass ((family ell m r).selectedEvent f α A) ≤
      uniformMass ((family ell m r).selectedMatch f α A) := by
  have h := SelectionPartition.mass_match_ge
    ((family ell m r).advice A) ((family ell m r).GoodAdvice f α A)
    ((family ell m r).selectedPoints f α A)
    ((family ell m r).selectedPoints_support f α A)
    ((family ell m r).selectedHit f α A)
    (α / 2) ((family ell m r).selectedPoints_match_sum f α A)
  have he : SelectionPartition.event ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A) =
      (family ell m r).selectedEvent f α A := by
    funext M
    exact propext ((family ell m r).selectedEvent_iff_points f α A M).symm
  have hm : SelectionPartition.matchEvent ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A)
      ((family ell m r).selectedHit f α A) =
      (family ell m r).selectedMatch f α A := by
    funext M
    exact propext ((family ell m r).selectedMatch_iff_points f α A M).symm
  rw [he, hm] at h
  exact h

theorem selectedEventMass_ge (f : Mat ell m → Vector ell) (α : ℝ) :
    (1 / (2 : ℝ) ^ (ell * r)) * adviceMass ((family ell m r).goodAt f α) ≤
      selectedEventMass r f α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun (A : RowMap ell r) _ => selected_event_mass_ge f α A)
  rw [← Finset.mul_expect] at h
  have hadvice : (𝔼 A : RowMap ell r, uniformMass ((family ell m r).goodAt f α A)) =
      adviceMass ((family ell m r).goodAt f α) := by
    simp only [uniformMass, adviceMass]
    exact Finset.expect_comm _ _ _
  rw [hadvice] at h
  exact h

theorem selectedMatchMass_ge (f : Mat ell m → Vector ell) (α : ℝ) :
    (α / 2) * selectedEventMass r f α ≤ selectedMatchMass r f α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun (A : RowMap ell r) _ => selected_match_mass_ge f α A)
  rw [← Finset.mul_expect] at h
  exact h

/-- The same bound for a uniform finite seed space, allowing repeated contexts. -/
theorem selectedEventMass_contextual_ge {Q : Type*} [Fintype Q]
    (f : Q → Mat ell m → Vector ell) (α g₀ : ℝ)
    (hgood : g₀ ≤ 𝔼 q, adviceMass ((family ell m r).goodAt (f q) α)) :
    (1 / (2 : ℝ) ^ (ell * r)) * g₀ ≤ 𝔼 q, selectedEventMass r (f q) α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun q _ => selectedEventMass_ge (r := r) (f q) α)
  rw [← Finset.mul_expect] at h
  exact (mul_le_mul_of_nonneg_left hgood (by positivity)).trans h

theorem selectedMatchMass_contextual_ge {Q : Type*} [Fintype Q]
    (f : Q → Mat ell m → Vector ell) (α : ℝ) :
    (α / 2) * (𝔼 q, selectedEventMass r (f q) α) ≤
      𝔼 q, selectedMatchMass r (f q) α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun q _ => selectedMatchMass_ge (r := r) (f q) α)
  rwa [← Finset.mul_expect] at h

end MaxCutGames.Inverse.RowErasureMatrix

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_ActualEvents
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two full-table events used in the projected-witness transfer. Their
sample space contains actual occurrence tuples and complete affine tables,
but no projection choice. The selected witness depends on row advice only.
-/

namespace MaxCutGames.Decoder.ActualEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] OAI.MaxCutGames.Decoder.ActualEvents.homFintype
theorem targetHit_implies_slice (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (p : Sample S k s d r)
    (h : targetHit S k s d r labeling α p = true) :
    sliceEvent S k s d r labeling α p = true := by
  exact of_decide_eq_true h |> fun hm => decide_eq_true
    ((RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch_event _ α _ _ hm)

theorem uniform_probability_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (p : Ω → Bool) :
    (FiniteDistribution.uniform Ω).probability p =
      𝔼 x : Ω, if p x then (1 : ℝ) else 0 := by
  simp only [FiniteDistribution.probability, FiniteDistribution.uniform,
    Fintype.expect_eq_sum_div_card, Finset.sum_div, ite_div, one_div, zero_div]

theorem unrestricted_slice_mass (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    (unrestricted S k s d r).probability (sliceEvent S k s d r labeling α) =
      𝔼 q : Context S k d,
        RowErasureMatrix.selectedEventMass r
          (ActualGoodRows.table S k s d labeling q.1 q.2) α := by
  unfold unrestricted
  rw [uniform_probability_expect, ActualSpectral.expect_prod]
  apply Finset.expect_congr rfl
  intro q _
  rw [ActualSpectral.expect_prod]
  simp only [sliceEvent, RowErasureMatrix.selectedEventMass, uniformMass, indicator,
    decide_eq_true_eq]

theorem unrestricted_match_mass (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    (unrestricted S k s d r).probability
      (fun p => sliceEvent S k s d r labeling α p && targetHit S k s d r labeling α p) =
      𝔼 q : Context S k d,
        RowErasureMatrix.selectedMatchMass r
          (ActualGoodRows.table S k s d labeling q.1 q.2) α := by
  have he : (fun p => sliceEvent S k s d r labeling α p && targetHit S k s d r labeling α p) =
      targetHit S k s d r labeling α := by
    funext p
    by_cases h : targetHit S k s d r labeling α p = true
    · simp [h, targetHit_implies_slice S k s d r labeling α p h]
    · simp [Bool.eq_false_iff.mpr h]
  rw [he]
  unfold unrestricted
  rw [uniform_probability_expect, ActualSpectral.expect_prod]
  apply Finset.expect_congr rfl
  intro q _
  rw [ActualSpectral.expect_prod]
  simp only [targetHit, RowErasureMatrix.selectedMatchMass, uniformMass, indicator,
    decide_eq_true_eq]

/-- The full-table slice event pays exactly one bounded column-fiber factor. -/
theorem slice_probability_lower (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α g₀ : ℝ)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α) :
    g₀ * (1 / (2 : ℝ) ^ (s * r)) ≤
      (unrestricted S k s d r).probability (sliceEvent S k s d r labeling α) := by
  rw [unrestricted_slice_mass]
  have h := RowErasureMatrix.selectedEventMass_contextual_ge (r := r)
    (fun q : Context S k d => ActualGoodRows.table S k s d labeling q.1 q.2) α g₀
    (by simpa only [ActualGoodRows.adviceMass, ActualSpectral.expect_prod] using hgood)
  simpa only [mul_comm] using h

theorem target_probability_lower (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    (α / 2) * (unrestricted S k s d r).probability (sliceEvent S k s d r labeling α) ≤
      (unrestricted S k s d r).probability
        (fun p => sliceEvent S k s d r labeling α p && targetHit S k s d r labeling α p) := by
  rw [unrestricted_slice_mass, unrestricted_match_mass]
  exact RowErasureMatrix.selectedMatchMass_contextual_ge (r := r)
    (fun q : Context S k d => ActualGoodRows.table S k s d labeling q.1 q.2) α

end
end MaxCutGames.Decoder.ActualEvents

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_SelectedPolicies
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual visible selector used by the stochastic decoder

At fixed labeling, the matrix table depends only on the occurrence question and
complement map. Its normalized row/column witness is selected from the observed
row map and row value. Transporting this witness through the actual homogeneous
coordinates supplies `VisiblePolicies.ResponseWitness`; the selected target's
affine intercept is retained separately, including exact equality on the slice.
-/

noncomputable section

namespace MaxCutGames.Decoder.SelectedPolicies

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction
open MaxCutGames.Inverse
open ActualSource VisiblePolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

variable {k s d r : ℕ}

theorem normalizedResponse_dimension (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    Module.finrank F2 (normalizedResponse S labeling α hα hsmall q hgood).columns ≤ r := by
  exact (Submodule.finrank_map_le (domainCoordinates k).symm.toLinearMap
    (normalizedDescription S labeling α hα hsmall q hgood).toSlice.columnSpan).trans
    (normalizedDescription S labeling α hα hsmall q hgood).toSlice.columnSpan_finrank_le

theorem chosenWitness_eq_normalizedResponse (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    chosenWitness (goodPredicate S labeling α hα hsmall) q =
      normalizedResponse S labeling α hα hsmall q hgood := by
  obtain ⟨hgood', hw⟩ := chosenWitness_spec (goodPredicate S labeling α hα hsmall) q
    ⟨normalizedResponse S labeling α hα hsmall q hgood, hgood, rfl⟩
  exact hw

/-- Coordinate transport keeps the actual affine target, including its selected
intercept; first-bit normalization never replaces it by a homogeneous target. -/
theorem normalized_target (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q)
    (M : Shortcode.Mat s (1 + 2 * k)) :
    (RowErasureMatrix.family s (1 + 2 * k) r).target
        (normalizedDescription S labeling α hα hsmall q hgood) M =
      (mapEquiv k s).symm M (normalizedResponse S labeling α hα hsmall q hgood).coefficient +
        (normalizedDescription S labeling α hα hsmall q hgood).intercept :=
  affine_evaluation k s M _ _

end MaxCutGames.Decoder.SelectedPolicies
end

/-! The selected full-table events pulled back to the genuine projected
experiment. The comparison space forgets the projection, while complete data
retains it only for the subsequent finite conditional-law argument. -/

namespace MaxCutGames.Decoder.ActualSeedEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype_r7c257f_1 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
theorem targetHit_eq_selectedMatch (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ)
    (x : Seed S k s d r) :
    targetHit S k s d r labeling α x = decide
      ((Inverse.RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch
        (SelectedPolicies.fullTable S labeling
          (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x))) α
        (LinearMap.toMatrix' (draw x).rowMap)
        (MatrixCoordinates.mapEquiv k s (AdviceExperiment.paddedMatrix (ActualGame.rhs S) (draw x)))) :=
  rfl

/-- Positive selected-slice mass automatically supplies actual good left
advice; goodness is not an independent projected experiment assumption. -/
theorem slice_good (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ)
    (x : Seed S k s d r) (hx : slice S k s d r labeling α x = true) :
    SelectedPolicies.GoodAdvice S labeling α
      (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x)) := by
  rw [slice_eq_selectedEvent] at hx
  have h := (Inverse.RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent_good
    (SelectedPolicies.fullTable S labeling
      (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x))) α
    (LinearMap.toMatrix' (draw x).rowMap)
    (MatrixCoordinates.mapEquiv k s (AdviceExperiment.paddedMatrix (ActualGame.rhs S) (draw x)))
    (of_decide_eq_true hx)
  change (Inverse.RowErasureMatrix.family s (1 + 2 * k) r).GoodAdvice
    (SelectedPolicies.fullTable S labeling
      (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x))) α
    (LinearMap.toMatrix' (draw x).rowMap)
    (MatrixCoordinates.mapEquiv k r
      ((draw x).rowMap.comp (AdviceExperiment.paddedMatrix (ActualGame.rhs S) (draw x))))
  rw [MatrixCoordinates.mapEquiv_rowAdvice]
  exact h

end
end MaxCutGames.Decoder.ActualSeedEvents

/-! Whole-table variation for the exact projected seed law in the selected
event coordinates. The projection is averaged out before the comparison. -/

namespace MaxCutGames.Decoder.ActualSeedVariation

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

theorem uniform_pushforward_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (e : X ≃ Y) :
    (FiniteDistribution.uniform X).pushforward e = FiniteDistribution.uniform Y := by
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  simp only [FiniteDistribution.transport, FiniteDistribution.uniform,
    Fintype.card_congr e]

theorem totalVariation_pushforward_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (μ ν : FiniteDistribution X) (e : X ≃ Y) :
    (μ.pushforward e).totalVariation (ν.pushforward e) = μ.totalVariation ν := by
  rw [FiniteDistribution.pushforward_equiv, FiniteDistribution.pushforward_equiv]
  unfold FiniteDistribution.totalVariation FiniteDistribution.transport
  congr 1
  exact e.symm.sum_comp (fun x => |μ.weight x - ν.weight x|)

attribute [local instance] OAI.MaxCutGames.Decoder.ActualSeedVariation.homFintype
/-- Three independent uniform samples are uniform on their full product. -/
theorem ideal_full_uniform (S : Source) (k s d r : ℕ) :
    AdviceLaw.withKernel
      ((FiniteDistribution.uniform (ActualGame.Question S k)).product
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)))
      (fun _ => FiniteDistribution.uniform (ActualGame.Map k s d)) =
        FiniteDistribution.uniform (ActualEvents.FullTableSample S k s d r) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro p
  simp only [AdviceLaw.withKernel, FiniteDistribution.product, FiniteDistribution.uniform,
    Fintype.card_prod, Nat.cast_mul]
  ring

theorem ideal_pad_coordinates (S : Source) (k s d r : ℕ) :
    (AdviceLaw.withKernel
      ((FiniteDistribution.uniform (ActualGame.Question S k)).product
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)))
      (fun _ => FiniteDistribution.uniform (ActualGame.Map k s d))).pushforward
        (ActualEvents.fullTableEquiv S k s d r) = ActualEvents.unrestricted S k s d r := by
  rw [ideal_full_uniform]
  exact uniform_pushforward_equiv _

theorem actual_totalVariation_le_slope (S : Source) (k s d r : ℕ)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (ActualEvents.unrestricted S k s d r).totalVariation
      ((ActualSeedEvents.law S k s d r β hβ hβ').pushforward (ActualSeedEvents.pad S k s d r)) ≤
        Foundations.Information.totalVariation
          (SparseLaw.independentWeights
            (SparseLaw.mixture β (SparseLaw.singletonPairWeights (Ambient s d))) k)
          (SparseLaw.uniformWeights (Fin k → Ambient s d × Ambient s d)) := by
  rw [FiniteDistribution.totalVariation_comm]
  have h := AdviceLaw.fullSeed_totalVariation_le_slope (V := Ambient s d)
    (FiniteDistribution.uniform (ActualGame.Question S k))
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r))
    (fun i => toBit (ActualGame.rhs S i)) β hβ hβ'
  rw [← ideal_pad_coordinates S k s d r]
  change ((ActualSeedEvents.law S k s d r β hβ hβ').pushforward
      (fun x => ActualEvents.fullTableEquiv S k s d r
        (AdviceLaw.fullSeedPad (fun i => toBit (ActualGame.rhs S i)) x))).totalVariation _ ≤ _
  rw [← FiniteDistribution.pushforward_comp, totalVariation_pushforward_equiv]
  convert h using 1 <;> congr 4 ; exact Subsingleton.elim _ _

end
end MaxCutGames.Decoder.ActualSeedVariation

/-!
# Conditional success of the actual selected policies

This endpoint uses the normalized witness chosen from the left observation and
the private Fourier kernel chosen from the right observation. The hypothesis is
literal uniform agreement on a transferred affine column slice. Deriving that
hypothesis from the actual visible conditional law is the separate transfer
step; it is not assumed as an inverse theorem or as extra prover information.
-/

noncomputable section

namespace MaxCutGames.Decoder.SelectedDecoding

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction MaxCutGames.Soundness
open MaxCutGames.Inverse
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

attribute [local instance] OAI.MaxCutGames.Decoder.SelectedDecoding.homFintype
/-- The selected target-hit event uses exactly the transported coefficient and
its adjusted intercept. This identifies the event used by the mass estimates. -/
theorem selectedMatch_iff_normalized (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q)
    (M : Shortcode.Mat s (1 + 2 * k))
    (hrow : RowErasureMatrix.rowAdvice (LinearMap.toMatrix' q.rowMap) M =
      mapEquiv k r q.rows) :
    (RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch
        (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap) M ↔
      M ∈ (RowErasureMatrix.family s (1 + 2 * k) r).points
          (normalizedDescription S labeling α hα hsmall q hgood) ∧
        fullTable S labeling q M =
          (mapEquiv k s).symm M
              (normalizedResponse S labeling α hα hsmall q hgood).coefficient +
            (normalizedDescription S labeling α hα hsmall q hgood).intercept := by
  let F := RowErasureMatrix.family s (1 + 2 * k) r
  let D := normalizedDescription S labeling α hα hsmall q hgood
  let D₀ := F.chosenDescription (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood
  have he := F.selectedMatch_iff_of_advice (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood M hrow
  obtain ⟨_, _, _, _, _, hslice, _, htarget⟩ :=
    normalizedDescription_spec S labeling α hα hsmall q hgood
  have hp : F.points D = F.points D₀ := congrArg Shortcode.Slice.points hslice
  rw [← normalized_target S labeling α hα hsmall q hgood M]
  constructor
  · intro h
    obtain ⟨hm, hf⟩ := he.mp h
    refine ⟨hp.symm ▸ hm, ?_⟩
    rw [htarget M hm]
    exact hf
  · rintro ⟨hm, hf⟩
    have hm₀ : M ∈ F.points D₀ := hp ▸ hm
    apply he.mpr
    refine ⟨hm₀, ?_⟩
    rw [← htarget M hm₀]
    exact hf

/-- Rank-nullity supplies the small trivial-character probability for every
row map, including those with dependent rows. -/
theorem rowKernel_reciprocal_le (A : Alphabet s →ₗ[F2] Vector r) :
    1 / (Fintype.card A.ker : ℝ) ≤ 1 / (2 : ℝ) ^ (s - r) := by
  have hk : 2 ^ (s - r) ≤ Fintype.card A.ker := by
    simpa only [Nat.card_eq_fintype_card] using binary_kernel_card_lower A
  have hk' : (2 : ℝ) ^ (s - r) ≤ (Fintype.card A.ker : ℝ) := by
    exact_mod_cast hk
  exact one_div_le_one_div_of_le (by positivity) hk'

/-- The actual independently sampled local policies obey the decoding lower
bound at every datum with a transferred good slice for its selected witness. -/
theorem observedAgreement_lower (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (hgood : GoodAdvice S labeling α (AdviceExperiment.leftObservation (ActualGame.rhs S) draw))
    (Mstar : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] Alphabet s)
    (hstar : draw.rowMap.comp Mstar = draw.rowMap.comp draw.hiddenMatrix)
    (hagreement : α / 4 ≤ transferredAgreement S labeling draw
      (normalizedResponse S labeling α hα hsmall
        (AdviceExperiment.leftObservation (ActualGame.rhs S) draw) hgood)
      (normalizedDescription S labeling α hα hsmall
        (AdviceExperiment.leftObservation (ActualGame.rhs S) draw) hgood).intercept Mstar) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (s * r) / (2 : ℝ) ^ r ≤
      observedAgreement S labeling (goodPredicate S labeling α hα hsmall) draw := by
  let q := AdviceExperiment.leftObservation (ActualGame.rhs S) draw
  let w := normalizedResponse S labeling α hα hsmall q hgood
  let u := (normalizedDescription S labeling α hα hsmall q hgood).intercept
  have hH : Module.finrank F2 draw.rowMap.ker ≤ s := by
    simpa only [Module.finrank_fin_fun] using draw.rowMap.ker.finrank_le
  have hs : 1 / (Fintype.card draw.rowMap.ker : ℝ) ≤ α / 8 :=
    (rowKernel_reciprocal_le draw.rowMap).trans hsmall.le
  have h := TransferredDecoding.actual_transferred_decoding S labeling draw.singletons
    draw.occurrences draw.positions draw.rowMap
    (AdviceFibers.observe draw.rowMap draw.hiddenMatrix) draw.complement Mstar hstar
    w.columns w.coefficient w.firstBit u α hα.le s r hH
    (normalizedResponse_dimension S labeling α hα hsmall q hgood) hs hagreement
  rw [observedAgreement_eq_private,
    chosenWitness_eq_normalizedResponse S labeling α hα hsmall _ hgood]
  exact h

end MaxCutGames.Decoder.SelectedDecoding
end

/-!
# The selected padded slice is the actual projected affine slice

After fixing row advice, the selected full-domain column equations on `Mπ` are
exactly the equations fixing `M` on the image of the selected column span under
`π`. The equivalence keeps the same maps, so both uniform sampling and affine
target equality transport without changing the chosen intercept.
-/

noncomputable section

namespace MaxCutGames.Decoder.ProjectedColumnSlice

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction MaxCutGames.Soundness
open MaxCutGames.Inverse
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

variable {k s d r : ℕ}

/-- Exact key sharing identifies the selected full table with the projected
answer table at every possible hidden matrix in this visible fiber. -/
theorem fullTable_padded (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (M : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] Alphabet s) :
    fullTable S labeling (AdviceExperiment.leftObservation (ActualGame.rhs S) draw)
        (mapEquiv k s (M.comp (AdviceExperiment.projection (ActualGame.rhs S) draw))) =
      TableKeysRestoration.projectedAnswer S k s d labeling draw.singletons
        (RawPrivateTable.supported draw.singletons (ActualGame.names S)
          draw.occurrences draw.positions) (M.prod draw.complement) := by
  unfold fullTable matrixTable
  rw [LinearEquiv.symm_apply_apply, TableKeysRestoration.projectedAnswer_pullback] ; rfl

end MaxCutGames.Decoder.ProjectedColumnSlice
end

/-! A finite experiment whose sample weights are constant on the selected
event becomes exactly uniform after conditioning on that event. The event is
allowed to have arbitrary positive mass, so this applies after the complete
visible datum and the chosen column constraints have both been fixed. -/

namespace MaxCutGames.Decoder.UniformConditioning

open Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {Ω : Type*} [Fintype Ω]

theorem sum_over_event (given : Ω → Bool) (f : Ω → ℝ) :
    (∑ x, if given x then f x else 0) = ∑ x : {x : Ω // given x = true}, f x.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun x => by simp) f

theorem probability_as_subtype_sum (μ : FiniteDistribution Ω) (given : Ω → Bool) :
    μ.probability given = ∑ x : {x : Ω // given x = true}, μ.weight x.val :=
  sum_over_event given μ.weight

theorem probability_and_as_subtype_sum (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) :
    μ.probability (fun x => given x && event x) =
      ∑ x : {x : Ω // given x = true}, if event x.val then μ.weight x.val else 0 := by
  calc
    _ = ∑ x, if given x then (if event x then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      change (if given x && event x then μ.weight x else 0) = _
      cases given x <;> cases event x <;> rfl
    _ = _ := sum_over_event given _

theorem probability_of_constant_weight (μ : FiniteDistribution Ω)
    (given : Ω → Bool) (c : ℝ) (hconstant : ∀ x, given x = true → μ.weight x = c) :
    μ.probability given = (Fintype.card {x : Ω // given x = true} : ℝ) * c := by
  rw [probability_as_subtype_sum]
  calc
    _ = ∑ _x : {x : Ω // given x = true}, c := by
      apply Finset.sum_congr rfl
      intro x _
      exact hconstant x.val x.property
    _ = _ := by simp [nsmul_eq_mul]

/-- Every remaining point receives equal conditional weight. Positivity of
the conditioning event justifies cancellation; no unconditional uniform law
on the original ambient experiment is required. -/
theorem condition_probability_uniform (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (positive : 0 < μ.probability given)
    (c : ℝ) (hconstant : ∀ x, given x = true → μ.weight x = c) :
    (μ.condition given positive).probability event =
      𝔼 x : {x : Ω // given x = true}, if event x.val then (1 : ℝ) else 0 := by
  have hp := probability_of_constant_weight μ given c hconstant
  have hc : c ≠ 0 := by
    intro hz
    rw [hp, hz, mul_zero] at positive
    exact (lt_irrefl 0) positive
  have hn : (Fintype.card {x : Ω // given x = true} : ℝ) ≠ 0 := by
    intro hz
    rw [hp, hz, zero_mul] at positive
    exact (lt_irrefl 0) positive
  rw [FiniteDistribution.probability_condition, probability_and_as_subtype_sum, hp,
    Fintype.expect_eq_sum_div_card]
  have hnum : (∑ x : {x : Ω // given x = true}, if event x.val then μ.weight x.val else 0) =
      c * ∑ x : {x : Ω // given x = true}, if event x.val then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [hconstant x.val x.property]
    cases event x.val <;> simp
  rw [hnum]
  field_simp [hc, hn]

/-- A proved bijection with the actual affine matrix slice identifies the
conditional target probability with that slice's complete uniform average. -/
theorem condition_probability_equiv {Y : Type*} [Fintype Y]
    (μ : FiniteDistribution Ω) (given event : Ω → Bool)
    (positive : 0 < μ.probability given) (c : ℝ)
    (hconstant : ∀ x, given x = true → μ.weight x = c)
    (e : {x : Ω // given x = true} ≃ Y) (target : Y → Bool)
    (hevent : ∀ x, event x.val = target (e x)) :
    (μ.condition given positive).probability event =
      𝔼 y : Y, if target y then (1 : ℝ) else 0 := by
  rw [condition_probability_uniform μ given event positive c hconstant]
  apply Fintype.expect_equiv e
  intro x
  rw [hevent x]

end
end MaxCutGames.Decoder.UniformConditioning

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_VisibleTransfer
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.VisibleTransfer

open MaxCutGames.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Ω D : Type*} [Fintype Ω] [Fintype D]

omit [Fintype D] in
theorem fiberMass_nonnegative (μ : FiniteDistribution Ω) (observe : Ω → D)
    (d : D) (event : Ω → Bool) : 0 ≤ fiberMass μ observe d event :=
  μ.probability_nonnegative _

omit [Fintype D] in
theorem fiberMass_mono (μ : FiniteDistribution Ω) (observe : Ω → D)
    (d : D) {event event' : Ω → Bool}
    (h : ∀ x, event x = true → event' x = true) :
    fiberMass μ observe d event ≤ fiberMass μ observe d event' := by
  apply μ.probability_mono
  intro x hx
  simp only [fiberEvent, Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
  exact ⟨hx.1, h x hx.2⟩

theorem sum_fiberMass (μ : FiniteDistribution Ω) (observe : Ω → D)
    (event : Ω → Bool) :
    ∑ d, fiberMass μ observe d event = μ.probability event := by
  classical
  unfold fiberMass FiniteDistribution.probability fiberEvent
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases event x <;> simp

theorem observation_weight (μ : FiniteDistribution Ω) (observe : Ω → D) (d : D) :
    (μ.pushforward observe).weight d = fiberMass μ observe d (fun _ => true) := by
  classical
  simp [FiniteDistribution.pushforward, fiberMass, FiniteDistribution.probability,
    fiberEvent]

/-- The positive part of the witness margin is paid for by the probability of
the actual observed data, rather than by the larger hidden sample space. -/
theorem witness_margin_le_visible_probability
    (μ : FiniteDistribution Ω) (observe : Ω → D)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    μ.probability (fun x => slice x && targetHit x) - threshold * μ.probability slice ≤
      (μ.pushforward observe).probability (visibleWitness μ observe slice targetHit threshold) := by
  classical
  have pointwise (d : D) :
      fiberMass μ observe d (fun x => slice x && targetHit x) -
          threshold * fiberMass μ observe d slice ≤
        if visibleWitness μ observe slice targetHit threshold d then
          (μ.pushforward observe).weight d else 0 := by
    have hs := fiberMass_nonnegative μ observe d slice
    have hm := fiberMass_nonnegative μ observe d (fun x => slice x && targetHit x)
    have hms : fiberMass μ observe d (fun x => slice x && targetHit x) ≤
        fiberMass μ observe d slice := by
      apply fiberMass_mono
      intro x hx
      simp only [Bool.and_eq_true] at hx
      exact hx.1
    have hmo : fiberMass μ observe d (fun x => slice x && targetHit x) ≤
        (μ.pushforward observe).weight d := by
      rw [observation_weight]
      exact fiberMass_mono μ observe d (fun _ _ => rfl)
    by_cases hgood : visibleWitness μ observe slice targetHit threshold d = true
    · simp only [hgood, ↓reduceIte]
      exact (sub_le_self _ (mul_nonneg hthreshold hs)).trans hmo
    · simp only [hgood, Bool.false_eq_true, ↓reduceIte]
      by_cases hpos : 0 < fiberMass μ observe d slice
      · have hnot : ¬ threshold * fiberMass μ observe d slice ≤
            fiberMass μ observe d (fun x => slice x && targetHit x) := by
          intro hle
          exact hgood (by simp [visibleWitness, hpos, hle])
        linarith
      · have hzero : fiberMass μ observe d slice = 0 := le_antisymm (le_of_not_gt hpos) hs
        rw [hzero, mul_zero, sub_zero]
        exact hms.trans_eq hzero
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun d _ => pointwise d
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_fiberMass,
    FiniteDistribution.probability] using hsum

omit [Fintype D] in
/-- On every selected datum the conditional distribution is defined on an
actual nonempty positive-mass slice and has the promised target agreement. -/
theorem visibleWitness_conditional
    (μ : FiniteDistribution Ω) (observe : Ω → D)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (d : D)
    (h : visibleWitness μ observe slice targetHit threshold d = true) :
    ∃ hpositive : 0 < μ.probability (fiberEvent observe d slice),
      threshold ≤ (μ.condition (fiberEvent observe d slice) hpositive).probability targetHit := by
  classical
  have hh : 0 < fiberMass μ observe d slice ∧
      threshold * fiberMass μ observe d slice ≤
        fiberMass μ observe d (fun x => slice x && targetHit x) := by
    simpa only [visibleWitness, decide_eq_true_eq] using h
  unfold fiberMass at hh
  refine ⟨hh.1, ?_⟩
  rw [FiniteDistribution.probability_condition]
  have hsame : (fun x => fiberEvent observe d slice x && targetHit x) =
      fiberEvent observe d (fun x => slice x && targetHit x) := by
    funext x
    simp [fiberEvent, Bool.and_assoc]
  rw [hsame]
  exact (le_div_iff₀ hh.1).mpr hh.2

/-- A pair of full-table event probabilities transfers with error
`(1 + threshold) * TV`. This estimate precedes all conditioning. -/
theorem margin_transfer (μ ν : FiniteDistribution Ω)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    μ.probability (fun x => slice x && targetHit x) - threshold * μ.probability slice -
        (1 + threshold) * μ.totalVariation ν ≤
      ν.probability (fun x => slice x && targetHit x) - threshold * ν.probability slice := by
  have hm := μ.probability_sub_le_totalVariation ν (fun x => slice x && targetHit x)
  have hs := ν.probability_sub_le_totalVariation μ slice
  rw [FiniteDistribution.totalVariation_comm] at hs
  have hscaled := mul_le_mul_of_nonneg_left hs hthreshold
  nlinarith

/-- The whole-table comparison and the exact finite disintegration combine
without any assumption on conditional projection laws. -/
theorem wholeTable_transfer_to_visibleWitness
    {Γ : Type*} [Fintype Γ]
    (unrestricted : FiniteDistribution Ω) (actual : FiniteDistribution Γ)
    (pad : Γ → Ω) (observe : Γ → D) (slice targetHit : Ω → Bool)
    (threshold γ : ℝ) (hthreshold : 0 ≤ threshold)
    (hmargin : γ ≤
      unrestricted.probability (fun x => slice x && targetHit x) -
        threshold * unrestricted.probability slice -
        (1 + threshold) * unrestricted.totalVariation (actual.pushforward pad)) :
    γ ≤ (actual.pushforward observe).probability
      (visibleWitness actual observe (fun x => slice (pad x))
        (fun x => targetHit (pad x)) threshold) := by
  have transferred := margin_transfer unrestricted (actual.pushforward pad)
    slice targetHit threshold hthreshold
  simp only [FiniteDistribution.probability_pushforward] at transferred
  exact (hmargin.trans transferred).trans
    (witness_margin_le_visible_probability actual observe
      (fun x => slice (pad x)) (fun x => targetHit (pad x)) threshold hthreshold)

theorem projected_witness_mass
    {Γ : Type*} [Fintype Γ]
    (unrestricted : FiniteDistribution Ω) (actual : FiniteDistribution Γ)
    (pad : Γ → Ω) (observe : Γ → D) (slice targetHit : Ω → Bool)
    (α g₀ c : ℝ) (hα : 0 ≤ α)
    (hslice : g₀ * c ≤ unrestricted.probability slice)
    (hagreement : (α / 2) * unrestricted.probability slice ≤
      unrestricted.probability (fun x => slice x && targetHit x))
    (herror : (1 + α / 4) * unrestricted.totalVariation (actual.pushforward pad) ≤
      α * g₀ * c / 8) :
    α * g₀ * c / 8 ≤ (actual.pushforward observe).probability
      (visibleWitness actual observe (fun x => slice (pad x))
        (fun x => targetHit (pad x)) (α / 4)) := by
  apply wholeTable_transfer_to_visibleWitness unrestricted actual pad observe slice targetHit
    (α / 4) (α * g₀ * c / 8) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hslice (show 0 ≤ α / 4 by positivity)
  nlinarith

end
end MaxCutGames.Decoder.VisibleTransfer

namespace MaxCutGames.Decoder.UniformFibers

open Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {Ω D Y : Type*}

theorem selectedFiberEquiv_point (observe : Ω → D) (d : D) (slice : Ω → Bool)
    (e : Y ≃ {x : Ω // observe x = d})
    (x : {x : Ω // VisibleTransfer.fiberEvent observe d slice x = true}) :
    (e (selectedFiberEquiv observe d slice e x).val).val = x.val := by
  exact congrArg Subtype.val (e.apply_symm_apply _)

/-- Conditioning after fixing the complete datum and the selected column
event leaves precisely the uniform restricted private fiber. -/
theorem conditional_probability [Fintype Ω] [Fintype Y]
    (μ : FiniteDistribution Ω) (observe : Ω → D) (d : D)
    (slice event : Ω → Bool)
    (positive : 0 < μ.probability (VisibleTransfer.fiberEvent observe d slice))
    (c : ℝ) (hconstant : ∀ x, observe x = d → μ.weight x = c)
    (e : Y ≃ {x : Ω // observe x = d}) :
    (μ.condition (VisibleTransfer.fiberEvent observe d slice) positive).probability event =
      𝔼 y : {y : Y // slice (e y).val = true},
        if event (e y.val).val then (1 : ℝ) else 0 := by
  apply UniformConditioning.condition_probability_equiv μ
    (VisibleTransfer.fiberEvent observe d slice) event positive c
    (fun x hx => hconstant x (by
      have h : observe x = d ∧ slice x = true := by
        simpa only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq] using hx
      exact h.1))
    (selectedFiberEquiv observe d slice e)
    (fun y => event (e y.val).val)
  intro x
  rw [selectedFiberEquiv_point]

end
end MaxCutGames.Decoder.UniformFibers

/-! The complete-data conditional law of the actual projected experiment.
The residual private matrix is uniform even when the occurrence law is
weighted and the public row map has deficient rank. -/

namespace MaxCutGames.Decoder.ActualConditionalLaw

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

section Conditioning

variable {k : ℕ} {Id K W R : Type}
    [Fintype Id] [AddCommGroup K] [Module F2 K] [Fintype K]
    [AddCommGroup W] [Module F2 W] [Fintype W]
    [AddCommGroup R] [Module F2 R] [Fintype R]

attribute [local instance] OAI.MaxCutGames.Decoder.ActualConditionalLaw.homFintype
theorem probability_condition_complete
    (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (d : AdviceLaw.CompleteData k Id K W R)
    (slice event : AdviceLaw.FullSeed k Id K W R → Bool)
    (positive : 0 < (AdviceLaw.fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').probability
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve d slice)) :
    ((AdviceLaw.fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').condition
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve d slice) positive).probability event =
        𝔼 N : {N : AdviceLaw.PrivateMap d // slice (AdviceLaw.completeAssemble d N) = true},
          if event (AdviceLaw.completeAssemble d N.val) then (1 : ℝ) else 0 := by
  exact UniformFibers.conditional_probability
    (AdviceLaw.fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ')
    AdviceLaw.completeObserve d slice event positive
    (AdviceLaw.completeWeight occurrences publicLaw β d)
    (AdviceLaw.fullSeed_weight_fiber occurrences publicLaw β hβ hβ' d)
    (AdviceLaw.completeFiberEquiv d)

end Conditioning

variable {k s d r : ℕ}

attribute [local instance] OAI.MaxCutGames.Decoder.ActualConditionalLaw.homFintype
/-- Both provers' answers, and their equality predicate, are fixed on the
complete observation fiber. Only the hidden matrix varies within that fiber. -/
theorem observedAgreement_completeDraw (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (data : AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (N N' : AdviceLaw.PrivateMap data) :
    VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw data N) =
      VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw data N') := by
  unfold VisiblePolicies.observedAgreement
  rw [AdviceLaw.completeDraw_left, AdviceLaw.completeDraw_left]
  simp only [AdviceExperiment.rightObservation, AdviceLaw.completeDraw_rows]
  rfl

theorem datumAgreement_nonneg (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (data : AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)) :
    0 ≤ datumAgreement S labeling good data :=
  FiniteDistribution.probability_nonnegative _ _

/-- The actual success observable factors through the complete visible datum;
this justifies integrating a lower bound over visible-witness probability. -/
theorem observedAgreement_seed (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (x : AdviceLaw.FullSeed k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)) :
    VisiblePolicies.observedAgreement S labeling good
      (AdviceLaw.seedToActualDraw x.1.1 x.1.2 x.2) =
        datumAgreement S labeling good (AdviceLaw.completeObserve x) := by
  let y := AdviceLaw.fullSeedCoordinatesEquiv x
  have hx : AdviceLaw.completeAssemble y.1 y.2 = x :=
    AdviceLaw.fullSeedCoordinatesEquiv.symm_apply_apply x
  rw [← hx, AdviceLaw.completeDraw_seed]
  change VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw y.1 y.2) =
    datumAgreement S labeling good (AdviceLaw.completeObserve (AdviceLaw.completeAssemble y.1 y.2))
  rw [AdviceLaw.completeObserve_assemble]
  exact observedAgreement_completeDraw S labeling good y.1 y.2 0

end
end MaxCutGames.Decoder.ActualConditionalLaw

/-!
# Actual conditional selected-fiber agreement

The selected event is the full-table event used by the total-variation
comparison. On a positive complete-data fiber it becomes the uniform actual
affine row/column slice. The selector is fixed by the left observation; the
extra complete data and a supporting matrix occur only in this analysis.
-/

noncomputable section

namespace MaxCutGames.Decoder.SelectedFiberLaw

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction MaxCutGames.Soundness
open MaxCutGames.Inverse MaxCutGames.Foundations.Games
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates ActualSeedEvents
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

/-- The universe finset is independent of the chosen finite enumeration.
The instances are explicit so elaboration need not unfold either enumeration. -/
private theorem univ_congr_inline_SelectedFiberLaw {X : Type*} (i j : Fintype X) :
    @Finset.univ X i = @Finset.univ X j := by
  cases Subsingleton.elim i j
  rfl

private theorem condition_prob_enumeration {Ω : Type} (i j : Fintype Ω)
    (μ : @FiniteDistribution Ω i) (ν : @FiniteDistribution Ω j)
    (hw : ∀ x, @FiniteDistribution.weight Ω i μ x = @FiniteDistribution.weight Ω j ν x) (slice event : Ω → Bool)
    (hm : 0 < @FiniteDistribution.probability Ω i μ slice)
    (hn : 0 < @FiniteDistribution.probability Ω j ν slice) :
    @FiniteDistribution.probability Ω i (@FiniteDistribution.condition Ω i μ slice hm) event =
      @FiniteDistribution.probability Ω j (@FiniteDistribution.condition Ω j ν slice hn) event := by
  cases Subsingleton.elim i j
  let : Fintype Ω := i
  have he : μ = ν := FiniteDistribution.eq_of_weight_eq hw
  subst ν
  rfl

variable {k s d r : ℕ}

attribute [local instance] OAI.MaxCutGames.Decoder.SelectedFiberLaw.homFintype
/-- On the selected event, the actual full-table target-hit predicate equals
projected affine equality with the very same normalized coefficient/intercept. -/
theorem target_assemble_iff (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (N : AdviceLaw.PrivateMap data)
    (hN : slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true) :
    targetHit S k s d r labeling α (AdviceLaw.completeAssemble data N) = true ↔
      TableKeysRestoration.projectedAnswer S k s d labeling (PaddedLaw.choiceMask data.2.1)
        (RawPrivateTable.supported (PaddedLaw.choiceMask data.2.1) (ActualGame.names S)
          data.1.1 (PaddedLaw.choiceSlots data.2.1)) ((datumMatrix S data N).prod data.2.2.1) =
        datumMatrix S data N (datumProjection S data
          (normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).coefficient) +
          (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).intercept := by
  have hp := (slice_assemble_iff S labeling α hα hsmall data hgood N).mp hN
  rw [targetHit_eq_selectedMatch]
  change decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch
      (fullTable S labeling (AdviceExperiment.leftObservation (ActualGame.rhs S)
        (AdviceLaw.completeDraw data N))) α (LinearMap.toMatrix' data.1.2)
      (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)))) = true ↔ _
  rw [datumLeft_eq, decide_eq_true_eq]
  refine (SelectedDecoding.selectedMatch_iff_normalized S labeling α hα hsmall
    (datumLeft S data) hgood _ (datumMatrix_rowAdvice S data N)).trans ?_
  have hp' : mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)) ∈
      (RowErasureMatrix.family s (1 + 2 * k) r).points
        (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood) := hp
  simp only [hp', true_and, LinearEquiv.symm_apply_apply]
  rw [show fullTable S labeling (datumLeft S data)
      (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data))) =
      TableKeysRestoration.projectedAnswer S k s d labeling (PaddedLaw.choiceMask data.2.1)
        (RawPrivateTable.supported (PaddedLaw.choiceMask data.2.1) (ActualGame.names S)
          data.1.1 (PaddedLaw.choiceSlots data.2.1)) ((datumMatrix S data N).prod data.2.2.1) from
    ProjectedColumnSlice.fullTable_padded S labeling (AdviceLaw.completeDraw data 0) (datumMatrix S data N)] ; rfl

/-- Positive mass supplies a supporting private coordinate in the selected
fiber; neither a hidden matrix nor good advice is an additional premise. -/
theorem exists_selected_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (data : Datum S k s d r)
    (positive : 0 < (law S k s d r β hβ hβ').probability
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α))) :
    ∃ N : AdviceLaw.PrivateMap data,
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true := by
  have hex : ∃ x : Seed S k s d r,
      VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α) x = true := by
    by_contra hn
    have he : VisibleTransfer.fiberEvent AdviceLaw.completeObserve data
        (slice S k s d r labeling α) = fun _ => false := by
      funext x
      apply Bool.eq_false_iff.mpr
      intro hx
      exact hn ⟨x, hx⟩
    rw [he, FiniteDistribution.probability_false] at positive
    exact (lt_irrefl 0) positive
  obtain ⟨x, hx⟩ := hex
  have hx' : AdviceLaw.completeObserve x = data ∧ slice S k s d r labeling α x = true := by
    simpa only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq] using hx
  let N := (AdviceLaw.completeFiberEquiv data).symm ⟨x, hx'.1⟩
  have he : AdviceLaw.completeAssemble data N = x :=
    congrArg Subtype.val ((AdviceLaw.completeFiberEquiv data).apply_symm_apply ⟨x, hx'.1⟩)
  exact ⟨N, he.symm ▸ hx'.2⟩

theorem good_of_selected_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data)
    (hN : slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true) :
    GoodAdvice S labeling α (datumLeft S data) := by
  have hg := slice_good S k s d r labeling α (AdviceLaw.completeAssemble data N) hN
  change GoodAdvice S labeling α
    (AdviceExperiment.leftObservation (ActualGame.rhs S) (AdviceLaw.completeDraw data N)) at hg
  rw [datumLeft_eq] at hg
  exact hg

/-- Exact conditional target probability, with no assumed uniformity premise. -/
theorem conditional_eq_transferred (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (Nstar : AdviceLaw.PrivateMap data)
    (hstar : slice S k s d r labeling α (AdviceLaw.completeAssemble data Nstar) = true)
    (positive : 0 < (law S k s d r β hβ hβ').probability
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α))) :
    ((law S k s d r β hβ hβ').condition
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α))
        positive).probability (targetHit S k s d r labeling α) =
      SelectedDecoding.transferredAgreement S labeling (AdviceLaw.completeDraw data 0)
        (normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood)
        (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).intercept
        (datumMatrix S data Nstar) := by
  let : Fintype (Fin S.occurrences) := Fin.fintype _
  let : Fintype (Alphabet s) := @Pi.instFintype (Fin s) (fun _ => F2) (instDecidableEqFin s) (Fin.fintype s) (fun _ => ZMod.fintype 2)
  let : Fintype (Vector d) := @Pi.instFintype (Fin d) (fun _ => F2) (instDecidableEqFin d) (Fin.fintype d) (fun _ => ZMod.fintype 2)
  let : Fintype (Vector r) := @Pi.instFintype (Fin r) (fun _ => F2) (instDecidableEqFin r) (Fin.fintype r) (fun _ => ZMod.fintype 2)
  let : Fintype (Alphabet s →ₗ[F2] Vector r) := ActualConditionalLaw.homFintype
  unfold law at positive ⊢
  have hconditional := ActualConditionalLaw.probability_condition_complete
    (k := k) (Id := Fin S.occurrences) (K := Alphabet s) (W := Vector d) (R := Vector r)
    (FiniteDistribution.uniform (ActualGame.Question S k))
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)) β hβ hβ' data
    (slice S k s d r labeling α) (targetHit S k s d r labeling α) (by
      convert positive using 1
      all_goals try with_reducible_and_instances rfl
      simp only [FiniteDistribution.probability,
        AdviceLaw.fullSeedLaw, FiniteDistribution.product, FiniteDistribution.uniform,
        ← Nat.card_eq_fintype_card]
      apply Finset.sum_congr (univ_congr_inline_SelectedFiberLaw _ _)
      intro x hx
      rfl)
  refine Eq.trans ?_ (hconditional.trans ?_)
  · apply condition_prob_enumeration
    intro x
    simp only [AdviceLaw.fullSeedLaw, FiniteDistribution.product, FiniteDistribution.uniform,
      ← Nat.card_eq_fintype_card]
  ·
    let : Fintype (RawPartnerTarget.RawPoint (PaddedLaw.choiceMask data.2.1) →ₗ[F2] Alphabet s) :=
      homFintype
    let : Fintype (RowErasureSliceQuotient.AffineSlice data.1.2
        ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
          (datumProjection S data)) (datumMatrix S data Nstar)) :=
      SelectedDecoding.affineSliceFintype _ _ _
    let f : {N : AdviceLaw.PrivateMap data //
        slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true} → ℝ :=
      fun N => if targetHit S k s d r labeling α (AdviceLaw.completeAssemble data N.val) = true
        then 1 else 0
    let g : RowErasureSliceQuotient.AffineSlice data.1.2
        ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
          (datumProjection S data)) (datumMatrix S data Nstar) → ℝ :=
      fun M => if TableKeysRestoration.projectedAnswer S k s d labeling
          (PaddedLaw.choiceMask data.2.1)
          (RawPrivateTable.supported (PaddedLaw.choiceMask data.2.1) (ActualGame.names S)
            data.1.1 (PaddedLaw.choiceSlots data.2.1)) (M.val.prod data.2.2.1) =
          M.val (datumProjection S data
            (normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).coefficient) +
            (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).intercept
        then 1 else 0
    have he : (𝔼 N, f N) = 𝔼 M, g M := by
      refine Fintype.expect_equiv
        (selectedPrivateEquiv S labeling α hα hsmall data hgood Nstar hstar) f g ?_
      intro N
      dsimp only [f, g]
      simp only [selectedPrivateEquiv_val]
      exact TransferredDecoding.indicator_congr _ _ _ _
        (target_assemble_iff S labeling α hα hsmall data hgood N.val N.property)
    calc
      _ = 𝔼 N, f N := by
        apply Finset.expect_congr (by ext N; simp only [Finset.mem_univ])
        intro N _
        exact TransferredDecoding.indicator_congr _ _ _ _ Iff.rfl
      _ = 𝔼 M, g M := he
      _ = _ := by
        unfold SelectedDecoding.transferredAgreement
        apply Finset.expect_congr (univ_congr_inline_SelectedFiberLaw _ _)
        intro M _
        exact TransferredDecoding.indicator_congr _ _ _ _ Iff.rfl

/-- Every complete visible datum selected by the actual witness event pays the
private-decoding success constant. Good advice and a nonempty transferred
slice follow from positivity and are not additional hypotheses. -/
theorem visibleWitness_decoding (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (data : Datum S k s d r)
    (hvisible : VisibleTransfer.visibleWitness (law S k s d r β hβ hβ')
      AdviceLaw.completeObserve (slice S k s d r labeling α)
      (targetHit S k s d r labeling α) (α / 4) data = true) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (s * r) / (2 : ℝ) ^ r ≤
      ActualConditionalLaw.datumAgreement S labeling (goodPredicate S labeling α hα hsmall) data := by
  obtain ⟨positive, hagree⟩ := VisibleTransfer.visibleWitness_conditional
    (law S k s d r β hβ hβ') AdviceLaw.completeObserve
    (slice S k s d r labeling α) (targetHit S k s d r labeling α) (α / 4) data hvisible
  obtain ⟨Nstar, hstar⟩ := exists_selected_private S labeling α β hβ hβ' data positive
  have hgood := good_of_selected_private S labeling α data Nstar hstar
  rw [conditional_eq_transferred S labeling α hα hsmall β hβ hβ' data hgood Nstar hstar positive] at hagree
  apply SelectedDecoding.observedAgreement_lower S labeling α hα hsmall
    (AdviceLaw.completeDraw data 0) hgood (datumMatrix S data Nstar) ?_ hagree
  exact (datumMatrix_rows S data Nstar).trans (datumMatrix_rows S data 0).symm

end MaxCutGames.Decoder.SelectedFiberLaw
end

/-! The full selected-witness argument on the actual projected experiment.
The variation comparison precedes all conditioning. Its visible event then
pays the independent private decoder success on every selected datum. -/

namespace MaxCutGames.Decoder.ActualProjectedTransfer

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

local instance homFintype_r7c257f_2 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
/-- The actual complete-data event has positive mass depending only on the
fixed inverse and alphabet parameters. -/
theorem visible_mass (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : slopeVariation k s d β ≤ ConstantSelection.variationBudget α g₀ s r) :
    ConstantSelection.visibleMass α g₀ s r ≤
      ((ActualSeedEvents.law S k s d r β hβ hβ').pushforward AdviceLaw.completeObserve).probability
        (VisibleTransfer.visibleWitness (ActualSeedEvents.law S k s d r β hβ hβ')
          AdviceLaw.completeObserve (ActualSeedEvents.slice S k s d r labeling α)
          (ActualSeedEvents.targetHit S k s d r labeling α) (α / 4)) := by
  have htv := (ActualSeedVariation.actual_totalVariation_le_slope S k s d r β hβ hβ').trans hvariation
  have h := VisibleTransfer.projected_witness_mass
    (ActualEvents.unrestricted S k s d r) (ActualSeedEvents.law S k s d r β hβ hβ')
    (ActualSeedEvents.pad S k s d r) AdviceLaw.completeObserve
    (ActualEvents.sliceEvent S k s d r labeling α) (ActualEvents.targetHit S k s d r labeling α)
    α g₀ (1 / (2 : ℝ) ^ (s * r)) hα.le
    (ActualEvents.slice_probability_lower S k s d r labeling α g₀ hgood)
    (ActualEvents.target_probability_lower S k s d r labeling α)
    (ConstantSelection.variationBudget_suffices hα s r htv)
  have hc : α * g₀ * (1 / (2 : ℝ) ^ (s * r)) / 8 =
      ConstantSelection.visibleMass α g₀ s r := by
    unfold ConstantSelection.visibleMass
    ring
  rw [hc] at h
  exact h

/-- Integrating a pointwise lower bound over a genuine probability event. -/
theorem event_expectation_lower {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (event : Ω → Bool) (f : Ω → ℝ)
    (γ₁ γ₂ : ℝ) (hγ₂ : 0 ≤ γ₂) (hf : ∀ x, 0 ≤ f x)
    (hmass : γ₁ ≤ μ.probability event)
    (hpoint : ∀ x, event x = true → γ₂ ≤ f x) :
    γ₁ * γ₂ ≤ μ.expectation f := by
  have hweighted : μ.probability event * γ₂ ≤ μ.expectation f := by
    unfold FiniteDistribution.probability FiniteDistribution.expectation
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : event x = true
    · simp only [hx, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left (hpoint x hx) (μ.nonnegative x)
    · simp only [hx, Bool.false_eq_true, ↓reduceIte, zero_mul]
      exact mul_nonneg (μ.nonnegative x) (hf x)
  exact (mul_le_mul_of_nonneg_right hmass hγ₂).trans hweighted

/-- End-to-end lower bound for actual local stochastic responses. No hidden
matrix, selected witness, or opposing observation is passed to a prover. -/
theorem actual_success_lower_oai (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α)
    (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : slopeVariation k s d β ≤ ConstantSelection.variationBudget α g₀ s r) :
    ConstantSelection.decodingMass α g₀ s r ≤
      (ActualSeedEvents.law S k s d r β hβ hβ').expectation
        (fun seed => VisiblePolicies.observedAgreement S labeling
          (SelectedPolicies.goodPredicate S labeling α hα hsmall)
          (AdviceLaw.seedToActualDraw seed.1.1 seed.1.2 seed.2)) := by
  let μ := ActualSeedEvents.law S k s d r β hβ hβ'
  let good := SelectedPolicies.goodPredicate S labeling α hα hsmall
  have h := event_expectation_lower (μ.pushforward AdviceLaw.completeObserve)
    (VisibleTransfer.visibleWitness μ AdviceLaw.completeObserve
      (ActualSeedEvents.slice S k s d r labeling α)
      (ActualSeedEvents.targetHit S k s d r labeling α) (α / 4))
    (ActualConditionalLaw.datumAgreement S labeling good)
    (ConstantSelection.visibleMass α g₀ s r) (ConstantSelection.conditionalMass α s r)
    (ConstantSelection.conditionalMass_pos hα s r).le
    (ActualConditionalLaw.datumAgreement_nonneg S labeling good)
    (visible_mass S labeling α g₀ β hα hβ hβ' hgood hvariation)
    (SelectedFiberLaw.visibleWitness_decoding S labeling α hα hsmall β hβ hβ')
  rw [FiniteDistribution.expectation_pushforward] at h
  unfold ConstantSelection.decodingMass
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply FiniteDistribution.expectation_congr
  intro seed
  exact ActualConditionalLaw.observedAgreement_seed S labeling good seed

end
end MaxCutGames.Decoder.ActualProjectedTransfer

end OAI
end

theorem solution : type_of% @OAI.MaxCutGames.Decoder.ActualProjectedTransfer.actual_success_lower_oai := @OAI.MaxCutGames.Decoder.ActualProjectedTransfer.actual_success_lower_oai
