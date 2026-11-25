-- Prove2me | solution 1 for GlobalTheory.finite_pullback_over_closedPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:06:12.57526+00:00
-- url     : https://prove2.me/submissions/4885a9bd-b510-40b9-8ad3-7f0150299dad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Z P : Scheme.{0}} (π : X ⟶ Sp ℤ)
    [LocallyOfFiniteType π] (s : X ⟶ Z) (t : P ⟶ Z) (σ : X) (hσ : IsClosed ({σ} : Set X))
    {F : Set P} (hF : F.Finite) :
    {w : ↑(pullback s t) | pullback.fst s t w = σ ∧ pullback.snd s t w ∈ F}.Finite := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hσ
  let i := X.fromSpecResidueField σ
  have h1 : LocallyOfFiniteType ((i ≫ s) ≫ specZIsTerminal.from Z) := by
    rw [specZIsTerminal.hom_ext ((i ≫ s) ≫ specZIsTerminal.from Z) (i ≫ π)]
    infer_instance
  have h2 : LocallyOfFiniteType (i ≫ s) := locallyOfFiniteType_of_comp _ (specZIsTerminal.from Z)
  have h3 : LocallyQuasiFinite (i ≫ s) :=
    .of_injective (Function.injective_of_subsingleton _)
  have h4 : QuasiCompact (i ≫ s) := ⟨fun U _ _ ↦ (Set.toFinite _).isCompact⟩
  have H := (IsPullback.of_hasPullback (pullback.fst s t) i).paste_horiz
    (IsPullback.of_hasPullback s t).flip
  have h5 : LocallyQuasiFinite (pullback.fst (pullback.fst s t) i ≫ pullback.snd s t) :=
    MorphismProperty.of_isPullback H.flip h3
  have h6 : QuasiCompact (pullback.fst (pullback.fst s t) i ≫ pullback.snd s t) :=
    MorphismProperty.of_isPullback H.flip h4
  refine (((pullback.fst (pullback.fst s t) i ≫ pullback.snd s t).finite_preimage hF).image
    (pullback.fst (pullback.fst s t) i)).subset ?_
  rintro w ⟨hw, hw'⟩
  have : w ∈ Set.range (pullback.fst (pullback.fst s t) i) := by
    rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
    exact hw
  obtain ⟨v, rfl⟩ := this
  exact ⟨v, by simpa using hw', rfl⟩
end GlobalTheory
