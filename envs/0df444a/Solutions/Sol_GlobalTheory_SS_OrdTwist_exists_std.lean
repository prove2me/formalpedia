-- Prove2me | solution 1 for GlobalTheory.SS.OrdTwist.exists_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:41:07.377854+00:00
-- url     : https://prove2.me/submissions/f37ac227-974f-4397-8fbf-383e31785562

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyAutomorphismShiftsJacobianOrder
import Theorems.Thm_GlobalTheory_SS_OrdTwist_rs_cstK

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
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdTwist
variable {K : Type} [Field K] {A : Over (Sp K)} {I : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.SS.OrdTwist
theorem _root_.solution {n : ℕ} (hA : SmoothOfRelativeDimension n A.hom) (U : A.left.Opens) (x : A.left) (hx : x ∈ U) :
    ∃ V : A.left.Opens, V ≤ U ∧ x ∈ V ∧ (cstK A V).IsStandardSmoothOfRelativeDimension n := by
  obtain ⟨W, -, V, hV, hxV, e, hf⟩ := hA.exists_isStandardSmoothOfRelativeDimension x
  obtain rfl : W = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    have : y = A.hom x := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact e hxV
  obtain ⟨g, hgU, hxg⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ hxV
  refine ⟨A.left.basicOpen g, hgU, hxg, ?_⟩
  have := hV.isLocalization_basicOpen g
  have h1 : (algebraMap Γ(A.left, V) Γ(A.left, A.left.basicOpen g)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway g
  have h2 : (cstK A V).IsStandardSmoothOfRelativeDimension n :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv hf
  have h3 := h1.comp h2
  rw [zero_add] at h3
  convert h3 using 1
  ext c
  exact (rs_cstK _ c).symm
end GlobalTheory.SS.OrdTwist
