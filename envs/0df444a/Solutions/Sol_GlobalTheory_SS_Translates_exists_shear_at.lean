-- Prove2me | solution 1 for GlobalTheory.SS.Translates.exists_shear_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:57:14.514358+00:00
-- url     : https://prove2.me/submissions/b69d0f4b-cad9-48f7-a5a4-80098325b924

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatible
import Theorems.Thm_GlobalTheory_SS_Translates_isoAt_iff
import Theorems.Thm_GlobalTheory_SS_Translates_exists_right_slice

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Translates
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
variable [GrpObj A] [IsCommMonObj A]
namespace GlobalTheory.SS.Translates
theorem _root_.solution [IsLocalRing R] {M : Model R A} (hM : Strict M) (s : 𝟙_ (Over (Sp R)) ⟶ M.Y) :
    ∃ (X : Scheme.{0}) (I G : X ⟶ (M.Y ⊗ M.Y).left) (o : X) (w : M.Y.left), IsOpenImmersion I ∧ IsOpenImmersion G ∧
      Ext (M.prod M) (M.prod M) (shear A true) I G ∧ w ∈ M.sp ∧ I o = (lift (𝟙 M.Y) (toUnit M.Y ≫ s)).left w := by
  have h3 : s.left ≫ M.Y.hom = 𝟙 (Sp R) := Over.w s
  obtain ⟨z, hz, h⟩ := (hM.2 true (s.left (IsLocalRing.closedPoint R)) congr($h3 (IsLocalRing.closedPoint R))).2
  obtain ⟨X, I, G, o, hI, hG, he, ho⟩ := isoAt_iff.1 h
  obtain ⟨w, hw, hw'⟩ := exists_right_slice M s _ z hz
  exact ⟨X, I, G, o, w, hI, hG, he, hw', ho.trans hw.symm⟩
end GlobalTheory.SS.Translates
