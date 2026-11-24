-- Prove2me | solution 1 for GlobalTheory.SS.Translates.exists_right_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:24:40.907354+00:00
-- url     : https://prove2.me/submissions/d7a8e250-358a-43ac-83b8-f4dfb4315c85

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
namespace GlobalTheory.SS.Translates
theorem _root_.solution (M : Model R A) (s : 𝟙_ (Over (Sp R)) ⟶ M.Y) (c : Sp R) (z : (M.Y ⊗ M.Y).left)
    (hz : (snd M.Y M.Y).left z = s.left c) :
    ∃ w, (lift (𝟙 M.Y) (toUnit M.Y ≫ s)).left w = z ∧ M.Y.hom w = c := by
  have h1 : (lift (𝟙 M.Y) (toUnit M.Y ≫ s)).left ≫ pullback.fst M.Y.hom M.Y.hom = 𝟙 _ :=
    congr(($(lift_fst (𝟙 M.Y) (toUnit M.Y ≫ s))).left)
  have h2 : (lift (𝟙 M.Y) (toUnit M.Y ≫ s)).left ≫ pullback.snd M.Y.hom M.Y.hom = M.Y.hom ≫ s.left :=
    congr(($(lift_snd (𝟙 M.Y) (toUnit M.Y ≫ s))).left)
  have h3 : s.left ≫ M.Y.hom = 𝟙 (Sp R) := Over.w s
  have hp : IsPullback (lift (𝟙 M.Y) (toUnit M.Y ≫ s)).left M.Y.hom (pullback.snd M.Y.hom M.Y.hom) s.left := by
    refine IsPullback.of_right ?_ h2 (IsPullback.of_hasPullback M.Y.hom M.Y.hom)
    rw [h1, h3]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd M.Y.hom M.Y.hom) (g := s.left) z c hz
  refine ⟨hp.isoPullback.inv p, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hp.isoPullback_inv_fst, hp1]
  · rw [← Scheme.Hom.comp_apply, hp.isoPullback_inv_snd, hp2]
end GlobalTheory.SS.Translates
