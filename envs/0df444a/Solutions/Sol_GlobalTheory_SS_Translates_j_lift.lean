-- Prove2me | solution 1 for GlobalTheory.SS.Translates.j_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:56:03.034416+00:00
-- url     : https://prove2.me/submissions/40f1d3ac-cd79-41fb-88ce-caa9b2df2bc8

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
import Theorems.Thm_GlobalTheory_SS_Translates_pj_fst
import Theorems.Thm_GlobalTheory_SS_Translates_pj_snd

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
theorem _root_.solution (M : Model R A) (u v : M.Y ⟶ M.Y) (u' v' : A ⟶ A) (hu : M.j ≫ u.left = u'.left ≫ M.j)
    (hv : M.j ≫ v.left = v'.left ≫ M.j) : M.j ≫ (lift u v).left = (lift u' v').left ≫ pj M M := by
  have h1 : (M.j ≫ (lift u v).left) ≫ (fst M.Y M.Y).left = ((lift u' v').left ≫ pj M M) ≫ (fst M.Y M.Y).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_fst, hu, pj_fst, ← Category.assoc, ← Over.comp_left, lift_fst]
  have h2 : (M.j ≫ (lift u v).left) ≫ (snd M.Y M.Y).left = ((lift u' v').left ≫ pj M M) ≫ (snd M.Y M.Y).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_snd, hv, pj_snd, ← Category.assoc, ← Over.comp_left, lift_snd]
  exact pullback.hom_ext h1 h2
end GlobalTheory.SS.Translates
