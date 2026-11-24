-- Prove2me | solution 1 for GlobalTheory.SS.SectionTranslation.ext_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:19:05.536174+00:00
-- url     : https://prove2.me/submissions/01de0caa-e9ab-4b5e-b220-0c875188ad0e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_ext_of_schDom
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_schDom_spec_map
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_j_isPullback

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.SectionTranslation
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.SectionTranslation
theorem _root_.solution [IsDomain R] [IsFractionRing R K] (M : Model R A) (U : M.Y.left.Opens) {Y Z : Scheme.{0}}
    {f g : U.toScheme ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (hU : (M.j ∣_ U) ≫ f = (M.j ∣_ U) ≫ g) : f = g := by
  have := M.smooth
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) := schDom_spec_map _ (IsFractionRing.injective R K)
  have hp := (isPullback_morphismRestrict M.j U).paste_vert (j_isPullback M)
  have : IsSchemeTheoreticallyDominant (M.j ∣_ U) := IsSchemeTheoreticallyDominant.of_isPullback hp.flip
  exact ext_of_schDom s h _ hU
end GlobalTheory.SS.SectionTranslation
