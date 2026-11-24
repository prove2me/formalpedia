-- Prove2me | solution 1 for GlobalTheory.SS.LawDef.sec_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:17:55.750809+00:00
-- url     : https://prove2.me/submissions/d0b263bc-4583-43da-b46f-93f06945fb25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslate
import Theorems.Thm_GlobalTheory_isDominant_spMap_of_isFractionRing


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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LawDef
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
namespace GlobalTheory.SS.LawDef
theorem _root_.solution [IsDomain R] [IsFractionRing R K] {M : Model R A} {p : 𝟙_ (Over (Sp K)) ⟶ A}
    {s t : 𝟙_ (Over (Sp R)) ⟶ M.Y} (h : Sec M p s) (h' : Sec M p t) : s = t := by
  have := M.sep
  have := isDominant_spMap_of_isFractionRing R K
  have : IsReduced (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsReduced (Sp R))
  ext1
  exact ext_of_isDominant_of_isSeparated M.Y.hom ((Over.w s).trans (Over.w t).symm) (spMap (algebraMap R K))
    (h.symm.trans h')
end GlobalTheory.SS.LawDef
