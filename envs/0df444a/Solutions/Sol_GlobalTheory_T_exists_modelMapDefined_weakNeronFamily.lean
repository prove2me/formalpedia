-- Prove2me | solution 1 for GlobalTheory.T.exists_modelMapDefined_weakNeronFamily
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:48:37.557132+00:00
-- url     : https://prove2.me/submissions/fb422b3c-afd9-4c2a-a166-26fb3880e700

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsModelMapDefinedWeakNeronFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsModelMapDefinedWeakNeronFamilyStatement
import Theorems.Thm_GlobalTheory_SS_exists_defAt_of_weakNeron


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) [IsIntegral A.left] (I : Type) (M : I → Model R A), WeakNeron M → ∀ N : Model R A, N.Irr → ∃ i, ∃ y ∈ N.sp, DefAt N (M i) (𝟙 A) y := by
  first | exact @GlobalTheory.SS.exists_defAt_of_weakNeron | exact GlobalTheory.SS.exists_defAt_of_weakNeron | (intros; apply GlobalTheory.SS.exists_defAt_of_weakNeron <;> assumption)
end _root_.GlobalTheory.T
