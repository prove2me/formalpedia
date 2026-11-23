-- Prove2me | solution 1 for GlobalTheory.SS.Model.dominant_j
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:44.043376+00:00
-- url     : https://prove2.me/submissions/2244fff0-5064-4b0f-b1a4-3ad1b19db746

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPoints
import Theorems.Thm_GlobalTheory_SS_Model_isPullback_j
import Theorems.Thm_GlobalTheory_schemeTheoreticallyDominant_fractionField


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
open GlobalTheory GlobalTheory.SS
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (Sp K)}
variable [IsDomain R] [IsFractionRing R K]
namespace GlobalTheory.SS
namespace Model
theorem _root_.solution (M : Model R A) : IsSchemeTheoreticallyDominant M.j := by
  have := schemeTheoreticallyDominant_fractionField R K
  have := M.smooth
  exact IsSchemeTheoreticallyDominant.of_isPullback M.isPullback_j.flip
end Model
end GlobalTheory.SS
