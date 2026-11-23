-- Prove2me | solution 1 for GlobalTheory.BoxDetUnique.gs_cst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:24.798951+00:00
-- url     : https://prove2.me/submissions/6e32bc0a-547b-4d45-b479-0b37ea95ca36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CardHomVanishingOfDiagBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DetKroneckerPower
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsBoxSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.BoxDetUnique
variable {X Y Z : Scheme.{0}} {R : Type} [CommRing R]
namespace GlobalTheory.BoxDetUnique
theorem _root_.solution (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : R) :
    gs r z U (cst p U a) = kv (r ≫ p) z a :=
  (gs_res r z le_top h _).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq (r ≫ p) z ⊤ trivial _))
end GlobalTheory.BoxDetUnique
