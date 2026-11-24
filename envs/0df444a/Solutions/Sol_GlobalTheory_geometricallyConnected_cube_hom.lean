-- Prove2me | solution 1 for GlobalTheory.geometricallyConnected_cube_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:07:14.417084+00:00
-- url     : https://prove2.me/submissions/1428d7d0-bbad-4883-ab7b-287cb6b09c84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Theorems.Thm_GlobalTheory_geometricallyConnected_tensorObj_hom
import Theorems.Thm_GlobalTheory_smooth_square_hom
import Theorems.Thm_GlobalTheory_geometricallyConnected_square_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{u}}
open ReciprocityTheory.ChartRestriction.G.Semi
variable (G : Over S) [Smooth G.hom]
variable [GeometricallyConnected G.hom]
namespace GlobalTheory
theorem _root_.solution : GeometricallyConnected (G3 G).hom :=
  have := smooth_square_hom G
  have := geometricallyConnected_square_hom G
  geometricallyConnected_tensorObj_hom G (G2 G)
end GlobalTheory
