-- Prove2me | solution 1 for GlobalTheory.geometricallyIntegral_tensorObj_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:13:33.970737+00:00
-- url     : https://prove2.me/submissions/1ac4a456-3c80-4166-bb65-c0cb605158c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Theorems.Thm_GlobalTheory_geometricallyIntegral_of_smooth
import Theorems.Thm_GlobalTheory_smooth_tensorObj_hom
import Theorems.Thm_GlobalTheory_geometricallyConnected_tensorObj_hom

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
namespace GlobalTheory
theorem _root_.solution (G H : Over S) [Smooth G.hom] [Smooth H.hom]
    [GeometricallyConnected G.hom] [GeometricallyConnected H.hom] :
    GeometricallyIntegral (G ⊗ H).hom :=
  have := smooth_tensorObj_hom G H
  have := geometricallyConnected_tensorObj_hom G H
  geometricallyIntegral_of_smooth _
end GlobalTheory
