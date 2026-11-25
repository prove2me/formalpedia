-- Prove2me | solution 1 for GlobalTheory.grpObj_geometricallyIntegral_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:58:37.517148+00:00
-- url     : https://prove2.me/submissions/0824216e-e916-45cb-b0a6-2fc3cde2320e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Theorems.Thm_GlobalTheory_geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution (S : Scheme.{0}) (H : Over S) [GrpObj H]
    [Smooth H.hom] [GeometricallyConnected H.hom] : GeometricallyIntegral H.hom :=
  geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres H.hom
end GlobalTheory
