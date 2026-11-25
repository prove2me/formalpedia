-- Prove2me | solution 1 for GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:58:36.731615+00:00
-- url     : https://prove2.me/submissions/e7633d6d-5d84-47ed-ade4-9fc5a48cd188

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f :=
  fun _ _ f _ _ ↦ geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres f
end GlobalTheory
