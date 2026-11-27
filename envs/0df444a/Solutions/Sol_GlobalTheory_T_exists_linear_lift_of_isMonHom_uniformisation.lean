-- Prove2me | solution 1 for GlobalTheory.T.exists_linear_lift_of_isMonHom_uniformisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:37.517831+00:00
-- url     : https://prove2.me/submissions/c51b8f66-d456-47d9-8c9d-79c0505366cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearLiftOfIsMonHomPolAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearLiftOfIsMonHomPolAVStatement
import Theorems.Thm_GlobalTheory_exists_linear_lift_of_isMonHom_polAV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (P P' : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (L' : LB P'.A.left) (u : HolUnif P.A L P.g) (u' : HolUnif P'.A L' P'.g) (f : P.A ⟶ P'.A), IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ), ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  first | exact @GlobalTheory.exists_linear_lift_of_isMonHom_polAV | exact GlobalTheory.exists_linear_lift_of_isMonHom_polAV | (intros; apply GlobalTheory.exists_linear_lift_of_isMonHom_polAV <;> assumption)
end _root_.GlobalTheory.T
