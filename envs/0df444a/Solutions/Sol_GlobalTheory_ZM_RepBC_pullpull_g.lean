-- Prove2me | solution 1 for GlobalTheory.ZM.RepBC.pullpull_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:51:40.063272+00:00
-- url     : https://prove2.me/submissions/5298b74b-61e2-4f41-bf66-a3e4d2a8f7b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Theorems.Thm_GlobalTheory_ZM_RepBC_appLE_appLE

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
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.RepBC
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.ZM.RepBC
theorem _root_.solution (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (J J' : PUnit → PUnit → M.ι)
    (e : ((M.pull π).pull x).U J ⊓ ((M.pull π).pull x).U J' ≤
      (x ≫ π) ⁻¹ᵁ (M.U (J PUnit.unit PUnit.unit) ⊓ M.U (J' PUnit.unit PUnit.unit))) :
    (((M.pull π).pull x).g J J').val =
      ((x ≫ π).appLE _ _ e).hom (M.g (J PUnit.unit PUnit.unit) (J' PUnit.unit PUnit.unit)).val := by
  rw [pull_g (M.pull π) x J J' (pull_inf_le _ _ _ _), pull_g M π _ _ (pull_inf_le _ _ _ _)]
  exact appLE_appLE x π _ _ e _
end GlobalTheory.ZM.RepBC
