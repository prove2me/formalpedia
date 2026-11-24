-- Prove2me | solution 1 for GlobalTheory.RootUnit.trF_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:07:21.084532+00:00
-- url     : https://prove2.me/submissions/ae664729-3e56-46da-a1ea-8ee3556845b0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitOfStalks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RootUnit
open TopologicalSpace
namespace GlobalTheory.RootUnit
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} (f : Y ⟶ X) (y : Y) (i j : PUnit → L.ι) :
    trF (L := L) (K := PUnit) (fun _ => f) (fun _ => 1) (𝟙 Y) y i j =
      gm (𝟙 Y ≫ f) y (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) (L.g _ _) := by
  rw [trF, Fintype.prod_unique, zpow_one]
end GlobalTheory.RootUnit
