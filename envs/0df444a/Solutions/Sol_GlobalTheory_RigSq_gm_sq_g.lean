-- Prove2me | solution 1 for GlobalTheory.RigSq.gm_sq_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:52:14.904498+00:00
-- url     : https://prove2.me/submissions/e1297d22-2d20-425d-945d-b7ba5f81f04d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRescaleRigidifiedSquareIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
noncomputable section
open GlobalTheory GlobalTheory.RigSq
variable {X Y : Scheme.{0}}
namespace GlobalTheory.RigSq
theorem _root_.solution (L : LB X) (f : Y ⟶ X) (y : Y) (j j' : L.ι) (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') :
    gm f y _ ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).g (fun _ => j) (fun _ => j')) =
      gm f y _ (L.g j j') ^ 2 := by
  have hp : f y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j) ⊓
      (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j') :=
    ⟨Set.mem_iInter.2 fun _ => hj, Set.mem_iInter.2 fun _ => hj'⟩
  show gm f y _ (∏ _k : Fin 1, (res _ (pullU (𝟙 X) _ (L.g j j'))) ^ (2 : ℤ)) = _
  rw [Fintype.prod_unique, map_zpow]
  refine (congrArg (· ^ (2 : ℤ)) ((gm_res f y _ hp _).trans (gm_pull f (𝟙 X) y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _))).trans ?_
  rw [Category.comp_id]
  exact zpow_two _ |>.trans (pow_two _).symm
end GlobalTheory.RigSq
