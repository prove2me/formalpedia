-- Prove2me | solution 1 for GlobalTheory.BoxSymLoc.gU_pull_box_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:07:33.589935+00:00
-- url     : https://prove2.me/submissions/95883edb-ef28-4576-bee7-915e7998a020

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RigidifiedSymBoxLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_lcg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_pullU_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxSymLoc
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res)
open ReciprocityTheory.ChartRestriction.G.Out.LBxP
variable {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
namespace GlobalTheory.BoxSymLoc
theorem _root_.solution (F : J → (X' ⟶ X)) (a : Y ⟶ X') (i j : J → L.ι) (y : Y)
    (hy : y ∈ a ⁻¹ᵁ ((LB.LinComb L F (fun _ => 1)).U i ⊓ (LB.LinComb L F (fun _ => 1)).U j))
    (hy' : ∀ m, y ∈ (a ≫ F m) ⁻¹ᵁ (L.U (i m) ⊓ L.U (j m))) :
    gU y hy (pullU a _ ((LB.LinComb L F (fun _ => 1)).g i j)) =
      ∏ m, gU y (hy' m) (pullU (a ≫ F m) _ (L.g (i m) (j m))) := by
  refine (gU_pullU a _ y hy _).trans ?_
  have e := gU_lcg L F (fun _ => 1) i j (a.base y) hy
  refine (congrArg (Units.map (RingHom.toMonoidHom (a.stalkMap y).hom)) e).trans ?_
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun m _ => ?_)
  refine (congrArg (Units.map (RingHom.toMonoidHom (a.stalkMap y).hom)) (zpow_one _)).trans ?_
  refine (gU_pullU a _ y _ _).symm.trans ?_
  exact gU_pullU_comp a (F m) _ _ y _ _
end GlobalTheory.BoxSymLoc
