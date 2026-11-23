-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.gr_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:56.697903+00:00
-- url     : https://prove2.me/submissions/6717ab9e-25c8-4a91-89cf-e35cbbb8ed1f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res

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
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SmallExtLift
variable {X Y Z : Scheme.{0}}
variable {R : Type} [CommRing R]
namespace GlobalTheory.SmallExtLift
theorem _root_.solution {M : LB X} {F : Y ⟶ X} {t : LB.Gen (M.pull F)} (ht : t.IsGen) (r : Z ⟶ Y) (z : Z)
    {i j : M.ι} (hi : F (r z) ∈ M.U i) (hj : F (r z) ∈ M.U j) :
    gr r z _ (pull_le M F i le_rfl hi) (t.s fun _ => i).val =
      gr (r ≫ F) z (M.U i ⊓ M.U j) ⟨hi, hj⟩ (M.g i j).val *
        gr r z _ (pull_le M F j le_rfl hj) (t.s fun _ => j).val := by
  have hm : r z ∈ (M.pull F).U (fun _ => i) ⊓ (M.pull F).U (fun _ => j) :=
    ⟨pull_le M F i le_rfl hi, pull_le M F j le_rfl hj⟩
  have := congrArg (fun u => gr r z _ hm u.val) (ht (fun _ => i) (fun _ => j))
  simp only [Units.val_mul, map_mul] at this
  refine (gr_res r z _ hm _).symm.trans (this.trans (congrArg₂ (· * ·) ?_ (gr_res r z _ hm _)))
  refine (congrArg (fun u => gr r z _ hm (Units.val u))
    ((Fintype.prod_unique (fun _ : PUnit => _ ^ (1 : ℤ))).trans (zpow_one _))).trans ?_
  exact gr_res r z _ hm _
end GlobalTheory.SmallExtLift
