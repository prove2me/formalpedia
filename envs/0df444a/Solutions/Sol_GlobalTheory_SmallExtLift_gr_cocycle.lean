-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.gr_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:15.974866+00:00
-- url     : https://prove2.me/submissions/d0722c92-5de8-4372-85e0-3f8bade26d03

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
theorem _root_.solution {M : LB X} (hM : M.IsLB) (f : Z ⟶ X) (z : Z) {i j k : M.ι} (hi : f z ∈ M.U i)
    (hj : f z ∈ M.U j) (hk : f z ∈ M.U k) :
    gr f z (M.U i ⊓ M.U j) ⟨hi, hj⟩ (M.g i j).val * gr f z (M.U j ⊓ M.U k) ⟨hj, hk⟩ (M.g j k).val =
      gr f z (M.U i ⊓ M.U k) ⟨hi, hk⟩ (M.g i k).val := by
  have hm : f z ∈ M.U i ⊓ M.U j ⊓ M.U k := ⟨⟨hi, hj⟩, hk⟩
  have := congrArg (fun u => gr f z _ hm u.val) (hM.cocycle i j k)
  simp only [Units.val_mul, map_mul] at this
  exact (congrArg₂ (· * ·) (gr_res f z _ hm _) (gr_res f z _ hm _)).symm.trans
    (this.trans (gr_res f z _ hm _))
end GlobalTheory.SmallExtLift
