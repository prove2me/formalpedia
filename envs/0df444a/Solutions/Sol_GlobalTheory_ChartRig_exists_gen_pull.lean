-- Prove2me | solution 1 for GlobalTheory.ChartRig.exists_gen_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:23.532191+00:00
-- url     : https://prove2.me/submissions/4ab61869-0814-49ab-a282-83be49e23a49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RigidifiedOfChart
import Theorems.Thm_GlobalTheory_ChartRig_res_res_pullU
import Theorems.Thm_GlobalTheory_ChartRig_res_pullU_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ChartRig
variable {X Y : Scheme.{0}}
namespace GlobalTheory.ChartRig
theorem _root_.solution (L : LB X) (f : Y ⟶ X) (i : L.ι) (hL : L.IsLB) (hi : ⊤ ≤ f ⁻¹ᵁ L.U i) :
    ∃ t : LB.Gen (L.pull f), t.IsGen := by
  have le1 : ∀ j : PUnit → L.ι, LB.wchart L (fun _ : PUnit => f) j ≤ f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U i) :=
    fun j => le_inf (LB.wchart_le L (fun _ : PUnit => f) j PUnit.unit) (le_top.trans hi)
  refine ⟨⟨fun j => res (le1 j) (pullU f _ (L.g (j PUnit.unit) i))⟩, fun j k => ?_⟩
  have le2 : LB.wchart L (fun _ : PUnit => f) j ⊓ LB.wchart L (fun _ : PUnit => f) k ≤
      f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (k PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => f) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => f) k PUnit.unit))
  have le3 : LB.wchart L (fun _ : PUnit => f) j ⊓ LB.wchart L (fun _ : PUnit => f) k ≤
      f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (k PUnit.unit) ⊓ L.U i) :=
    le_inf le2 (le_top.trans hi)
  have gg : (L.pull f).g j k = res le2 (pullU f _ (L.g (j PUnit.unit) (k PUnit.unit))) :=
    (Fintype.prod_unique (fun _ : PUnit =>
      (res le2 (pullU f _ (L.g (j PUnit.unit) (k PUnit.unit)))) ^ (1 : ℤ))).trans (zpow_one _)
  have c := congrArg (fun x => res le3 (pullU f _ x)) (hL.cocycle (j PUnit.unit) (k PUnit.unit) i)
  simp only [map_mul] at c
  rw [res_pullU_res f _ _ _ le3 _ le2, res_pullU_res f _ _ _ le3 _ (inf_le_right.trans (le1 k)),
    res_pullU_res f _ _ _ le3 _ (inf_le_left.trans (le1 j))] at c
  rw [gg]
  exact (res_res_pullU f _ _ _ (le1 j) inf_le_left _).trans
    (c.symm.trans (congrArg _ (res_res_pullU f _ _ _ (le1 k) inf_le_right _).symm))
end GlobalTheory.ChartRig
