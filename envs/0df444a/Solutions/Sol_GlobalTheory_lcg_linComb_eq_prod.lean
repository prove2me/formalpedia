-- Prove2me | solution 1 for GlobalTheory.lcg_linComb_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:59.604845+00:00
-- url     : https://prove2.me/submissions/a0e586dd-03bf-4465-9497-88b37d262ec4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LcgLinCombEqProd
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pullU_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (a b : K → (LB.LinComb L F (fun _ => 1)).ι) :
    LB.lcg (LB.LinComb L F (fun _ => 1)) φ ε a b =
      ∏ i, res (boxGen_overlap_le L F φ a b i)
        (LB.lcg (L.pull (F i)) φ ε (fun k _ => a k i) (fun k _ => b k i)) := by
  show (∏ k, (res _ (pullU (φ k) (LB.wchart L F (a k) ⊓ LB.wchart L F (b k))
      (LB.lcg L F (fun _ => 1) (a k) (b k)))) ^ ε k) =
    ∏ i, res _ (∏ k, (res _ (pullU (φ k)
      (LB.wchart L (fun _ : PUnit => F i) (fun _ => a k i) ⊓ LB.wchart L (fun _ : PUnit => F i) (fun _ => b k i))
      (LB.lcg L (fun _ : PUnit => F i) (fun _ => 1) (fun _ => a k i) (fun _ => b k i)))) ^ ε k)
  simp only [LB.lcg, map_prod, map_zpow, zpow_one, Finset.univ_unique, Finset.prod_singleton,
    ReciprocityTheory.ChartRestriction.G.DVR.pullU_res, ← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
  congr 1
  repeat erw [ReciprocityTheory.ChartRestriction.G.DVR.res_res']
end GlobalTheory
