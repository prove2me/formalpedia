-- Prove2me | solution 1 for GlobalTheory.BoxSymLoc.isGen_boxGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:18:38.561477+00:00
-- url     : https://prove2.me/submissions/4e3a1998-53fd-4949-9147-fb0d61ee4110

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RigidifiedSymBoxLB
import Theorems.Thm_GlobalTheory_BoxSymLoc_gU_pull_box_g
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_lcg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_pull_g
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
theorem _root_.solution (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (ht : ∀ i, (t i).IsGen) :
    (GeneratorPullback.boxGen L F φ ε t).IsGen := by
  intro i j
  apply unit_ext
  intro y hy
  have hm : ∀ m, y ∈ (LB.LinComb (L.pull (F m)) φ ε).U (fun k _ => i k m) ⊓
      (LB.LinComb (L.pull (F m)) φ ε).U (fun k _ => j k m) :=
    fun m => ⟨GeneratorPullback.box_le L F φ i m hy.1, GeneratorPullback.box_le L F φ j m hy.2⟩
  have hk : ∀ k m, y ∈ (φ k ≫ F m) ⁻¹ᵁ (L.U (i k m) ⊓ L.U (j k m)) := fun k m =>
    ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 k) m, Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 k) m⟩
  have hb : ∀ (c : K → J → L.ι) (hc : y ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) φ c),
      gU y hc ((GeneratorPullback.boxGen L F φ ε t).s c) =
        ∏ m, gU y (GeneratorPullback.box_le L F φ c m hc) ((t m).s (fun k _ => c k m)) := fun c hc =>
    (map_prod (gU y hc) _ _).trans (Finset.prod_congr rfl fun m _ => gU_res _ _ _ _)
  have Ht : ∀ m, gU y (GeneratorPullback.box_le L F φ i m hy.1) ((t m).s (fun k _ => i k m)) =
      (∏ k, gU y (hk k m) (pullU (φ k ≫ F m) _ (L.g (i k m) (j k m))) ^ ε k) *
        gU y (GeneratorPullback.box_le L F φ j m hy.2) ((t m).s (fun k _ => j k m)) := by
    intro m
    refine (gU_res (inf_le_left : (LB.LinComb (L.pull (F m)) φ ε).U (fun k _ => i k m) ⊓
      (LB.LinComb (L.pull (F m)) φ ε).U (fun k _ => j k m) ≤ _) y (hm m) _).symm.trans ?_
    refine (congrArg (gU y (hm m)) (ht m (fun k _ => i k m) (fun k _ => j k m))).trans ?_
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gU_res _ _ _ _))
    refine (gU_lcg (L.pull (F m)) φ ε _ _ y (hm m)).trans ?_
    refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_
    exact gU_pull_g L (F m) (φ k) _ _ y _ (hk k m)
  have hg : gU y hy ((LB.LinComb (LB.LinComb L F (fun _ => 1)) φ ε).g i j) =
      ∏ m, ∏ k, gU y (hk k m) (pullU (φ k ≫ F m) _ (L.g (i k m) (j k m))) ^ ε k := by
    refine (gU_lcg (LB.LinComb L F (fun _ => 1)) φ ε i j y hy).trans ?_
    refine Eq.trans ?_ Finset.prod_comm
    refine Finset.prod_congr rfl fun k _ => ?_
    refine Eq.trans ?_ (Finset.prod_zpow _ _ _).symm
    exact congrArg (· ^ ε k) (gU_pull_box_g L F (φ k) (i k) (j k) y _ (hk k))
  refine ((gU_res _ y hy _).trans (hb i hy.1)).trans ?_
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) hg
    ((gU_res _ y hy _).trans (hb j hy.2)))).symm
  exact (Finset.prod_congr rfl fun m _ => Ht m).trans Finset.prod_mul_distrib
end GlobalTheory.BoxSymLoc
