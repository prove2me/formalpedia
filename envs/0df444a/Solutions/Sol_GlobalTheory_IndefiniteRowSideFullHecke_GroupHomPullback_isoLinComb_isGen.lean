-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.isoLinComb_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:50:51.449435+00:00
-- url     : https://prove2.me/submissions/01d53061-8bf4-427f-aa89-ea8773603d32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_GroupHomPullback
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GroupHomPullback_res_prod_pr
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GroupHomPullback_isoUnit_compat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
variable {X X' Y Y' : Scheme.{u}}
variable {K : Type u} [Fintype K]
namespace GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback
theorem _root_.solution {L M : LB X} {u : LB.Iso L M} (hu : u.IsGen) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : (isoLinComb u φ ε).IsGen := by
  have key (j j' : K → M.ι) (i i' : K → L.ι) (W : Y.Opens)
      (h : W ≤ LB.wchart M φ j ⊓ LB.wchart L φ i) (h' : W ≤ LB.wchart M φ j' ⊓ LB.wchart L φ i')
      (hM : W ≤ LB.wchart M φ j ⊓ LB.wchart M φ j') (hL : W ≤ LB.wchart L φ i ⊓ LB.wchart L φ i') :
      res h (∏ k, (pr (φ k) (le_pre_inf M L φ j i k) (isoUnit u (j k) (i k))) ^ (ε k)) =
      res (U := LB.wchart M φ j ⊓ LB.wchart M φ j') hM ((LB.LinComb M φ ε).g j j') *
      (res (U := LB.wchart L φ i ⊓ LB.wchart L φ i') hL ((LB.LinComb L φ ε).g i i'))⁻¹ *
      res h' (∏ k, (pr (φ k) (le_pre_inf M L φ j' i' k) (isoUnit u (j' k) (i' k))) ^ (ε k)) := by
    rw [res_prod_pr, res_prod_pr, res_linComb_g, res_linComb_g,
      ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← inv_zpow, ← mul_zpow, ← mul_zpow]
    congr 1
    exact isoUnit_compat hu _ _ _ _ _ _ _ _ _
  intro p q
  exact key p.1 q.1 p.2 q.2 _ inf_le_left inf_le_right _ _
end GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback
