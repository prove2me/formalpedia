-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg.rigAt_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:56:14.329888+00:00
-- url     : https://prove2.me/submissions/902ec011-22bd-4c69-9f44-5a2ec7d7537c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RawDegreeForms
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg_res_res
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg_res_pull_res
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg_res_pull_res_pull

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings
variable (R : Type) [CommRing R] [IsDomain R]
attribute [instance] RawDeg.addCommGroup RawDeg.free RawDeg.finite
open GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
variable {R} (D : RawDeg R)
namespace GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
theorem _root_.solution (i i' : D.P.L.ι) {V V' W} (h h') (k : W ≤ V) (k' : W ≤ V') (hW) :
    res k (D.rigAt i V h) =
      D.gAt (pzero D.P.A (genPt R)).left i i' W hW * res k' (D.rigAt i' V' h') := by
  have H := congrArg (fun u => res (U := (toUnit (genPt R)).left ⁻¹ᵁ
      ((D.P.L.pull (eSec D.P.A)).U (fun _ => i) ⊓ (D.P.L.pull (eSec D.P.A)).U (fun _ => i'))) (V := W)
    (fun _ hy => ⟨Set.mem_iInter.2 fun _ => h (k hy), Set.mem_iInter.2 fun _ => h' (k' hy)⟩)
      (pullU (toUnit (genPt R)).left _ u))
    (D.rig_gen (fun _ => i) (fun _ => i'))
  simp only [map_mul] at H
  have a1 : W ≤ (toUnit (genPt R)).left ⁻¹ᵁ (D.P.L.pull (eSec D.P.A)).U (fun _ => i) :=
    fun _ hy => Set.mem_iInter.2 fun _ => h (k hy)
  have a2 : W ≤ (toUnit (genPt R)).left ⁻¹ᵁ (D.P.L.pull (eSec D.P.A)).U (fun _ => i') :=
    fun _ hy => Set.mem_iInter.2 fun _ => h' (k' hy)
  refine ((res_res _ _ _).trans (res_res _ _ _)).trans
    ((res_pull_res _ _ _ a1 _).symm.trans (H.trans ?_))
  refine congrArg₂ (· * ·) ?_ ?_
  · have hg : ∀ hh, (D.P.L.pull (eSec D.P.A)).g (fun _ => i) (fun _ => i') =
        res (U := eSec D.P.A ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U i')) hh
          (pullU (eSec D.P.A) _ (D.P.L.g i i')) := by
      intro hh
      simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]
      rfl
    rw [hg (le_inf
      (inf_le_left.trans (LB.wchart_le D.P.L (K := PUnit) (fun _ => eSec D.P.A) _ PUnit.unit))
      (inf_le_right.trans (LB.wchart_le D.P.L (K := PUnit) (fun _ => eSec D.P.A) _ PUnit.unit)))]
    exact res_pull_res_pull (eSec D.P.A) (toUnit (genPt R)).left (D.P.L.U i ⊓ D.P.L.U i') _ _ hW _
  · exact (res_pull_res _ _ _ a2 _).trans ((res_res _ _ _).trans (res_res _ _ _)).symm
end GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
