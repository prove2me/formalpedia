-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.h1Zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:10:49.523955+00:00
-- url     : https://prove2.me/submissions/00c60ef5-6855-4a4d-a658-1c8f6adc459a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_le_iSup_inf
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_isCoboundary_of_refine
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_chart_change
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_chart_restrict
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CechOne
open SecOn
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable {M : LB X}
namespace GlobalTheory.AbLaw.CechOne
theorem _root_.solution (hM : M.IsLB) : FirstCohomologyVanishes M ↔ CechHOneVanishesOnOpen M ⊤ := by
  constructor
  · intro H I O _ hc φ hφ
    have hc' : ⨆ p : I × M.ι, O p.1 ⊓ M.U p.2 = ⊤ := by
      refine top_unique (hc.trans (iSup_le fun a => (le_iSup_inf (hM.cover.ge.trans' le_top)).trans
        (iSup_le fun i => le_iSup (fun p : I × M.ι => O p.1 ⊓ M.U p.2) (a, i))))
    obtain ⟨ψ, hψ⟩ := H (I × M.ι) (fun p => O p.1 ⊓ M.U p.2) Prod.snd (fun _ => inf_le_right) hc'
      (fun p q => chart hM p.2 (inf_le_left.trans inf_le_right)
        (restrict M (inf_le_inf inf_le_left inf_le_left) (φ p.1 q.1))) (by
      intro p q r
      rw [← chart_restrict, ← chart_restrict, ← chart_restrict,
        ← chart_change hM p.2 q.2 ((inf_le_left.trans inf_le_left).trans inf_le_right), ← map_add]
      simp only [restrict_restrict]
      exact congrArg _ (hφ p.1 q.1 r.1 _ ((inf_le_left.trans inf_le_left).trans inf_le_left)
        ((inf_le_left.trans inf_le_right).trans inf_le_left) (inf_le_right.trans inf_le_left)))
    refine isCoboundary_of_refine hφ (fun p : I × M.ι => O p.1 ⊓ M.U p.2) Prod.fst
      (fun _ => inf_le_left) (fun _ => le_top.trans hc'.ge)
      (fun p => (chart hM p.2 inf_le_right).symm (ψ p)) fun p q => ?_
    apply (chart hM p.2 (inf_le_left.trans inf_le_right)).injective
    rw [map_sub, chart_restrict hM p.2 inf_le_right, LinearEquiv.apply_symm_apply,
      chart_change hM p.2 q.2 _ (inf_le_right.trans inf_le_right) (restrict M inf_le_right _),
      chart_restrict hM q.2 inf_le_right,
      LinearEquiv.apply_symm_apply]
    exact hψ p q
  · intro H I V c hV hc φ hφ
    obtain ⟨ψ, hψ⟩ := H I V (fun _ => le_top) hc.ge
      (fun a b => (chart hM (c a) (inf_le_left.trans (hV a))).symm (φ a b)) (by
      intro a b d W ha hb hd
      apply (chart hM (c a) (ha.trans (hV a))).injective
      have h := congrArg (rs X (le_inf (le_inf ha hb) hd)) (hφ a b d)
      simp only [map_add, map_mul, rs_rs] at h
      rw [map_add, chart_restrict hM (c a) (inf_le_left.trans (hV a)),
        chart_change hM (c a) (c b) _ (hb.trans (hV b)),
        chart_restrict hM (c b) (inf_le_left.trans (hV b)),
        chart_restrict hM (c a) (inf_le_left.trans (hV a))]
      simpa only [LinearEquiv.apply_symm_apply] using h)
    refine ⟨fun a => chart hM (c a) (hV a) (ψ a), fun a b => ?_⟩
    have h := (LinearEquiv.symm_apply_eq _).1 (hψ a b)
    rw [h, map_sub, chart_restrict hM (c a) (hV a),
      chart_change hM (c a) (c b) _ (inf_le_right.trans (hV b)), chart_restrict hM (c b) (hV b)]
end GlobalTheory.AbLaw.CechOne
