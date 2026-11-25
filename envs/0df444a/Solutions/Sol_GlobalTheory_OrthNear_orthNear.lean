-- Prove2me | solution 1 for GlobalTheory.OrthNear.orthNear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:15:45.02407+00:00
-- url     : https://prove2.me/submissions/32fe5f64-bd37-48a8-9fde-388aed873c84

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DminCptEq
import Theorems.Thm_GlobalTheory_OrthNear_isOrth_x0F
import Theorems.Thm_GlobalTheory_OrthNear_dmin_cpt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_det_ne_of_orth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_isOpen_OmF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_zero_mem_OmF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_densF_continuousOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_densF_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_isOpen_OmF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoE_nfac_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoE_nfac_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app


section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.OrthNear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem mat_cpt_eq_mat_mul_mat_nmat {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) τ := rfl
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem densF_eq_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z = _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X y z := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF, _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem nfac_cpt_eq_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac, _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem cpt_mem_dom_iff_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom ↔ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z ∈ X.dom := by
  have hdet : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ).det ≠ 0 ↔
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ).det ≠ 0 := by
    intro τ
    rw [mat_cpt_eq_mat_mul_mat_nmat, mat_cpt_eq_mat_mul_mat_nmat, Matrix.det_mul, Matrix.det_mul]
    simp [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.det_ne_of_orth X hx τ, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.det_ne_of_orth X hy τ]
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom, _root_.ReciprocityTheory.ChartRestriction.G.FD.GG, Set.mem_setOf_eq, hdet,
    _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]
end GlobalTheory.OrthNear
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.OrthNear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.OrthNear
namespace _root_.GlobalTheory.OrthNear
theorem _root_.solution : (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r), ∃ ρ c C : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ < ρ → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom ∧ c ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z ≤ C ∧ c ≤ X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∧ X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ≤ C) := by
  intro r X la
  set x0 := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F X
  have h0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 := _root_.GlobalTheory.OrthNear.isOrth_x0F X
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.isOpen_iff.mp (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.isOpen_OmF X x0) 0 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.zero_mem_OmF X x0 h0)
  set K := Metric.closedBall (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (ρ0 / 2)
  have hKsub : K ⊆ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0 :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKne : K.Nonempty := ⟨0, Metric.mem_closedBall_self (by linarith)⟩
  have hd : ContinuousOn (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0) K := (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.densF_continuousOn (X := X) (x0 := x0)).mono hKsub
  have hn : ContinuousOn (fun z => X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) K :=
    (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_cont X x0 la).mono hKsub
  obtain ⟨z1, hz1, hmin1⟩ := hK.exists_isMinOn hKne hd
  obtain ⟨z2, hz2, hmin2⟩ := hK.exists_isMinOn hKne hn
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hd
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn hn
  refine ⟨ρ0 / 2, min (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0 z1) (X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z2)), max C1 C2,
    by linarith, lt_min (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.densF_pos (hKsub hz1)) (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_pos X x0 (hKsub hz2)), ?_⟩
  intro x hx z hz
  have hzK : z ∈ K := Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hz.le)
  have hdom : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z ∈ X.dom := hKsub hzK
  rw [densF_eq_of_isOrth X hx h0, nfac_cpt_eq_of_isOrth X hx h0,
    cpt_mem_dom_iff_of_isOrth X hx h0]
  exact ⟨hdom, (min_le_left _ _).trans (isMinOn_iff.mp hmin1 z hzK),
    (Real.le_norm_self _).trans ((hC1 z hzK).trans (le_max_left _ _)),
    (min_le_right _ _).trans (isMinOn_iff.mp hmin2 z hzK),
    (Real.le_norm_self _).trans ((hC2 z hzK).trans (le_max_right _ _))⟩
end _root_.GlobalTheory.OrthNear
end GlobalTheory.OrthNear
