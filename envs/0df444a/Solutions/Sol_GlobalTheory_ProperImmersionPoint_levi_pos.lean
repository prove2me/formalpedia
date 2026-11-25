-- Prove2me | solution 1 for GlobalTheory.ProperImmersionPoint.levi_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:14:48.247381+00:00
-- url     : https://prove2.me/submissions/fb8a7e65-c0c4-414e-9bcd-2c83f9f598bf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PointwiseNormInvarianceHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSelectForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CptDifferentiable
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_cpt_differentiable
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_sum_norm_pos
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_ratio_pos
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_log_ratio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_isOpen_OmF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_cpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_phla_cpt_cdAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_ofReal_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_ofReal_const_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_re_nonpos_of_isLocalMax
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_log_sum_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_logPshAt_normSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.ProperImmersionPoint
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.ProperImmersionPoint
theorem _root_.solution {r : ℕ} {X : Data E r} {L eW : Wt X.Ψ r} {N a : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ} {et : Frame X.Ψ r → ℂ} (ha : 0 < a)
    (hw : ∀ k, X.IsSec L (w k)) (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) (het : X.IsSec eW et)
    (hpos : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X (a • L - eW)) x0 z ξ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (he : et x ≠ 0) (hmax : ∀ y ∈ X.dom, ratio X L eW a w et y ≤ ratio X L eW a w et x) (ξ : Fin (nd X) → ℂ)
    (hξ : ξ ≠ 0) :
    0 < (leviV (nd X) (fun z => ((Real.log (∑ k, ‖w k (cpt X x z)‖ ^ 2) : ℝ) : ℂ)) 0 ξ).re := by
  have hz : cpt X x 0 = x := IW.cpt_zero X x
  have h0 : (0 : V (nd X)) ∈ OmF X x := by
    change cpt X x 0 ∈ X.dom
    rwa [hz]
  have hO := ExF.isOpen_OmF X x
  have htn : OmF X x ∈ 𝓝 (0 : V (nd X)) := hO.mem_nhds h0
  have holo : ∀ {P : Frame X.Ψ r → ℂ}, DifferentiableOn ℂ P X.dom →
      ContDiffAt ℂ 2 (fun z => P (cpt X x z)) 0 := by
    intro P hP
    have h1 : DifferentiableOn ℂ (fun z => P (cpt X x z)) (OmF X x) :=
      hP.comp (cpt_differentiable X x).differentiableOn fun _ hz => hz
    exact ((contDiffOn_of_differentiableOn _ _ _ hO h1).contDiffAt htn).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hga := holo het.1
  have hgw : ∀ k, ContDiffAt ℂ 2 (fun z => w k (cpt X x z)) 0 := fun k =>
    holo (hw k).1
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (a : ℝ) := ⟨_, rfl⟩
  have hm' : (1 : ℝ) ≤ m := by
    rw [hm]
    exact_mod_cast ha
  obtain ⟨fα, hfα⟩ : ∃ f : V (nd X) → ℝ,
      f = fun v => Real.log (Complex.normSq (et (cpt X x v))) := ⟨_, rfl⟩
  obtain ⟨fP, hfP⟩ : ∃ f : V (nd X) → ℝ, f = fun v => phla X (a • L - eW) (cpt X x v) := ⟨_, rfl⟩
  obtain ⟨fW, hfW⟩ : ∃ f : V (nd X) → ℝ,
      f = fun v => Real.log (∑ k, ‖w k (cpt X x v)‖ ^ 2) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ f : V (nd X) → ℝ,
      f = fun v => (fα v + fP v) + (-m) * fW v := ⟨_, rfl⟩
  have hαc : ContDiffAt ℝ 2 (fun v => Complex.normSq (et (cpt X x v))) 0 := by
    have := (contDiff_norm_sq ℝ).comp_contDiffAt (0 : V (nd X)) (hga.restrict_scalars ℝ)
    simpa [Function.comp_def, Complex.normSq_eq_norm_sq] using this
  have hα0 : Complex.normSq (et (cpt X x 0)) ≠ 0 := by
    rw [hz]; exact (Complex.normSq_pos.2 he).ne'
  have hcα : ContDiffAt ℝ 2 fα 0 := by rw [hfα]; exact hαc.log hα0
  have hcP : ContDiffAt ℝ 2 fP 0 := by
    rw [hfP]; exact (IW.phla_cpt_cdAt X x h0 _).of_le (WithTop.coe_le_coe.2 le_top)
  have hWc : ContDiffAt ℝ 2 (fun v => ∑ k, ‖w k (cpt X x v)‖ ^ 2) 0 :=
    ContDiffAt.sum (fun k _ => (contDiff_norm_sq ℝ).comp_contDiffAt _ ((hgw k).restrict_scalars ℝ))
  have hW0 : (∑ k, ‖w k (cpt X x 0)‖ ^ 2) ≠ 0 := (sum_norm_pos hnz h0).ne'
  have hcW : ContDiffAt ℝ 2 fW 0 := by rw [hfW]; exact hWc.log hW0
  have hc1 : ContDiffAt ℝ 2 (fun v => fα v + fP v) 0 := hcα.add hcP
  have hc2 : ContDiffAt ℝ 2 (fun v => (-m) * fW v) 0 := contDiffAt_const.mul hcW
  have hch : ContDiffAt ℝ 2 h 0 := by rw [hh]; exact hc1.add hc2
  have hne : ∀ᶠ v in 𝓝 (0 : V (nd X)), et (cpt X x v) ≠ 0 :=
    hga.continuousAt.eventually_ne (by rw [hz]; exact he)
  have hloc : ∀ᶠ v in 𝓝 (0 : V (nd X)), h v = Real.log (ratio X L eW a w et (cpt X x v)) := by
    filter_upwards [htn, hne] with v hv hv'
    rw [log_ratio hnz hv hv', hh, hfα, hfP, hfW, hm]
  have hmaxh : IsLocalMax h 0 := by
    have h00 := hloc.self_of_nhds
    rw [hz] at h00
    filter_upwards [hloc, htn, hne] with v hv hvt hv'
    rw [hv, h00]
    exact Real.log_le_log (ratio_pos hnz hvt hv') (hmax _ hvt)
  have hL := Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hch hmaxh ξ
  have e1 : leviV (nd X) (fun y => ((h y : ℝ) : ℂ)) 0 ξ =
      leviV (nd X) (fun y => ((fα y + fP y : ℝ) : ℂ)) 0 ξ +
        leviV (nd X) (fun y => (((-m) * fW y : ℝ) : ℂ)) 0 ξ := by
    rw [hh]; exact Y.LocalMaximumSecondDerivative.leviV_ofReal_add hc1 hc2 ξ
  have e2 : leviV (nd X) (fun y => ((fα y + fP y : ℝ) : ℂ)) 0 ξ =
      leviV (nd X) (fun y => ((fα y : ℝ) : ℂ)) 0 ξ +
        leviV (nd X) (fun y => ((fP y : ℝ) : ℂ)) 0 ξ :=
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add hcα hcP ξ
  rw [e1, e2, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ hcW] at hL
  simp only [Complex.add_re, Complex.re_ofReal_mul] at hL
  have hαnn : 0 ≤ (leviV (nd X) (fun y => ((fα y : ℝ) : ℂ)) 0 ξ).re := by
    have hpos' : 0 < ∑ _j : Fin 1, Complex.normSq (et (cpt X x 0)) := by
      simp only [Fin.sum_univ_one, hz]; exact Complex.normSq_pos.2 he
    have := leviV_log_sum_nonneg (m := 1)
      (u := fun _ v => Complex.normSq (et (cpt X x v))) (x := 0)
      (fun _ => hαc) (fun _ => logPshAt_normSq hga) hpos' ξ
    rw [hfα]; simpa using this
  have hPpos : 0 < (leviV (nd X) (fun y => ((fP y : ℝ) : ℂ)) 0 ξ).re := by
    rw [hfP]; exact hpos x hx 0 h0 ξ hξ
  have hfin : 0 < (leviV (nd X) (fun y => ((fW y : ℝ) : ℂ)) 0 ξ).re := by
    by_contra hle
    push Not at hle
    have h1 := mul_nonneg (by linarith : (0 : ℝ) ≤ m) (neg_nonneg.2 hle)
    nlinarith
  rw [hfW] at hfin
  exact hfin
end GlobalTheory.ProperImmersionPoint
