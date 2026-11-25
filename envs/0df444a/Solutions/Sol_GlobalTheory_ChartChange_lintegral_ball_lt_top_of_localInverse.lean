-- Prove2me | solution 1 for GlobalTheory.ChartChange.lintegral_ball_lt_top_of_localInverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:30.235863+00:00
-- url     : https://prove2.me/submissions/c0343d21-af5e-4ba7-b61b-d0a6ed35e7f1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralBallLtTopOfLocalInverse
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
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
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn
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
open GlobalTheory GlobalTheory.ChartChange
open Filter
namespace GlobalTheory.ChartChange
theorem _root_.solution {n : ℕ} (η θ : V n → V n) {U : Set (V n)} (hU : IsOpen U)
    (h0 : (0 : V n) ∈ U) (hη : DifferentiableOn ℂ η U) (hθ : ContinuousAt θ 0) (hθ0 : θ 0 = 0)
    (hηθ : ∀ᶠ z in 𝓝 (0 : V n), η (θ z) = z) (hθη : ∀ᶠ w in 𝓝 (0 : V n), θ (η w) = w)
    (g h : V n → ℝ≥0∞) (hgh : ∀ w ∈ U, g (η w) = h w) {ρ : ℝ} (hρ : 0 < ρ)
    (hint : ∫⁻ w in Metric.ball (0 : V n) ρ, h w < ⊤) :
    ∃ S ∈ 𝓝 (0 : V n), ∫⁻ z in S, g z < ⊤ := by
  have hcd : ContDiffOn ℝ ∞ η U := by
    refine (contDiffOn_piLp 2).2 fun i => ?_
    have hi : DifferentiableOn ℂ (fun z => η z i) U := (differentiableOn_piLp 2).1 hη i
    exact (contDiffOn_of_differentiableOn n _ U hU hi).restrict_scalars ℝ
  have hfc : ContinuousAt (fun w => |(fderiv ℝ η w).det|) 0 := by
    have h1 : ContinuousOn (fderiv ℝ η) U := hcd.continuousOn_fderiv_of_isOpen hU (by simp)
    exact (ContinuousLinearMap.continuous_det.continuousAt.comp (h1.continuousAt (hU.mem_nhds h0))).abs
  set C : ℝ := |(fderiv ℝ η 0).det| + 1 with hC
  have hb : ∀ᶠ w in 𝓝 (0 : V n), |(fderiv ℝ η w).det| < C := hfc.eventually_lt continuousAt_const (by simp [hC])
  have hall : ∀ᶠ w in 𝓝 (0 : V n), w ∈ U ∧ w ∈ Metric.ball (0 : V n) ρ ∧ θ (η w) = w ∧
      |(fderiv ℝ η w).det| < C := by
    filter_upwards [hU.mem_nhds h0, Metric.ball_mem_nhds (0 : V n) hρ, hθη, hb] with w a b c d
    exact ⟨a, b, c, d⟩
  obtain ⟨δ, hδ, hB⟩ := Metric.eventually_nhds_iff_ball.1 hall
  refine ⟨η '' Metric.ball 0 δ, ?_, ?_⟩
  · have h1 : ∀ᶠ z in 𝓝 (0 : V n), θ z ∈ Metric.ball (0 : V n) δ :=
      hθ.eventually (by rw [hθ0]; exact Metric.ball_mem_nhds _ hδ)
    filter_upwards [h1, hηθ] with z hz1 hz2
    exact ⟨θ z, hz1, hz2⟩
  · have hd : ∀ w ∈ Metric.ball (0 : V n) δ,
        HasFDerivWithinAt η (fderiv ℝ η w) (Metric.ball (0 : V n) δ) w := fun w hw =>
      (((hcd.differentiableOn (by simp)).differentiableAt
        (hU.mem_nhds (hB w hw).1)).hasFDerivAt).hasFDerivWithinAt
    have hinj : Set.InjOn η (Metric.ball (0 : V n) δ) := fun w hw w' hw' e => by
      rw [← (hB w hw).2.2.1, e, (hB w' hw').2.2.1]
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball hd hinj]
    calc ∫⁻ w in Metric.ball (0 : V n) δ, ENNReal.ofReal |(fderiv ℝ η w).det| * g (η w)
        ≤ ∫⁻ w in Metric.ball (0 : V n) δ, ENNReal.ofReal C * h w := by
          refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
          rw [hgh w (hB w hw).1]
          gcongr
          exact (hB w hw).2.2.2.le
      _ = ENNReal.ofReal C * ∫⁻ w in Metric.ball (0 : V n) δ, h w :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * ∫⁻ w in Metric.ball (0 : V n) ρ, h w := by
          exact mul_le_mul_right (lintegral_mono_set fun w hw => (hB w hw).2.1) _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
end GlobalTheory.ChartChange
