-- Prove2me | solution 1 for GlobalTheory.exists_const_ratio_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:38:03.01815+00:00
-- url     : https://prove2.me/submissions/e43540ee-6ba8-4bb6-b504-938ccb6b65eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsConstRatioOfNormEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (I : Type) (T K : ℝ) (f g : I → ℂ → ℂ) (c : ℂ → ℂ), 0 < K →
      (∀ i, DifferentiableOn ℂ (f i) {w | T < w.im} ∧ DifferentiableOn ℂ (g i) {w | T < w.im}) →
      (∀ i w, T < w.im → f i w = c w * g i w ∧ ‖f i w‖ = K * ‖g i w‖) →
      ∃ κ : ℂ, ‖κ‖ = K ∧ ∀ i w, T < w.im → f i w = κ * g i w := by
  intro I T K f g c hK hd h
  by_cases h0 : ∀ i w, T < w.im → g i w = 0
  · refine ⟨K, by simp [abs_of_pos hK], fun i w hw => ?_⟩
    rw [(h i w hw).1, h0 i w hw]; simp
  push_neg at h0
  obtain ⟨i₀, w₀, hw₀, hg₀⟩ := h0
  have hU : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected {w : ℂ | T < w.im} := (convex_halfSpace_im_gt T).isPreconnected
  have hca : ContinuousAt (g i₀) w₀ :=
    (hd i₀).2.continuousOn.continuousAt (hU.mem_nhds hw₀)
  have hev : ∀ᶠ w in nhds w₀, T < w.im ∧ g i₀ w ≠ 0 :=
    (hU.eventually_mem hw₀).and (hca.eventually_ne hg₀)
  obtain ⟨r, hr, hB⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hsub : Metric.ball w₀ r ⊆ {w : ℂ | T < w.im} := fun w hw => (hB w hw).1
  have hcq : ∀ w ∈ Metric.ball w₀ r, c w = f i₀ w / g i₀ w := fun w hw => by
    rw [(h i₀ w (hB w hw).1).1, mul_div_cancel_right₀ _ (hB w hw).2]
  have hcd : DifferentiableOn ℂ c (Metric.ball w₀ r) :=
    (((hd i₀).1.mono hsub).div ((hd i₀).2.mono hsub) fun w hw => (hB w hw).2).congr hcq
  have hcn : ∀ w ∈ Metric.ball w₀ r, ‖c w‖ = K := fun w hw => by
    rw [hcq w hw, norm_div, (h i₀ w (hB w hw).1).2,
      mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 (hB w hw).2)]
  have hm : w₀ ∈ Metric.ball w₀ r := Metric.mem_ball_self hr
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (convex_ball w₀ r).isPreconnected Metric.isOpen_ball hcd hm
    (fun w hw => by
      show ‖c w‖ ≤ ‖c w₀‖
      rw [hcn w hw, hcn w₀ hm])
  refine ⟨c w₀, hcn w₀ hm, fun i w hw => ?_⟩
  have ha : AnalyticOnNhd ℂ (f i) {w : ℂ | T < w.im} := (hd i).1.analyticOnNhd hU
  have hb : AnalyticOnNhd ℂ (fun w => c w₀ * g i w) {w : ℂ | T < w.im} :=
    ((hd i).2.const_mul (c w₀)).analyticOnNhd hU
  have he : f i =ᶠ[nhds w₀] fun w => c w₀ * g i w := by
    filter_upwards [Metric.ball_mem_nhds w₀ hr] with z hz
    rw [(h i z (hB z hz).1).1, hconst hz]
    rfl
  exact ha.eqOn_of_preconnected_of_eventuallyEq hb hUc hw₀ he hw
end GlobalTheory
