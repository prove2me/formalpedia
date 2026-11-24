-- Prove2me | solution 1 for GlobalTheory.LogExt.cauchy_of_log_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:13:26.438804+00:00
-- url     : https://prove2.me/submissions/21abe742-0d42-459e-a3bc-61c8da211679

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannExtensionOfLogGrowth
import Theorems.Thm_GlobalTheory_LogExt_isLittleO_inv_of_log_growth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LogExt
open Filter Topology Asymptotics Metric Set Complex
open scoped Real
namespace GlobalTheory.LogExt
theorem _root_.solution {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hg0 : g 0 ≠ 0) (hgs : ∀ t ∈ sphere (0 : ℂ) R, g t ≠ 0)
    (hf : ∀ t ∈ closedBall (0 : ℂ) R, ∀ᶠ z in 𝓝 t, g z ≠ 0 → DifferentiableAt ℂ f z)
    (hb : ∀ t ∈ closedBall (0 : ℂ) R, ∃ (C : ℝ) (k : ℕ),
      ∀ᶠ z in 𝓝 t, g z ≠ 0 → ‖f z‖ ≤ C * (1 + |Real.log ‖g z‖|) ^ k) :
    (∮ t in C(0, R), t⁻¹ • f t) = (2 * π * I : ℂ) • f 0 := by
  classical
  set F : ℂ → ℂ := fun t => if g t = 0 then limUnder (𝓝[≠] t) f else f t with hF
  have hFf : ∀ t, g t ≠ 0 → F t = f t := fun t ht => by simp [hF, ht]
  have hd : DifferentiableOn ℂ F (closedBall 0 R) := by
    intro t ht
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases hgt : g t = 0
    · have hne : ¬ ∀ᶠ z in 𝓝 t, g z = 0 := fun h =>
        hg0 (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (convex_closedBall (0 : ℂ) R).isPreconnected ht h (mem_closedBall_self hR.le))
      have hev : ∀ᶠ z in 𝓝[≠] t, g z ≠ 0 :=
        (hg t ht).eventually_eq_zero_or_eventually_ne_zero.resolve_left hne
      rw [eventually_nhdsWithin_iff] at hev
      obtain ⟨C, k, hCk⟩ := hb t ht
      have hs := hev.and (hf t ht)
      have hD := Complex.differentiableOn_update_limUnder_of_isLittleO (f := f) hs
        (fun z hz => (hz.1.2 (hz.1.1 hz.2)).differentiableWithinAt)
        (isLittleO_inv_of_log_growth (hg t ht) hne hCk)
      refine (hD.differentiableAt hs).congr_of_eventuallyEq ?_
      filter_upwards [hev] with z hz
      by_cases hzt : z = t
      · subst hzt; simp [hF, hgt]
      · rw [Function.update_of_ne hzt, hFf z (hz hzt)]
    · refine ((hf t ht).self_of_nhds hgt).congr_of_eventuallyEq ?_
      filter_upwards [(hg t ht).continuousAt.eventually_ne hgt] with z hz using hFf z hz
  have h := hd.circleIntegral_sub_inv_smul (mem_ball_self hR)
  rw [hFf 0 hg0] at h
  rw [← h]
  refine circleIntegral.integral_congr hR.le fun t ht => ?_
  simp [hFf t (hgs t ht)]
end GlobalTheory.LogExt
