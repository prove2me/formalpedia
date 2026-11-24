-- Prove2me | solution 1 for GlobalTheory.LogExt.differentiableAt_lineIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:51:56.930038+00:00
-- url     : https://prove2.me/submissions/bbab39c3-16ef-42ae-82fc-d6aa6db61adf

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannExtensionOfLogGrowth

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory.LogExt
theorem _root_.solution {Ω : Set V} {u : V → ℂ}
    (hu : AnalyticOnNhd ℂ u Ω) {b₀ v : V} {R : ℝ} (hR : 0 < R)
    (hs : ∀ t ∈ sphere (0 : ℂ) R, b₀ + t • v ∈ Ω) :
    DifferentiableAt ℂ (fun b => ∮ t in C(0, R), t⁻¹ • u (b + t • v)) b₀ := by
  have hcf : ContinuousOn (fun t : ℂ => fderiv ℂ u (b₀ + t • v)) (sphere 0 R) :=
    hu.fderiv.continuousOn.comp (by fun_prop) hs
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn hcf
  have hev : ∀ᶠ b in 𝓝 b₀, ∀ t ∈ sphere (0 : ℂ) R,
      AnalyticAt ℂ u (b + t • v) ∧ ‖fderiv ℂ u (b + t • v)‖ < M + 1 := by
    refine (isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually fun t ht => ?_
    have hc : ContinuousAt (fun p : V × ℂ => p.1 + p.2 • v) (b₀, t) := by fun_prop
    have ha := hu _ (hs t ht)
    have h1 : ∀ᶠ x in 𝓝 (b₀ + t • v), ‖fderiv ℂ u x‖ < M + 1 :=
      ha.fderiv.continuousAt.norm.eventually (gt_mem_nhds (lt_add_of_le_of_pos (hM t ht) one_pos))
    exact hc.eventually (ha.eventually_analyticAt.and h1)
  have hm : ∀ θ : ℝ, circleMap 0 R θ ∈ sphere (0 : ℂ) R := fun θ => circleMap_mem_sphere 0 hR.le θ
  have hw : Continuous fun θ : ℝ => deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹ := by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).mul continuous_const).mul
      ((continuous_circleMap 0 R).inv₀ fun θ => circleMap_ne_center hR.ne')
  have hwn : ∀ θ : ℝ, ‖deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹‖ = 1 := fun θ => by
    simp [deriv_circleMap, abs_of_pos hR, hR.ne']
  have hcont : ∀ b, (∀ t ∈ sphere (0 : ℂ) R, AnalyticAt ℂ u (b + t • v)) →
      Continuous fun θ : ℝ => (deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹) •
        u (b + circleMap 0 R θ • v) := fun b hb => by
    refine hw.smul (continuous_iff_continuousAt.mpr fun θ => ?_)
    exact ContinuousAt.comp (f := fun θ : ℝ => b + circleMap 0 R θ • v)
      (hb _ (hm θ)).continuousAt (by fun_prop)
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (μ := MeasureTheory.volume) (a := 0) (b := 2 * π) (bound := fun _ => M + 1)
    (F := fun b θ => (deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹) • u (b + circleMap 0 R θ • v))
    (F' := fun b θ => (deriv (circleMap 0 R) θ * (circleMap 0 R θ)⁻¹) •
      fderiv ℂ u (b + circleMap 0 R θ • v)) hev
    (hev.mono fun b hb => (hcont b fun t ht => (hb t ht).1).aestronglyMeasurable)
    ((hcont b₀ fun t ht => hu _ (hs t ht)).intervalIntegrable _ _)
    ((hw.smul (hcf.comp_continuous (continuous_circleMap 0 R) hm)).aestronglyMeasurable)
    (Eventually.of_forall fun θ _ b hb => by
      rw [norm_smul, hwn, one_mul]; exact (hb _ (hm θ)).2.le)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ b hb => by
      have h1 := (hb _ (hm θ)).1.differentiableAt.hasFDerivAt
      exact ((hasFDerivAt_comp_add_right _).mpr h1).fun_const_smul _)
  refine key.differentiableAt.congr_of_eventuallyEq (Eventually.of_forall fun b => ?_)
  simp only [circleIntegral, smul_eq_mul, mul_assoc]
end GlobalTheory.LogExt
