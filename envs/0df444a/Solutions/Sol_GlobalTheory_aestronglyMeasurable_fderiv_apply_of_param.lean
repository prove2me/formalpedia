-- Prove2me | solution 1 for GlobalTheory.aestronglyMeasurable_fderiv_apply_of_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:22:17.104644+00:00
-- url     : https://prove2.me/submissions/318ca147-91bd-4039-939a-34076d8e20ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped Topology Interval
open GlobalTheory
variable {T : Type*} [MeasurableSpace T] {μ : Measure T}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution {F : T → E → V} {x₀ : E}
    (hmeas : ∀ᶠ y in 𝓝 x₀, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀) (v : E) :
    AEStronglyMeasurable (fun t => fderiv ℂ (F t) x₀ v) μ := by
  classical
  let f : ℂ → T → V := fun c t =>
    if AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ then
      c⁻¹ • (F t (x₀ + c • v) - F t x₀) else 0
  have h0 : AEStronglyMeasurable (fun t => F t x₀) μ := hmeas.self_of_nhds
  have hev : ∀ᶠ c : ℂ in 𝓝[≠] 0, AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ := by
    have hc : Tendsto (fun c : ℂ => x₀ + c • v) (𝓝 0) (𝓝 x₀) := by
      have : Continuous (fun c : ℂ => x₀ + c • v) := by fun_prop
      simpa using this.tendsto 0
    exact (hc.eventually hmeas).filter_mono nhdsWithin_le_nhds
  refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ)) (f := f) (fun c => ?_) ?_
  · by_cases h : AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ
    · simp only [f, if_pos h]
      exact (h.sub h0).const_smul c⁻¹
    · simp only [f, if_neg h]
      exact aestronglyMeasurable_const
  · filter_upwards [hdiff] with t ht
    have h1 := hasLineDerivAt_iff_tendsto_slope_zero.1 (ht.hasFDerivAt.hasLineDerivAt v)
    refine h1.congr' ?_
    filter_upwards [hev] with c hc
    simp only [f, if_pos hc]
end GlobalTheory
