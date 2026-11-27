-- Prove2me | solution 1 for GlobalTheory.locallyIntegrableOn_log_norm_of_frequently_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:41:26.648738+00:00
-- url     : https://prove2.me/submissions/33471f6b-a6da-4cf3-943c-4a5d60478a5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableOnOfNormLeSumAbsLogAddLogLog
import Theorems.Thm_GlobalTheory_exists_integrableOn_log_norm_of_frequently_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℂ} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hx : ∀ x ∈ U, ∃ᶠ z in 𝓝 x, f z ≠ 0) :
    (∀ᵐ z ∂(μ.restrict U), f z ≠ 0) ∧ LocallyIntegrableOn (fun z => Real.log ‖f z‖) U μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h : ∀ x ∈ U, ∃ r > 0, (∀ᵐ z ∂(μ.restrict (ball x r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball x r) μ := fun x hxU =>
    exists_integrableOn_log_norm_of_frequently_ne_zero μ
      (hf.eventually_differentiableAt (hU.mem_nhds hxU)) (hx x hxU)
  refine ⟨?_, fun x hxU => ?_⟩
  · rw [ae_restrict_iff'₀ hU.measurableSet.nullMeasurableSet, ae_iff]
    refine measure_null_of_locally_null _ fun x hx' => ?_
    have hxU : x ∈ U := by
      by_contra hn
      exact hx' fun h => absurd h hn
    obtain ⟨r, hr, h1, -⟩ := h x hxU
    rw [ae_restrict_iff' measurableSet_ball, ae_iff] at h1
    refine ⟨_ ∩ ball x r, inter_mem_nhdsWithin _ (ball_mem_nhds x hr), measure_mono_null ?_ h1⟩
    rintro z ⟨hz, hzb⟩ hz'
    exact hz fun _ => hz' hzb
  · obtain ⟨r, hr, -, h2⟩ := h x hxU
    exact ⟨ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr), h2⟩
end GlobalTheory
