-- Prove2me | solution 1 for GlobalTheory.enorm_pow_mul_lintegral_le_of_circular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:46:59.47147+00:00
-- url     : https://prove2.me/submissions/f147a4fa-4f4e-441e-bcf3-cd1644dae742

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_enorm_pow_mul_le_lintegral_circle
import Theorems.Thm_GlobalTheory_measurePreserving_smul_of_norm_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set
open scoped ENNReal Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
namespace GlobalTheory
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] {S : Set E}
    (hS : MeasurableSet S) (hSc : ∀ c : ℂ, ‖c‖ = 1 → ∀ z ∈ S, c • z ∈ S) {φ : E → H}
    (hφc : ContinuousOn φ S) (hφ : ∀ z ∈ S, DiffContOnCl ℂ (fun c : ℂ => φ (c • z)) (ball 0 1))
    {w : E → ℝ≥0∞} (hw : Measurable w) (hwc : ∀ c : ℂ, ‖c‖ = 1 → ∀ z ∈ S, w (c • z) = w z)
    (n : ℕ) :
    ‖φ 0‖ₑ ^ n * ∫⁻ z in S, w z ∂μ ≤ ∫⁻ z in S, ‖φ z‖ₑ ^ n * w z ∂μ := by
  classical
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h2 : (0 : ℝ) < 2 * π := by positivity
  have hn : ∀ t, ‖circleMap 0 1 t‖ = 1 := fun t => by simp
  set g : E → ℝ≥0∞ := S.indicator fun z => ‖φ z‖ₑ ^ n * w z with hg
  have hgm : Measurable g := by
    have h1 : ContinuousOn (fun z => ‖φ z‖ₑ ^ n) S :=
      (ENNReal.continuous_pow n).comp_continuousOn hφc.enorm
    have h3 := (h1.measurable_piecewise (g := fun _ => 0) continuousOn_const hS).mul hw
    convert h3 using 1
    ext z
    by_cases hz : z ∈ S <;> simp [hg, hz]
  have hj : Measurable fun p : ℝ × E => g (circleMap 0 1 p.1 • p.2) := by
    refine hgm.comp (Continuous.measurable ?_)
    exact ((continuous_circleMap 0 1).comp continuous_fst).smul continuous_snd
  have hA : ∫⁻ t in Ioc 0 (2 * π), ∫⁻ z, g (circleMap 0 1 t • z) ∂μ =
      (∫⁻ z in S, ‖φ z‖ₑ ^ n * w z ∂μ) * ENNReal.ofReal (2 * π) := by
    have h4 : ∀ t, ∫⁻ z, g (circleMap 0 1 t • z) ∂μ = ∫⁻ z in S, ‖φ z‖ₑ ^ n * w z ∂μ := fun t => by
      rw [(measurePreserving_smul_of_norm_eq_one μ (hn t)).lintegral_comp hgm, hg,
        lintegral_indicator hS]
    simp [h4]
  rw [← ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.2 h2).ne' ENNReal.ofReal_ne_top, ← hA,
    lintegral_lintegral_swap hj.aemeasurable, mul_right_comm, ← lintegral_const_mul _ hw,
    ← lintegral_indicator hS]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ S
  · have h5 : ∀ t, g (circleMap 0 1 t • z) = ‖φ (circleMap 0 1 t • z)‖ₑ ^ n * w z := fun t => by
      rw [hg, indicator_of_mem (hSc _ (hn t) z hz), hwc _ (hn t) z hz]
    have h6 : Measurable fun t => ‖φ (circleMap 0 1 t • z)‖ₑ ^ n := by
      refine Continuous.measurable ((ENNReal.continuous_pow n).comp (Continuous.enorm ?_))
      exact hφc.comp_continuous ((continuous_circleMap 0 1).smul continuous_const)
        fun t => hSc _ (hn t) z hz
    simp only [indicator_of_mem hz, h5]
    rw [lintegral_mul_const _ h6]
    gcongr
    simpa using enorm_pow_mul_le_lintegral_circle (hφ z hz) n
  · simp [hz]
end GlobalTheory
