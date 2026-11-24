-- Prove2me | solution 1 for GlobalTheory.rayAvg_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:37:44.174995+00:00
-- url     : https://prove2.me/submissions/3f7604b6-5475-493e-9a0b-d3ff786e6dc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralUnitBallRayAverageLe
import Theorems.Thm_GlobalTheory_rayAvg_inner
import Theorems.Thm_GlobalTheory_rayAvg_radial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (Ψ : E → ℝ≥0∞) (m : ℕ), Measurable Ψ → finrank ℝ E = m + 1 → ∫⁻ v in Metric.closedBall (0:E) 1, ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂volume ∂μ ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ := by
  intro E _ _ _ _ _ μ _ Ψ m hΨ hd
  have hF : Measurable fun p : E × ℝ => ENNReal.ofReal (p.2 ^ m * ‖p.1‖ ^ (m + 1)) * Ψ (p.2 • p.1) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hΨ.comp (measurable_snd.smul measurable_fst))
  have hK : Measurable fun p : ℝ × E =>
      (if ‖p.2‖ ≤ p.1 then ENNReal.ofReal (‖p.2‖ ^ (m + 1) / p.1 ^ (m + 2)) * Ψ p.2 else 0) := by
    refine Measurable.ite (measurableSet_le (measurable_norm.comp measurable_snd) measurable_fst) ?_
      measurable_const
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hΨ.comp measurable_snd)
  calc ∫⁻ v in Metric.closedBall (0:E) 1, ∫⁻ t in Ioi (0:ℝ),
        ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂volume ∂μ
      = ∫⁻ t in Ioi (0:ℝ), (∫⁻ v in Metric.closedBall (0:E) 1,
        ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂μ) := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ t in Ioi (0:ℝ), (∫⁻ y,
        (if ‖y‖ ≤ t then ENNReal.ofReal (‖y‖ ^ (m + 1) / t ^ (m + 2)) * Ψ y else 0) ∂μ) :=
        setLIntegral_congr_fun measurableSet_Ioi (fun t ht => rayAvg_inner μ Ψ m hΨ hd ht)
    _ = ∫⁻ y, (∫⁻ t in Ioi (0:ℝ),
        (if ‖y‖ ≤ t then ENNReal.ofReal (‖y‖ ^ (m + 1) / t ^ (m + 2)) * Ψ y else 0)) ∂μ :=
        lintegral_lintegral_swap hK.aemeasurable
    _ ≤ ∫⁻ y, ENNReal.ofReal (1 / ((m : ℝ) + 1)) * Ψ y ∂μ :=
        lintegral_mono (fun y => rayAvg_radial m (norm_nonneg y) (Ψ y))
    _ = ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ := lintegral_const_mul _ hΨ
end GlobalTheory
