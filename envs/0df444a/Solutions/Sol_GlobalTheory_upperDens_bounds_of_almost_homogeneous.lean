-- Prove2me | solution 1 for GlobalTheory.upperDens_bounds_of_almost_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:40:36.30695+00:00
-- url     : https://prove2.me/submissions/ed158489-69a2-4eaa-aa3e-b36377904321

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDensityBoundsAlmostHomogeneousMeasure
import Theorems.Thm_GlobalTheory_UpperDensBounds_tendsto_const_mul_nhdsGT
import Theorems.Thm_GlobalTheory_UpperDensBounds_ball_scale
import Theorems.Thm_GlobalTheory_UpperDensBounds_mul_div_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
open GlobalTheory.UpperDensBounds
namespace GlobalTheory
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (c : ℝ≥0∞), c ≠ ⊤ → Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) → ∀ ε η : ℝ, 0 < ε → ε < 1 → (∀ x : V, ‖x‖ < η → ∀ᶠ r in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧ ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r))) → ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ Module.finrank ℝ V) * c ≤ GlobalTheory.HaarDensChart.upperDens l ν x ∧ GlobalTheory.HaarDensChart.upperDens l ν x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ Module.finrank ℝ V) * c := by
  intro V _ _ _ _ _ l ν _ _ c _ hc ε η h0 h1 H x hx
  have he : 0 < 1 - ε := by linarith
  have hp : 0 < 1 + ε := by linarith
  set d := Module.finrank ℝ V
  unfold GlobalTheory.HaarDensChart.upperDens
  constructor
  ·
    set u : ℝ := (1 + ε)⁻¹ with hu
    have hu0 : 0 < u := inv_pos.mpr hp
    have ht : Tendsto (fun s : ℝ => ENNReal.ofReal (u ^ d) *
        (ν (Metric.ball 0 (u * s)) / l (Metric.ball 0 (u * s)))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (u ^ d) * c)) :=
      ENNReal.Tendsto.const_mul (hc.comp (tendsto_const_mul_nhdsGT hu0)) (Or.inr ENNReal.ofReal_ne_top)
    rw [← ht.limsup_eq]
    refine limsup_le_limsup ?_
    filter_upwards [(tendsto_const_mul_nhdsGT hu0).eventually (H x hx), self_mem_nhdsWithin] with s hs hs0
    have hs0 : 0 < s := hs0
    rw [ball_scale l x hu0 hs0, mul_div_scale u hu0 d]
    refine ENNReal.div_le_div_right ?_ _
    have hr : (1 + ε) * (u * s) = s := by rw [hu, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    have := hs.2
    rw [hr] at this
    exact this.trans (measure_mono Metric.ball_subset_closedBall)
  ·
    set t : ℝ := (1 + ε) / (1 - ε) with htdef
    have ht0 : 0 < t := div_pos hp he
    have ht : Tendsto (fun s : ℝ => ENNReal.ofReal (t ^ d) *
        (ν (Metric.ball 0 (t * s)) / l (Metric.ball 0 (t * s)))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (t ^ d) * c)) :=
      ENNReal.Tendsto.const_mul (hc.comp (tendsto_const_mul_nhdsGT ht0)) (Or.inr ENNReal.ofReal_ne_top)
    rw [← ht.limsup_eq]
    refine limsup_le_limsup ?_
    filter_upwards [(tendsto_const_mul_nhdsGT ht0).eventually (H x hx), self_mem_nhdsWithin] with s hs hs0
    have hs0 : 0 < s := hs0
    rw [ball_scale l x ht0 hs0, mul_div_scale t ht0 d]
    refine ENNReal.div_le_div_right ?_ _
    have hr : (1 - ε) * (t * s) = (1 + ε) * s := by
      rw [htdef, ← mul_assoc, mul_div_cancel₀ _ he.ne']
    refine le_trans (measure_mono (Metric.closedBall_subset_ball ?_)) hs.1
    rw [hr]; nlinarith
end GlobalTheory
