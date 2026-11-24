-- Prove2me | solution 1 for GlobalTheory.log_norm_le_circleAverage_log_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:19:02.271511+00:00
-- url     : https://prove2.me/submissions/329201d8-1edb-4247-b095-bf05bb8c122b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableOnOfNormLeSumAbsLogAddLogLog

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
namespace GlobalTheory
theorem _root_.solution {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall 0 1))
    (h0 : g 0 ≠ 0) : Real.log ‖g 0‖ ≤ Real.circleAverage (fun z => Real.log ‖g z‖) 0 1 := by
  have hg' : AnalyticOnNhd ℂ g (closedBall 0 |(1 : ℝ)|) := by simpa using hg
  rw [hg'.circleAverage_log_norm one_ne_zero h0, le_add_iff_nonneg_left]
  refine finsum_nonneg fun u => ?_
  by_cases hu : u ∈ closedBall (0 : ℂ) |(1 : ℝ)|
  · refine mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg' u) ?_
    rcases eq_or_ne u 0 with rfl | h
    · simp
    · refine Real.log_nonneg ?_
      have h1 : ‖u‖ ≤ 1 := by simpa using hu
      simpa using (one_le_inv₀ (norm_pos_iff.2 h)).2 h1
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
end GlobalTheory
