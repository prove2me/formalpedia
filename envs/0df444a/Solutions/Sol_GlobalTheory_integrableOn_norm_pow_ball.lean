-- Prove2me | solution 1 for GlobalTheory.integrableOn_norm_pow_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:01:25.321328+00:00
-- url     : https://prove2.me/submissions/9e3a8453-6623-4d40-b7e9-0532d29906fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall

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
theorem _root_.solution {H : Type*} [NormedAddCommGroup H] (μ : Measure E)
    [μ.IsAddHaarMeasure] {a : E} {r : ℝ} {φ : E → H} (hφ : ContinuousOn φ (closedBall a r))
    (n : ℕ) : IntegrableOn (fun z => ‖φ z‖ ^ n) (ball a r) μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  exact ((hφ.norm.pow n).integrableOn_compact (isCompact_closedBall a r)).mono_set
    ball_subset_closedBall
end GlobalTheory
