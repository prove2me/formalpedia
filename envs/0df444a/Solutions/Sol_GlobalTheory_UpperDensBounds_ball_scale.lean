-- Prove2me | solution 1 for GlobalTheory.UpperDensBounds.ball_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:31:04.503063+00:00
-- url     : https://prove2.me/submissions/9a644225-1820-4942-aa9a-6cbd584fdf13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDensityBoundsAlmostHomogeneousMeasure

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
open GlobalTheory GlobalTheory.UpperDensBounds
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.UpperDensBounds
theorem _root_.solution (l : Measure V) [l.IsAddHaarMeasure] (x : V) {k s : ℝ} (hk : 0 < k) (hs : 0 < s) :
    l (Metric.ball 0 (k * s)) = ENNReal.ofReal (k ^ Module.finrank ℝ V) * l (Metric.closedBall x s) := by
  rw [Measure.addHaar_ball_of_pos l 0 (mul_pos hk hs), Measure.addHaar_closedBall l x hs.le, mul_pow,
    ENNReal.ofReal_mul (by positivity), mul_assoc]
end GlobalTheory.UpperDensBounds
