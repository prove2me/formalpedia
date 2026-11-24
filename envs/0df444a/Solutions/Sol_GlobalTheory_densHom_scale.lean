-- Prove2me | solution 1 for GlobalTheory.densHom_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:35:28.141587+00:00
-- url     : https://prove2.me/submissions/0860d26b-79c5-4cc6-9f59-779116589946

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDensityOriginOfAlmostHomogeneous
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open MeasureTheory Filter Topology Matrix
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (l : Measure V) [l.IsAddHaarMeasure] (x : V) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) :
    l (Metric.closedBall x (s * r)) =
      ENNReal.ofReal (s ^ Module.finrank ℝ V) * l (Metric.ball 0 r) := by
  rw [Measure.addHaar_closedBall_mul_of_pos l x hs r, Measure.addHaar_closedBall l 0 hr.le,
    Measure.addHaar_ball_of_pos l 0 hr]
end _root_.GlobalTheory
end GlobalTheory
