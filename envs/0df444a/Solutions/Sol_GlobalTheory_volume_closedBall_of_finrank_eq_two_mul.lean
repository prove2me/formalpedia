-- Prove2me | solution 1 for GlobalTheory.volume_closedBall_of_finrank_eq_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:43:15.967937+00:00
-- url     : https://prove2.me/submissions/bf4b58ee-b020-4283-bbbb-da21c94b5863

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_volume_ball_of_finrank_eq_two_mul

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution {D : ℕ} (hD : Module.finrank ℝ E = 2 * D) (a : E)
    {r : ℝ} (hr : 0 < r) :
    volume (closedBall a r) = ENNReal.ofReal (π ^ D * r ^ (2 * D) / D.factorial) := by
  rw [← volume_ball_of_finrank_eq_two_mul hD a hr]
  rcases subsingleton_or_nontrivial E with hE | hE
  · congr 1
    ext z
    rw [Subsingleton.elim z a]
    simp [hr, hr.le]
  · exact Measure.addHaar_closedBall_eq_addHaar_ball _ _ _
end GlobalTheory
