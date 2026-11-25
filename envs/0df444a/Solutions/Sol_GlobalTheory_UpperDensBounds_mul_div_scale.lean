-- Prove2me | solution 1 for GlobalTheory.UpperDensBounds.mul_div_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:28:09.849508+00:00
-- url     : https://prove2.me/submissions/4dd7a960-34fb-4b5a-a5a6-81698cd37421

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
theorem _root_.solution (t : ℝ) (ht : 0 < t) (d : ℕ) (a b : ℝ≥0∞) :
    ENNReal.ofReal (t ^ d) * (a / (ENNReal.ofReal (t ^ d) * b)) = a / b := by
  have hp : ENNReal.ofReal (t ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hp ENNReal.ofReal_ne_top]
end GlobalTheory.UpperDensBounds
