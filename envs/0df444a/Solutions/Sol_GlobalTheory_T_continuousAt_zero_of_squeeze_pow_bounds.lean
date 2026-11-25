-- Prove2me | solution 1 for GlobalTheory.T.continuousAt_zero_of_squeeze_pow_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:39:45.948064+00:00
-- url     : https://prove2.me/submissions/143873ba-93f7-404c-a329-b3b720e29695

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ContinuousAtZeroOfSqueezePowBounds
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ContinuousAtZeroOfSqueezePowBoundsStatement

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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (f : V → ℝ≥0∞) (c : ℝ≥0∞), c ≠ ⊤ → (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) → f 0 = c ∧ ContinuousAt f 0 := by
  first | exact @GlobalTheory.squeeze_continuousAt_zero | exact GlobalTheory.squeeze_continuousAt_zero | (intros; apply GlobalTheory.squeeze_continuousAt_zero <;> assumption)
end _root_.GlobalTheory.T
