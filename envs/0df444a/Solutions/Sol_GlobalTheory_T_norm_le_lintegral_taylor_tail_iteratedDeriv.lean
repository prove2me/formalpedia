-- Prove2me | solution 1 for GlobalTheory.T.norm_le_lintegral_taylor_tail_iteratedDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:50.854608+00:00
-- url     : https://prove2.me/submissions/1ed2b17f-5176-4525-ac74-52fc5f4099c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralTaylorTailIteratedDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralTaylorTailIteratedDerivStatement
import Theorems.Thm_GlobalTheory_taylorTail_bound


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (h : ℝ → F) (m : ℕ), ContDiff ℝ (⊤ : ℕ∞) h → (∀ j ≤ m, Tendsto (iteratedDeriv j h) atTop (𝓝 0)) → ENNReal.ofReal ‖h 0‖ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ)) * ‖iteratedDeriv (m + 1) h t‖ₑ := by
  first | exact @GlobalTheory.taylorTail_bound | exact GlobalTheory.taylorTail_bound | (intros; apply GlobalTheory.taylorTail_bound <;> assumption)
end _root_.GlobalTheory.T
