-- Prove2me | solution 1 for GlobalTheory.T.exponent_divisor_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:01:01.321835+00:00
-- url     : https://prove2.me/submissions/b4de66d3-405f-4771-bedb-f3c1b9d67207

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExponentDivisorSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExponentBookkeepingDivisorSumLeStatement
import Theorems.Thm_GlobalTheory_exponent_sum_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k f r : ℕ) (G N H a Q C : ℝ), 1 ≤ k → 1 ≤ r → 1 ≤ f → Real.log f ≤ Real.sqrt r → 1 ≤ G → 1 ≤ N → G ≤ H → N ≤ H → 0 ≤ a → 0 ≤ Q → Q * 9 ^ f ≤ H → 60 ≤ C → ∑ de ∈ Finset.Icc 1 ⌊G⌋₊, ((de : ℝ) / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * Real.logb 2 f)) * ((G / de) ^ ((k : ℝ) + Real.logb 2 (2 * f) + 1) * (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by
  first | exact @GlobalTheory.exponent_sum_le | exact GlobalTheory.exponent_sum_le | (intros; apply GlobalTheory.exponent_sum_le <;> assumption)
end _root_.GlobalTheory.T
