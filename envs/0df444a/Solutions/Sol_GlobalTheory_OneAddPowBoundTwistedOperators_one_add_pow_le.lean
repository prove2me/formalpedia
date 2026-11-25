-- Prove2me | solution 1 for GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:04:10.127156+00:00
-- url     : https://prove2.me/submissions/77da6618-5ffd-4494-af42-277b503552d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ImportsBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OneAddPowBoundTwistedOperators
namespace GlobalTheory.OneAddPowBoundTwistedOperators
theorem _root_.solution : ∀ {L : ℝ}, (0 : ℝ) ≤ L → ∀ (N : ℕ), ((1 : ℝ) + L) ^ N ≤ (2 : ℝ) ^ N * ((1 : ℝ) + L ^ N) := by
  intro L hL N
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ N := by positivity
  have hLN : (0 : ℝ) ≤ L ^ N := pow_nonneg hL N
  rcases le_total L 1 with h | h
  · have h1 : ((1 : ℝ) + L) ^ N ≤ (2 : ℝ) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    nlinarith
  · have h1 : ((1 : ℝ) + L) ^ N ≤ (2 * L) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    rw [mul_pow] at h1
    nlinarith
end GlobalTheory.OneAddPowBoundTwistedOperators
