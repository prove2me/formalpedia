-- Prove2me | solution 1 for GlobalTheory.WeightedInverseBound.norm_le_of_coercive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:23:18.596881+00:00
-- url     : https://prove2.me/submissions/1d8fc062-7558-429b-87e0-cc1047d056ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBound
import Theorems.Thm_GlobalTheory_WeightedInverseBound_dot_le_card_mul_norm_mul_norm
import Theorems.Thm_GlobalTheory_WeightedInverseBound_norm_sq_le_dot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory
open GlobalTheory.WeightedInverseBound
namespace GlobalTheory.WeightedInverseBound
theorem _root_.solution {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {c : ℝ} (hc : 0 < c)
    (hY : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y.mulVec x) (z : Fin g → ℝ) :
    ‖z‖ ≤ g / c * ‖Y.mulVec z‖ := by
  rcases (norm_nonneg z).eq_or_lt with h | h
  · rw [← h]; positivity
  have h1 := hY z
  have h2 := dot_le_card_mul_norm_mul_norm z (Y.mulVec z)
  have h3 := norm_sq_le_dot z
  have h4 : ‖z‖ * (c * ‖z‖) ≤ ‖z‖ * (g * ‖Y.mulVec z‖) := by nlinarith
  have h5 := le_of_mul_le_mul_left h4 h
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  linarith
end GlobalTheory.WeightedInverseBound
