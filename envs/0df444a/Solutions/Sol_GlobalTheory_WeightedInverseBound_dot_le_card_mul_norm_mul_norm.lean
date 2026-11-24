-- Prove2me | solution 1 for GlobalTheory.WeightedInverseBound.dot_le_card_mul_norm_mul_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:14:41.173342+00:00
-- url     : https://prove2.me/submissions/dc5efc30-9af1-4910-8a41-d7dd3845d92d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBound

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
theorem _root_.solution {g : ℕ} (x y : Fin g → ℝ) : x ⬝ᵥ y ≤ g * (‖x‖ * ‖y‖) := by
  calc x ⬝ᵥ y = ∑ k, x k * y k := rfl
    _ ≤ ∑ _k : Fin g, ‖x‖ * ‖y‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        exact mul_le_mul (norm_le_pi_norm x k) (norm_le_pi_norm y k) (abs_nonneg _)
          (norm_nonneg _)
    _ = g * (‖x‖ * ‖y‖) := by simp
end GlobalTheory.WeightedInverseBound
