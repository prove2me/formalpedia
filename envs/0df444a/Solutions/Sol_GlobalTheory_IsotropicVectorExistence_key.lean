-- Prove2me | solution 1 for GlobalTheory.IsotropicVectorExistence.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:29.563353+00:00
-- url     : https://prove2.me/submissions/25387ce9-cfd1-4306-88bf-47628a4124b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsBisLast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IsotropicVectorExistence
namespace GlobalTheory.IsotropicVectorExistence
theorem _root_.solution {z : ℂ} (k : ℕ) (h : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : z ^ (2 ^ (k + 1)) - 1 = (z ^ (2 ^ k) - 1) * (z ^ (2 ^ k) + 1) := by
      rw [show 2 ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul]; ring
    have h2 : (3 / 2 : ℝ) ≤ ‖z ^ (2 ^ k) + 1‖ := by
      have h3 : (2 : ℂ) = (z ^ (2 ^ k) + 1) - (z ^ (2 ^ k) - 1) := by ring
      have h4 : ‖(2 : ℂ)‖ ≤ ‖z ^ (2 ^ k) + 1‖ + ‖z ^ (2 ^ k) - 1‖ := by
        rw [h3]; exact norm_sub_le _ _
      have h5 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have h6 := h (2 ^ k)
      linarith
    rw [e, norm_mul, pow_succ]
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2) ^ k * ‖z - 1‖) * (3 / 2) := by ring
      _ ≤ ‖z ^ (2 ^ k) - 1‖ * ‖z ^ (2 ^ k) + 1‖ :=
        mul_le_mul ih h2 (by norm_num) (norm_nonneg _)
end GlobalTheory.IsotropicVectorExistence
