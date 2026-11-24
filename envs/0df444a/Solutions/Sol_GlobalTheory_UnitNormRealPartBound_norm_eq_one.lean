-- Prove2me | solution 1 for GlobalTheory.UnitNormRealPartBound.norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:03:08.448014+00:00
-- url     : https://prove2.me/submissions/f9a2f4f7-3b58-4758-bb9b-8869693b20a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReGt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitNormRealPartBound
namespace GlobalTheory.UnitNormRealPartBound
theorem _root_.solution {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) : ‖z‖ = 1 := by
  have hup : ∀ n : ℕ, ‖z‖ ^ n < 3 / 2 := fun n => by
    have := h n
    calc ‖z‖ ^ n = ‖(z ^ n - 1) + 1‖ := by rw [sub_add_cancel, norm_pow]
      _ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ < 3 / 2 := by rw [norm_one]; linarith
  have hlo : ∀ n : ℕ, 1 / 2 < ‖z‖ ^ n := fun n => by
    have := h n
    have h2 : ‖(1 : ℂ)‖ ≤ ‖z ^ n - 1‖ + ‖z ^ n‖ := by
      calc ‖(1 : ℂ)‖ = ‖-(z ^ n - 1) + z ^ n‖ := by ring_nf
        _ ≤ ‖-(z ^ n - 1)‖ + ‖z ^ n‖ := norm_add_le _ _
        _ = ‖z ^ n - 1‖ + ‖z ^ n‖ := by rw [norm_neg]
    rw [norm_one, norm_pow] at h2
    linarith
  rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) h1
    linarith [hlo n]
  · exact h1
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 / 2 : ℝ) h1
    linarith [hup n]
end GlobalTheory.UnitNormRealPartBound
