-- Prove2me | solution 1 for GlobalTheory.PositiveFormRecursion.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:43:46.997034+00:00
-- url     : https://prove2.me/submissions/026d8106-fe2f-4ce9-9967-7afbe5306219

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsBisSide
import Theorems.Thm_GlobalTheory_PositiveFormRecursion_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PositiveFormRecursion
namespace GlobalTheory.PositiveFormRecursion
theorem _root_.solution : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ (2 : ℕ) ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z hz
  have key : ∀ n : ℕ, (3/2 : ℝ) ^ n * ‖z - 1‖ ≤ ‖z ^ (2 : ℕ) ^ n - 1‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : z ^ (2 : ℕ) ^ (n + 1) = (z ^ (2 : ℕ) ^ n) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e]
      have hs := step (z ^ (2 : ℕ) ^ n) (hz n)
      calc (3/2 : ℝ) ^ (n + 1) * ‖z - 1‖ = (3/2) * ((3/2) ^ n * ‖z - 1‖) := by ring
        _ ≤ (3/2) * ‖z ^ (2 : ℕ) ^ n - 1‖ := by gcongr
        _ ≤ _ := hs
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3/2)
  have hn' := (div_lt_iff₀ (by positivity)).mp hn
  have h1 := key n
  have h2 := hz n
  nlinarith
end GlobalTheory.PositiveFormRecursion
