-- Prove2me | solution 1 for GlobalTheory.KeyLemmaTwo.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:47:02.739992+00:00
-- url     : https://prove2.me/submissions/2eddc27f-2f92-4b7e-a8d7-418678ec29d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ImportsAlt
import Theorems.Thm_GlobalTheory_KeyLemmaTwo_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KeyLemmaTwo
namespace GlobalTheory.KeyLemmaTwo
theorem _root_.solution : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := key h k
  have h2 := h (2 ^ k)
  rw [div_lt_iff₀ hpos] at hk
  linarith
end GlobalTheory.KeyLemmaTwo
