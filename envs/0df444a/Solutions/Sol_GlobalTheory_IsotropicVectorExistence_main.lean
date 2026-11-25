-- Prove2me | solution 1 for GlobalTheory.IsotropicVectorExistence.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:56:10.968335+00:00
-- url     : https://prove2.me/submissions/6d1b39a8-7e16-4bd0-a8d9-5788cdf27f1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsBisLast
import Theorems.Thm_GlobalTheory_IsotropicVectorExistence_key

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
theorem _root_.solution : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ (by positivity)] at hk
  have a := key k h
  have b := h (2 ^ k)
  nlinarith
end GlobalTheory.IsotropicVectorExistence
