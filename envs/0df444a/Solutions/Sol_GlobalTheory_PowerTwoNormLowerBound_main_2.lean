-- Prove2me | solution 2 for GlobalTheory.PowerTwoNormLowerBound.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:44:40.491841+00:00
-- url     : https://prove2.me/submissions/4a27ff5f-1c1d-4040-867f-e9291303fa33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormPowTwoPowSubOneGe
import Theorems.Thm_GlobalTheory_PowerTwoNormLowerBound_norm_pow_two_pow_sub_one_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerTwoNormLowerBound
namespace GlobalTheory.PowerTwoNormLowerBound
theorem _root_.solution : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 : (1 / 2 : ℝ) < (3 / 2 : ℝ) ^ k * ‖z - 1‖ := (div_lt_iff₀ hpos).mp hk
  have h2 := norm_pow_two_pow_sub_one_ge h k
  have h3 := h (2 ^ k)
  linarith
end GlobalTheory.PowerTwoNormLowerBound
