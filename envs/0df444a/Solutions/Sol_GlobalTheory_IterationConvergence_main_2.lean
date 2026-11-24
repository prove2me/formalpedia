-- Prove2me | solution 2 for GlobalTheory.IterationConvergence.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:27.447214+00:00
-- url     : https://prove2.me/submissions/4bbc9587-c9ad-4682-afa5-47ec593d8f27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsTer
import Theorems.Thm_GlobalTheory_IterationConvergence_iter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IterationConvergence
namespace GlobalTheory.IterationConvergence
theorem _root_.solution : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z hz
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := iter hz k
  have h2 := hz (2 ^ k)
  rw [div_lt_iff₀ hpos] at hk
  linarith
end GlobalTheory.IterationConvergence
