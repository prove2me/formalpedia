-- Prove2me | solution 1 for GlobalTheory.IterationConvergence.iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:57:29.656707+00:00
-- url     : https://prove2.me/submissions/7b646f8a-45b3-4412-aa01-2353d520d3e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsTer
import Theorems.Thm_GlobalTheory_IterationConvergence_step

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
theorem _root_.solution {z : ℂ} (hz : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) (k : ℕ) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := step (z ^ (2 ^ k)) (hz _)
    have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [e, pow_succ]
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = (3 / 2) * ((3 / 2) ^ k * ‖z - 1‖) := by ring
      _ ≤ (3 / 2) * ‖z ^ (2 ^ k) - 1‖ := by gcongr
      _ ≤ _ := hs
end GlobalTheory.IterationConvergence
