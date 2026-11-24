-- Prove2me | solution 1 for GlobalTheory.UltrametricPowerBound.pow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:43:33.936322+00:00
-- url     : https://prove2.me/submissions/a2c77093-b84f-4023-aa78-4d86b7678bba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubOneLe
import Theorems.Thm_GlobalTheory_UltrametricPowerBound_ultra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UltrametricPowerBound
variable {l : ℕ} [Fact (Nat.Prime l)]
namespace GlobalTheory.UltrametricPowerBound
theorem _root_.solution (w : ℚ_[l]) (hw : ‖w‖ ≤ 1) (k : ℕ) : ‖w ^ k - 1‖ ≤ ‖w - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : w ^ (k + 1) - 1 = w * (w ^ k - 1) + (w - 1) := by ring
    rw [e]
    refine (ultra _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    calc ‖w‖ * ‖w ^ k - 1‖ ≤ 1 * ‖w ^ k - 1‖ := by gcongr
      _ ≤ ‖w - 1‖ := by rw [one_mul]; exact ih
end GlobalTheory.UltrametricPowerBound
