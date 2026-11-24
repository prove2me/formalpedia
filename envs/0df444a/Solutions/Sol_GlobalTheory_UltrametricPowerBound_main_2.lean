-- Prove2me | solution 2 for GlobalTheory.UltrametricPowerBound.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:57:05.32866+00:00
-- url     : https://prove2.me/submissions/be1c896f-d473-429b-97ae-95f60b9c0d6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubOneLe
import Theorems.Thm_GlobalTheory_UltrametricPowerBound_ultra
import Theorems.Thm_GlobalTheory_UltrametricPowerBound_pow_sub_one_le

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
theorem _root_.solution : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (w : ℚ_[l]), ‖w‖ ≤ (1 : ℝ) → ∀ (k : ℕ),
    ‖w ^ k - (1 : ℚ_[l]) - (↑k : ℚ_[l]) * (w - (1 : ℚ_[l]))‖ ≤ ‖w - (1 : ℚ_[l])‖ ^ (2 : ℕ) := by
  intro l _ w hw k
  induction k with
  | zero => simp
  | succ k ih =>
    have e : w ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℚ_[l]) * (w - 1)
        = (w ^ k - 1 - (k : ℚ_[l]) * (w - 1)) + (w - 1) * (w ^ k - 1) := by push_cast; ring
    rw [e]
    refine (ultra _ _).trans (max_le ih ?_)
    rw [norm_mul, sq]
    exact mul_le_mul_of_nonneg_left (pow_sub_one_le w hw k) (norm_nonneg _)
end GlobalTheory.UltrametricPowerBound
