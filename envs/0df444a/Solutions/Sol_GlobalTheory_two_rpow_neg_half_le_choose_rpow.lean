-- Prove2me | solution 1 for GlobalTheory.two_rpow_neg_half_le_choose_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:52.058583+00:00
-- url     : https://prove2.me/submissions/68303f25-5808-4cd5-9af2-1814264f5560

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
namespace GlobalTheory
theorem _root_.solution {i N r : ℕ} (hi : i ≤ N) (hr : N ≤ r) :
    (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ (N.choose i : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hpos : (0 : ℝ) < N.choose i := by exact_mod_cast Nat.choose_pos hi
  have hle : (N.choose i : ℝ) ≤ (2 : ℝ) ^ (r : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.choose_le_two_pow N i).trans (Nat.pow_le_pow_right two_pos hr)
  calc (2 : ℝ) ^ (-(r : ℝ) / 2) = ((2 : ℝ) ^ (r : ℝ)) ^ (-(1 : ℝ) / 2) := by
        rw [← Real.rpow_mul zero_le_two]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)
end GlobalTheory
