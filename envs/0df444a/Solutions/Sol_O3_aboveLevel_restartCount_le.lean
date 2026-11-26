-- Prove2me | solution 1 for O3.aboveLevel_restartCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:08:15.011258+00:00
-- url     : https://prove2.me/submissions/79720b18-4c3b-4615-ad7a-f843aa85488a

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
import Theorems.Thm_O3_aboveAccumulatedWeight_zero
import Theorems.Thm_O3_aboveLevel_zero
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right


attribute [local simp] O3.aboveAccumulatedWeight_zero
attribute [local simp] O3.aboveLevel_zero

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {Delta0 delta : ℝ}
    (hDelta0 : 0 < Delta0) (hdelta : 0 < delta) :
    aboveLevel Delta0 (aboveRestartCount Delta0 delta) ≤ delta := by
  let ratio := Delta0 / delta
  have hratio : 0 < ratio := div_pos hDelta0 hdelta
  have hlog : Real.logb 2 ratio ≤ (aboveRestartCount Delta0 delta : ℝ) := by
    exact Nat.le_ceil _
  have hratio_pow : ratio ≤ 2 ^ (aboveRestartCount Delta0 delta : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num) hratio).mp hlog
  rw [Real.rpow_natCast] at hratio_pow
  have hscaled : Delta0 ≤ (2 : ℝ) ^ aboveRestartCount Delta0 delta * delta := by
    calc
      Delta0 = ratio * delta := by
        dsimp [ratio]
        exact (div_mul_cancel₀ Delta0 hdelta.ne').symm
      _ ≤ (2 : ℝ) ^ aboveRestartCount Delta0 delta * delta :=
        mul_le_mul_of_nonneg_right hratio_pow hdelta.le
  unfold aboveLevel
  exact (div_le_iff₀ (pow_pos (by norm_num) _)).2 (by
    simpa [mul_comm] using hscaled)
end O3
