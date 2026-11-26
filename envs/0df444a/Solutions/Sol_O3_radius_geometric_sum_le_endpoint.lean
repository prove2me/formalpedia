-- Prove2me | solution 1 for O3.radius_geometric_sum_le_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:27:02.593076+00:00
-- url     : https://prove2.me/submissions/aafc7e14-a881-4811-9050-2bad4d2ee3b3

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization
import Theorems.Thm_O3_two_rpow_gt_one
import Theorems.Thm_O3_aboveAccumulatedWeight_zero
import Theorems.Thm_O3_aboveGeometricSum_le
import Theorems.Thm_O3_aboveLevel_zero
import Theorems.Thm_O3_abovePhaseTrace_length
import Theorems.Thm_O3_aboveRestartTrace_length
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.aboveAccumulatedWeight_zero
attribute [local simp] O3.aboveLevel_zero
attribute [local simp] O3.abovePhaseTrace_length
attribute [local simp] O3.aboveRestartTrace_length
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open O3
namespace O3
theorem _root_.solution {a beta : ℝ}
    (ha : 0 < a) (hbeta : 0 ≤ beta) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ j * beta) ^ a ≤
      geometricAmortizationConstant a * (((2 : ℝ) ^ J * beta) ^ a) := by
  by_cases hb : beta = 0
  · subst beta
    simp [Real.zero_rpow ha.ne']
  have hbetaPos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hb)
  have hratio : 1 < (2 : ℝ) ^ a := two_rpow_gt_one ha
  have hbetaPow : 0 ≤ beta ^ a := Real.rpow_nonneg hbeta _
  have hrewrite :
      ∑ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ j * beta) ^ a =
        ∑ j ∈ Finset.range (J + 1), beta ^ a * ((2 : ℝ) ^ a) ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.mul_rpow (pow_nonneg (by norm_num) _) hbeta]
    rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) a j]
    ring
  rw [hrewrite]
  have hgeom := aboveGeometricSum_le hbetaPow hratio (J + 1)
  have hend : (((2 : ℝ) ^ J * beta) ^ a) =
      beta ^ a * ((2 : ℝ) ^ a) ^ J := by
    rw [Real.mul_rpow (pow_nonneg (by norm_num) _) hbeta]
    rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) a J]
    ring
  unfold geometricAmortizationConstant
  rw [hend]
  calc
    ∑ j ∈ Finset.range (J + 1), beta ^ a * ((2 : ℝ) ^ a) ^ j
        ≤ beta ^ a * ((2 : ℝ) ^ a) ^ (J + 1) /
            ((2 : ℝ) ^ a - 1) := hgeom
    _ = (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1) *
          (beta ^ a * ((2 : ℝ) ^ a) ^ J) := by rw [pow_succ]; ring
end O3
