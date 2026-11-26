-- Prove2me | solution 1 for O3.aboveRestartGap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:08:19.925581+00:00
-- url     : https://prove2.me/submissions/b87594f2-0b9c-49ee-8ab5-ee6f981542b8

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
import Theorems.Thm_O3_aboveAccumulatedWeight_zero
import Theorems.Thm_O3_aboveLevel_zero
import Theorems.Thm_O3_aboveLevel_succ
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
theorem _root_.solution
    {Delta0 : ℝ} (gap : ℕ → ℝ)
    (hzero : gap 0 ≤ Delta0)
    (hstep : ∀ s, gap (s + 1) ≤ gap s / 2) :
    ∀ s, gap s ≤ aboveLevel Delta0 s := by
  intro s
  induction s with
  | zero => simpa using hzero
  | succ s ih =>
      rw [aboveLevel_succ]
      exact (hstep s).trans (div_le_div_of_nonneg_right ih (by norm_num))
end O3
