-- Prove2me | solution 1 for O3.aboveCeilingSum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:08:46.59826+00:00
-- url     : https://prove2.me/submissions/7d9bf5e5-3fca-4dcb-ab6a-431079bbfb1d

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
theorem _root_.solution (S : ℕ) (work : Fin S → ℝ)
    (hwork : ∀ s, 0 ≤ work s) :
    ∑ s, (Nat.ceil (work s) : ℝ) ≤ (∑ s, work s) + S := by
  calc
    ∑ s, (Nat.ceil (work s) : ℝ) ≤ ∑ s, (work s + 1) := by
      apply Finset.sum_le_sum
      intro s _
      exact (Nat.ceil_lt_add_one (hwork s)).le
    _ = (∑ s, work s) + S := by simp [Finset.sum_add_distrib]
end O3
