-- Prove2me | solution 1 for O3.aboveWrapperWeight_doubling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:28.20098+00:00
-- url     : https://prove2.me/submissions/7d85c0d2-0796-4f2f-ac38-f2187a40b58c

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization
import Theorems.Thm_O3_two_rpow_gt_one

set_option autoImplicit true
open O3
namespace O3
theorem _root_.solution {a : ℝ} (ha : 0 < a) :
    DoublingWeight (aboveWrapperWeight a) ((2 : ℝ) ^ a) := by
  refine ⟨two_rpow_gt_one ha, ?_, ?_, ?_⟩
  · intro x hx
    exact Real.rpow_nonneg hx _
  · intro x hx y hy hxy
    exact Real.rpow_le_rpow hx hxy ha.le
  · intro x hx
    unfold aboveWrapperWeight
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx]
end O3
