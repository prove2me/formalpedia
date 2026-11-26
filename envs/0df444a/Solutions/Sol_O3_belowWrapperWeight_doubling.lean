-- Prove2me | solution 1 for O3.belowWrapperWeight_doubling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:32.578606+00:00
-- url     : https://prove2.me/submissions/91092343-2271-47d1-bf7e-085d969e8e0c

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization
import Theorems.Thm_O3_belowWrapperWeight_nonneg
import Theorems.Thm_O3_belowWrapperWeight_mono

set_option autoImplicit true
open O3
namespace O3
theorem _root_.solution :
    DoublingWeight belowWrapperWeight (Real.sqrt 2) := by
  have hsqrt : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  refine ⟨hsqrt, @belowWrapperWeight_nonneg, ?_, ?_⟩
  · exact belowWrapperWeight_mono
  · intro x hx
    unfold belowWrapperWeight
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hp1 : 0 < Real.exp 1 + x := add_pos_of_pos_of_nonneg (Real.exp_pos 1) hx
    have hp2 : 0 < Real.exp 1 + 2 * x :=
      add_pos_of_pos_of_nonneg (Real.exp_pos 1) (mul_nonneg (by norm_num) hx)
    have hlog : Real.log (Real.exp 1 + x) ≤ Real.log (Real.exp 1 + 2 * x) := by
      exact Real.strictMonoOn_log.monotoneOn hp1 hp2 (by linarith)
    have hfac : 0 ≤ Real.sqrt 2 * Real.sqrt x :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
end O3
