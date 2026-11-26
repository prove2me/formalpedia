-- Prove2me | solution 1 for O3.belowWrapperWeight_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:27:24.571547+00:00
-- url     : https://prove2.me/submissions/d64bf60c-95a8-4177-82ec-c872be39adb1

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization

set_option autoImplicit true
open O3
namespace O3
theorem _root_.solution :
    MonotoneOn belowWrapperWeight (Set.Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  unfold belowWrapperWeight
  have hpx : 0 < Real.exp 1 + x := add_pos_of_pos_of_nonneg (Real.exp_pos 1) hx
  have hpy : 0 < Real.exp 1 + y := add_pos_of_pos_of_nonneg (Real.exp_pos 1) hy
  have hsum : Real.exp 1 + x ≤ Real.exp 1 + y := by linarith
  have hlog : Real.log (Real.exp 1 + x) ≤ Real.log (Real.exp 1 + y) :=
    Real.strictMonoOn_log.monotoneOn hpx hpy hsum
  apply mul_le_mul (Real.sqrt_le_sqrt hxy)
  · exact hlog
  · exact Real.log_nonneg (by
      have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
      linarith)
  · exact Real.sqrt_nonneg _
end O3
