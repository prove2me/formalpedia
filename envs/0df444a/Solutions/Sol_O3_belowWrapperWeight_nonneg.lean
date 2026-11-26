-- Prove2me | solution 1 for O3.belowWrapperWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:27:23.845024+00:00
-- url     : https://prove2.me/submissions/a07758d7-78a0-4e73-9c98-b713ff20a87e

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization

set_option autoImplicit true
open O3
namespace O3
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ belowWrapperWeight x := by
  unfold belowWrapperWeight
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by
    have : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith))
end O3
