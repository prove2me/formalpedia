-- Prove2me | solution 1 for O3.two_rpow_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:24:38.577333+00:00
-- url     : https://prove2.me/submissions/dea1f42f-4f15-4a09-be46-854d0c54bf95

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization

set_option autoImplicit true
open O3
namespace O3
theorem _root_.solution {a : ℝ} (ha : 0 < a) :
    1 < (2 : ℝ) ^ a := by
  exact (Real.one_lt_rpow (by norm_num) ha)
end O3
