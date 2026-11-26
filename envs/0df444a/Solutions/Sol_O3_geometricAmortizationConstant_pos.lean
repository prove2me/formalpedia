-- Prove2me | solution 1 for O3.geometricAmortizationConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:16.604389+00:00
-- url     : https://prove2.me/submissions/ae27748d-2036-4e49-9dcf-1c256a4c63b5

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization
import Theorems.Thm_O3_two_rpow_gt_one

set_option autoImplicit true
open O3
namespace O3
theorem _root_.solution {a : ℝ} (ha : 0 < a) :
    0 < geometricAmortizationConstant a := by
  unfold geometricAmortizationConstant
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (sub_pos.mpr (two_rpow_gt_one ha))
end O3
