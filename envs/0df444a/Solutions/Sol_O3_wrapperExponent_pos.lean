-- Prove2me | solution 1 for O3.wrapperExponent_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:41.016453+00:00
-- url     : https://prove2.me/submissions/a563ea00-0c6c-4fe1-8aa8-258e105403c1

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization
import Theorems.Thm_O3_aboveAlpha_pos


set_option autoImplicit true
open O3
namespace O3
theorem _root_.solution {p : ℝ} (hp : 1 < p) :
    0 < WrapperExponent p := by
  unfold WrapperExponent
  split_ifs with h
  · norm_num
  · exact aboveAlpha_pos (lt_of_not_ge h)
end O3
