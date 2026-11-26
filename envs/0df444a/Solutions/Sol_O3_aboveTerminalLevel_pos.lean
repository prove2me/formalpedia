-- Prove2me | solution 1 for O3.aboveTerminalLevel_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:53.059638+00:00
-- url     : https://prove2.me/submissions/5d21e1fd-73fa-4375-9297-d1d03e6f429b

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {rho M : ℝ} (hrho : 0 < rho) (hM : 0 < M) :
    0 < aboveTerminalLevel rho M := by
  exact div_pos (sq_pos_of_pos hrho) (mul_pos (by norm_num) hM)
end O3
