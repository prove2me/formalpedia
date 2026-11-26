-- Prove2me | solution 1 for O3.aboveEta_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:02:24.173528+00:00
-- url     : https://prove2.me/submissions/f1051ee1-b9d5-471e-9a6d-73c09ccf7a85

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution (p : ℝ) : 0 < aboveEta p := by
  exact Real.rpow_pos_of_pos (by norm_num) _
end O3
