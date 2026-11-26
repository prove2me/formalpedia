-- Prove2me | solution 1 for O3.aboveAP_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:03:02.4298+00:00
-- url     : https://prove2.me/submissions/17b6e2b6-27b3-46c9-aa88-ecb5cdfc3b8e

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p : ℝ} (hp : AboveTwoRegime p) :
    0 < aboveAP p := by
  change 2 < p at hp
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)
end O3
