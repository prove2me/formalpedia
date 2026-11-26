-- Prove2me | solution 1 for O3.aboveLevel_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:47.54075+00:00
-- url     : https://prove2.me/submissions/48e9d503-ee93-4352-8269-d54205d60fe6

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {Delta0 : ℝ} (hDelta0 : 0 < Delta0) (s : ℕ) :
    0 < aboveLevel Delta0 s := by
  exact div_pos hDelta0 (pow_pos (by norm_num) _)
end O3
