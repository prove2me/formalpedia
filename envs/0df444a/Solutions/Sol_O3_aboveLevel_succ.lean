-- Prove2me | solution 1 for O3.aboveLevel_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:04:06.562802+00:00
-- url     : https://prove2.me/submissions/d3dc0f47-cb7b-4c22-ad6c-268f170a0726

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution (Delta0 : ℝ) (s : ℕ) :
    aboveLevel Delta0 (s + 1) = aboveLevel Delta0 s / 2 := by
  unfold aboveLevel
  rw [pow_succ]
  ring
end O3
