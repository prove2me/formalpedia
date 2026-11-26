-- Prove2me | solution 1 for N4Code.le_succ_of_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:16.365065+00:00
-- url     : https://prove2.me/submissions/81376db6-e9d5-46d8-841f-9c2a029d8800

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a b : ℕ} (h : a - 1 ≤ b) : a ≤ b + 1 := by omega
end N4Code
