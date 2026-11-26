-- Prove2me | solution 1 for N4Code.sub_two_le_sub_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:37.848923+00:00
-- url     : https://prove2.me/submissions/2e745eed-988d-42be-a93b-2c7711d53598

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a b : ℕ} (h : a - 2 ≤ b - 2) (hb : 2 ≤ b) : a ≤ b := by omega
end N4Code
