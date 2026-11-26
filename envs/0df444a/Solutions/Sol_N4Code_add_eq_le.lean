-- Prove2me | solution 1 for N4Code.add_eq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:33.193035+00:00
-- url     : https://prove2.me/submissions/0f4cfa5f-4086-4143-92e8-bad49f296db2

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a b c : ℕ} (h : a + c = b) : a ≤ b := by omega
end N4Code
