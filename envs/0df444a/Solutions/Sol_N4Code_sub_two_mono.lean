-- Prove2me | solution 1 for N4Code.sub_two_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:56.147802+00:00
-- url     : https://prove2.me/submissions/35a45173-051d-4080-b35b-62e611c9df68

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a b : ℕ} (h : a ≤ b) : a - 2 ≤ b - 2 := by omega
end N4Code
