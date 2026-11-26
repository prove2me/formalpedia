-- Prove2me | solution 1 for N4Code.sub_two_lt_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:01.900582+00:00
-- url     : https://prove2.me/submissions/cbdc6a7b-780f-4e9e-a12b-7c7b2048d959

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a : ℕ} (h : 2 ≤ a) : a - 2 < a - 1 := by omega
end N4Code
