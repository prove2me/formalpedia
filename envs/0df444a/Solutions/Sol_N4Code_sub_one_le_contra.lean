-- Prove2me | solution 1 for N4Code.sub_one_le_contra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:35.526829+00:00
-- url     : https://prove2.me/submissions/9831abfa-d633-4e46-924d-0f72c0cefd3b

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a b : ℕ} (h1 : b - 1 ≤ a) (h2 : a ≤ b - 2) (hb : 2 ≤ b) : False := by
  omega
end N4Code
