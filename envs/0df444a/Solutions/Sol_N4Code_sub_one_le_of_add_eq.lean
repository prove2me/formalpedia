-- Prove2me | solution 1 for N4Code.sub_one_le_of_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:35.631381+00:00
-- url     : https://prove2.me/submissions/eb905581-068d-4a3d-9119-e477c2d1410f

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a b c : ℕ} (h : a + c = b) (hc : c ≤ 1) : b - 1 ≤ a := by
  omega
end N4Code
