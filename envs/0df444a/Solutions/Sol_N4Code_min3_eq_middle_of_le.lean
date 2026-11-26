-- Prove2me | solution 1 for N4Code.min3_eq_middle_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:29.8468+00:00
-- url     : https://prove2.me/submissions/a6490c3c-a255-4e5f-b939-6c82d93faf03

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a b c : ℕ} (ha : b ≤ a) (hc : b ≤ c) :
    min a (min b c) = b := by
  rw [min_eq_right (le_trans (min_le_left _ _) ha)]
  exact min_eq_left hc
end N4Code
