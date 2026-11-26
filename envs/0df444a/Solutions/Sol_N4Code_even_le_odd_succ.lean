-- Prove2me | solution 1 for N4Code.even_le_odd_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:18.145634+00:00
-- url     : https://prove2.me/submissions/d5bc4cc0-005c-4d89-89dd-e7a13f5bae77

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a b : ℕ} (h : 2 * a ≤ 2 * b + 1) : 2 * a + 1 ≤ 2 * b + 1 := by
  by_cases hab : a ≤ b
  · omega
  · exfalso
    have hgt : b < a := lt_of_not_ge hab
    omega
end N4Code
