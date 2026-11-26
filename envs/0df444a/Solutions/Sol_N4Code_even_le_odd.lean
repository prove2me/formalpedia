-- Prove2me | solution 1 for N4Code.even_le_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:42.741877+00:00
-- url     : https://prove2.me/submissions/d7e0521f-6b12-4568-bfa7-0fb96c5e7d38

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a b : ℕ} (h : 2 * a ≤ 2 * b + 1) : 2 * a ≤ 2 * b := by
  by_cases hab : a ≤ b
  · omega
  · have hgt : b < a := lt_of_not_ge hab
    omega
end N4Code
