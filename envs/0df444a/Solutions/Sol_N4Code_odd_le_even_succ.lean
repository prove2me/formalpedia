-- Prove2me | solution 1 for N4Code.odd_le_even_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:42.247502+00:00
-- url     : https://prove2.me/submissions/4c1843ad-e95b-4e1d-a9ce-64164e208611

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a b : ℕ} (h : 2 * a + 1 ≤ 2 * b) : 2 * a + 2 ≤ 2 * b := by
  by_cases hab : a < b
  · omega
  · have hba : b ≤ a := le_of_not_gt hab
    omega
end N4Code
