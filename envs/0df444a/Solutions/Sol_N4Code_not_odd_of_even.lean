-- Prove2me | solution 1 for N4Code.not_odd_of_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:26.060626+00:00
-- url     : https://prove2.me/submissions/e26fbf92-6462-439d-8d87-bf90e79da6b6

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a : ℕ} (h : Even a) : ¬ Odd a := by
  rintro ⟨l, hl⟩
  rcases h with ⟨k, hk⟩
  omega
end N4Code
