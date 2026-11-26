-- Prove2me | solution 1 for N4Code.colWeight_le_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:41.102806+00:00
-- url     : https://prove2.me/submissions/2f209bd7-5465-40ac-beac-11ed6171e195

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution : ∀ c : Column, colWeight c ≤ 4 := by
  decide
end N4Code
