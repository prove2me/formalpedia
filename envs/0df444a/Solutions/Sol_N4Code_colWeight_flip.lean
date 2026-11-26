-- Prove2me | solution 1 for N4Code.colWeight_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:37.757373+00:00
-- url     : https://prove2.me/submissions/9168f501-1913-4b15-a353-84a9f14b7e4e

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
theorem _root_.solution : ∀ c : Column, colWeight (flipCol c) = 4 - colWeight c := by
  decide
end N4Code
