-- Prove2me | solution 1 for N4Code.flipCol_col0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:14.669908+00:00
-- url     : https://prove2.me/submissions/020f58f7-2205-4a2b-9adc-6fa5545113e9

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution : flipCol col0 = col15 := by
  funext k
  simp [flipCol, col0, col15]
end N4Code
