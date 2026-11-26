-- Prove2me | solution 1 for N4Code.tableK_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:10:43.838841+00:00
-- url     : https://prove2.me/submissions/9e308b7f-f8a7-4c2d-bfa1-d25a25cccf53

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
theorem _root_.solution (a4 a5 a6 a7 : ℕ) : tableK a4 a5 a6 a7 0 = 1 := by
  simp [tableK]
end N4Code
