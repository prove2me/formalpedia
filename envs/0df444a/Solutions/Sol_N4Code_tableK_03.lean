-- Prove2me | solution 1 for N4Code.tableK_03
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:13:19.877042+00:00
-- url     : https://prove2.me/submissions/4d6973b0-b991-4841-ab44-1870a9e0677f

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
theorem _root_.solution (a4 a5 a6 a7 : ℕ) :
    tableK a4 a5 a6 a7 1 = 0 ∧ tableK a4 a5 a6 a7 2 = 0 ∧ tableK a4 a5 a6 a7 3 = 0 := by
  simp [tableK]
end N4Code
