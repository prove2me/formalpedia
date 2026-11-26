-- Prove2me | solution 1 for N4Code.tableK_47
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:46.925912+00:00
-- url     : https://prove2.me/submissions/d29b5f98-bac3-4725-81ab-4093c7d812f7

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
    tableK a4 a5 a6 a7 4 = a4 ∧ tableK a4 a5 a6 a7 5 = a5 ∧
      tableK a4 a5 a6 a7 6 = a6 ∧ tableK a4 a5 a6 a7 7 = a7 := by
  simp [tableK]
end N4Code
