-- Prove2me | solution 1 for N4Code.colVal_eq_zero_iff_col0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:10:09.497908+00:00
-- url     : https://prove2.me/submissions/048b0fcc-13c7-45c7-9ca2-02c0841b13fb

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_colVal_eq_iff_colOfNat


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution (c : Column) : colVal c = 0 ↔ c = col0 := by
  simpa [show colOfNat 0 = col0 by decide] using (colVal_eq_iff_colOfNat c 0 (by norm_num))
end N4Code
