-- Prove2me | solution 1 for N4Code.exists_col0_of_count_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:25.834623+00:00
-- url     : https://prove2.me/submissions/17c159a4-58c3-4ace-abe2-f90e8d469017

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_colVal_eq_zero_iff_col0
import Theorems.Thm_N4Code_count_pos_iff_exists


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h : 1 ≤ count C 0) :
    ∃ t : Fin n, C t = col0 := by
  rcases (count_pos_iff_exists C 0).mp (by omega : count C 0 > 0) with ⟨t, ht⟩
  exact ⟨t, (colVal_eq_zero_iff_col0 (C t)).mp ht⟩
end N4Code
