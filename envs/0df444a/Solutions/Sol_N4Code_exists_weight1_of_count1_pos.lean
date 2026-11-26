-- Prove2me | solution 1 for N4Code.exists_weight1_of_count1_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:48.346295+00:00
-- url     : https://prove2.me/submissions/6a3511f1-d0e3-4900-a930-bb3cbae82bb3

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_count_pos_iff_exists
import Theorems.Thm_N4Code_colOfNat_colVal


set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (hpos : count C 1 > 0) :
    ∃ t : Fin n, colWeight (C t) = 1 := by
  rcases (count_pos_iff_exists C 1).1 hpos with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [← colOfNat_colVal (C t), ht]
  decide
end N4Code
