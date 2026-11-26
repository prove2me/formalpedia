-- Prove2me | solution 1 for N4Code.count_replace_0_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:38.697489+00:00
-- url     : https://prove2.me/submissions/df489476-895c-4507-ace0-354a316e6f01

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_colVal_eq_zero_iff_col0
import Theorems.Thm_N4Code_count_replace_dec


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (s' : Column)
    (h0 : C t = col0) (hs : s' ≠ col0) :
    count (replaceColumn C t s') 0 = count C 0 - 1 := by
  exact count_replace_dec C t s' 0 (by rw [h0]; decide)
    (by intro h; exact hs ((colVal_eq_zero_iff_col0 s').mp h))
end N4Code
