-- Prove2me | solution 1 for N4Code.wordTuple_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:01.651486+00:00
-- url     : https://prove2.me/submissions/f6c973a7-64e5-4f49-af25-4e3e1125475a

import Definitions.Def_N4Code_Definitions
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Definitions.Def_N4Code_Basic
import Theorems.Thm_N4Code_w_i_eq_card_onesOn
import Theorems.Thm_N4Code_goodWord_iff
import Theorems.Thm_N4Code_fin16_val_mem_Icc

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (k : ℕ → ℕ) {y : Word n} (hy : y ∈ GoodWords C k) :
    GoodTuplePred C k (wordTuple C y) := by
  intro a
  rw [Finset.mem_powersetCard]
  constructor
  · exact Finset.filter_subset _ _
  · change (onesOn (fiber C a.val) y).card = k a.val
    rw [← w_i_eq_card_onesOn]
    exact (goodWord_iff C k y).1 hy a.val (fin16_val_mem_Icc a)
end N4Code
