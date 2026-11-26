-- Prove2me | solution 1 for N4Code.hammingDist_row_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:22.163903+00:00
-- url     : https://prove2.me/submissions/1cb7b338-bb0d-495a-9600-7944e962c6f4

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
import Theorems.Thm_N4Code_colBit_eq_testBit


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (i j : Fin 4) :
    hammingDist (row C i) (row C j) =
      ∑ t : Fin n, if (colVal (C t)).testBit (3 - i.val) ≠ (colVal (C t)).testBit (3 - j.val) then 1 else 0 := by
  unfold hammingDist hammingWeight bitXor
  apply Finset.sum_congr rfl
  intro t _
  simp [row, colBit_eq_testBit]
end N4Code
