-- Prove2me | solution 1 for N4Code.hammingDist_rows_of_types
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:09.448928+00:00
-- url     : https://prove2.me/submissions/e9cdf3b7-5b90-473c-974f-9e9255860da9

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
import Theorems.Thm_N4Code_hammingDist_row_eq_indicator
import Theorems.Thm_N4Code_sum_indicator_of_types

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (i j : Fin 4)
    (S : Finset ℕ) (hS : ∀ t : Fin n, colVal (C t) ∈ S) :
    hammingDist (row C i) (row C j) =
      ∑ k ∈ S, count C k *
        if k.testBit (3 - i.val) ≠ k.testBit (3 - j.val) then 1 else 0 := by
  rw [hammingDist_row_eq_indicator C i j]
  exact sum_indicator_of_types C S
    (fun k => k.testBit (3 - i.val) ≠ k.testBit (3 - j.val)) hS
end N4Code
