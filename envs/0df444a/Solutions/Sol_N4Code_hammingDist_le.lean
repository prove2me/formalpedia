-- Prove2me | solution 1 for N4Code.hammingDist_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:02.049941+00:00
-- url     : https://prove2.me/submissions/2b3520b5-d801-480e-bf04-5445cc53102b

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

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (x y : Word n) : hammingDist x y ≤ n := by
  unfold hammingDist hammingWeight
  calc
    (∑ i ∈ (Finset.univ : Finset (Fin n)), if bitXor x y i = true then 1 else 0) ≤
        ∑ i ∈ (Finset.univ : Finset (Fin n)), 1 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : bitXor x y i = true <;> simp [h]
    _ = n := by simp
end N4Code
