-- Prove2me | solution 1 for N4Code.bitXor_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:41.98337+00:00
-- url     : https://prove2.me/submissions/383bb40a-cf85-42ef-9e37-e15a7979b56e

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
theorem _root_.solution {n : ℕ} (x y z : Word n) : bitXor (bitXor x y) z = bitXor x (bitXor y z) := by
  funext i
  by_cases hx : x i = true <;> by_cases hy : y i = true <;> by_cases hz : z i = true <;>
    simp [bitXor, hx, hy, hz]
end N4Code
