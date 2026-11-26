-- Prove2me | solution 1 for N4Code.bitXor_eq_false_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:39.504452+00:00
-- url     : https://prove2.me/submissions/4232b96a-6c74-4a72-b069-fa2875d922cf

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
import Theorems.Thm_N4Code_bitXor_self

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (x y : Word n) : (bitXor x y = fun _ => false) ↔ x = y := by
  constructor
  · intro h
    funext i
    have h' := congrFun h i
    cases hx : x i <;> cases hy : y i <;> simp [bitXor] at h'
    all_goals simp_all
  · intro h
    rw [← h]
    exact bitXor_self x
end N4Code
