-- Prove2me | solution 1 for N4Code.hammingDist_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:51.94375+00:00
-- url     : https://prove2.me/submissions/e3dd052f-8f07-4b47-abe0-d208a23e772c

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
import Theorems.Thm_N4Code_bitXor_eq_false_iff
import Theorems.Thm_N4Code_hammingWeight_eq_zero_iff

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (x y : Word n) : hammingDist x y = 0 ↔ x = y := by
  rw [hammingDist, hammingWeight_eq_zero_iff]
  rw [show (∀ i : Fin n, bitXor x y i = false) ↔ bitXor x y = fun _ => false by
    constructor
    · intro h
      funext i
      exact h i
    · intro h i
      simpa using (congrFun h i)]
  exact bitXor_eq_false_iff x y
end N4Code
