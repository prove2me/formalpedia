-- Prove2me | solution 1 for N4Code.hammingWeight_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:41.345727+00:00
-- url     : https://prove2.me/submissions/582cede4-3d3c-4dae-8c18-af7015651051

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
theorem _root_.solution {n : ℕ} (w : Word n) :
    hammingWeight w = 0 ↔ ∀ i : Fin n, w i = false := by
  unfold hammingWeight
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h i
    have hi := h i (Finset.mem_univ i)
    cases hx : w i <;> simp [hx] at hi ⊢
  · intro h i _
    have hx : w i = false := h i
    simp [hx]
end N4Code
