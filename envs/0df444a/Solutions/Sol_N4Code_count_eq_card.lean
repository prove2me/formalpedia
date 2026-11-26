-- Prove2me | solution 1 for N4Code.count_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:42.963003+00:00
-- url     : https://prove2.me/submissions/a8b7a9d2-a103-403f-a498-293c84c6f1bc

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
theorem _root_.solution {n : ℕ} (C : Code n) (i : ℕ) :
    count C i = (Finset.univ.filter fun t : Fin n => colVal (C t) = i).card := by
  simp [count]
end N4Code
