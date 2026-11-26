-- Prove2me | solution 1 for N4Code.dCode_le_dRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:14.946979+00:00
-- url     : https://prove2.me/submissions/415f150b-3cba-4043-97f7-05d6bbc598fd

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
theorem _root_.solution {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) :
    dCode C y ≤ dRow C j y := by
  unfold dCode dRow
  fin_cases j
  · exact Nat.min_le_left _ _
  · exact (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  · exact (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.min_le_left _ _))
  · exact (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.min_le_right _ _))
end N4Code
