-- Prove2me | solution 1 for N4Code.count_eq_zero_of_16_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:54.232521+00:00
-- url     : https://prove2.me/submissions/d38b1a5b-64d9-4ccc-b4ae-cf5b6821df1f

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
theorem _root_.solution {n : ℕ} (C : Code n) {i : ℕ} (hi : 16 ≤ i) : count C i = 0 := by
  unfold count
  apply Finset.sum_eq_zero
  intro t _
  have hle := colVal_le_15 (C t)
  have : colVal (C t) ≠ i := by omega
  simp [this]
end N4Code
