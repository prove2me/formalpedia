-- Prove2me | solution 1 for N4Code.alpha_eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:14.497349+00:00
-- url     : https://prove2.me/submissions/790c0edc-4968-46a5-94fb-593e7fdceccb

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
import Theorems.Thm_N4Code_dCode_le

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) {d : ℕ} (hd : n < d) : alpha C d = 0 := by
  unfold alpha
  apply Finset.sum_eq_zero
  intro y _
  have hle := dCode_le C y
  have : dCode C y ≠ d := by omega
  simp [this]
end N4Code
