-- Prove2me | solution 1 for N4Code.sum_counts_eq_n
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:09.00261+00:00
-- url     : https://prove2.me/submissions/ed17914d-799c-49eb-94d5-4ee77e91a2e8

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
theorem _root_.solution {n : ℕ} (C : Code n) : (∑ i ∈ Finset.Icc 0 15, count C i) = n := by
  rw [show (∑ i ∈ Finset.Icc 0 15, count C i) =
        ∑ i ∈ Finset.Icc 0 15, ∑ t ∈ (Finset.univ : Finset (Fin n)),
          if colVal (C t) = i then 1 else 0 by
        apply Finset.sum_congr rfl
        intro i _
        rfl]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq, colVal_le_15]
end N4Code
