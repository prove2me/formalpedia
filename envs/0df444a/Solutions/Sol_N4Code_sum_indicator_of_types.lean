-- Prove2me | solution 1 for N4Code.sum_indicator_of_types
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:22.613269+00:00
-- url     : https://prove2.me/submissions/28e54def-cb49-4098-b222-331627283923

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
theorem _root_.solution {n : ℕ} (C : Code n) (S : Finset ℕ) (p : ℕ → Prop)
    [DecidablePred p] (hS : ∀ t : Fin n, colVal (C t) ∈ S) :
    (∑ t : Fin n, if p (colVal (C t)) then 1 else 0) =
      ∑ i ∈ S, count C i * (if p i then 1 else 0) := by
  rw [show (∑ t : Fin n, if p (colVal (C t)) then 1 else 0) =
        ∑ t : Fin n, ∑ i ∈ S, if colVal (C t) = i then (if p i then 1 else 0) else 0 by
        apply Finset.sum_congr rfl
        intro t _
        have ht := hS t
        rw [Finset.sum_ite_eq]
        simp [ht]]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ t : Fin n, if colVal (C t) = i then (if p i then 1 else 0) else 0)
        = (∑ t : Fin n, if colVal (C t) = i then 1 else 0) * (if p i then 1 else 0) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _
          by_cases h : colVal (C t) = i <;> by_cases hp : p i <;> simp [h, hp]
    _ = count C i * (if p i then 1 else 0) := by rfl
end N4Code
