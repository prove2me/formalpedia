-- Prove2me | solution 1 for N4Code.dRow_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:28.421084+00:00
-- url     : https://prove2.me/submissions/82bcceb7-6ac1-4d74-bd6a-9eb3cfe8a1f9

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
import Theorems.Thm_N4Code_dRow_eq_hammingDist
import Theorems.Thm_N4Code_class_contribution

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) :
    dRow C j y = ∑ i ∈ Finset.Icc 0 15,
      if i.testBit (3 - j.val) then count C i - w_i C i y else w_i C i y := by
  rw [dRow_eq_hammingDist]
  unfold hammingDist hammingWeight
  have hstep : (∑ t ∈ (Finset.univ : Finset (Fin n)),
        if bitXor (row C j) y t = true then 1 else 0) =
      ∑ t ∈ (Finset.univ : Finset (Fin n)),
        ∑ i ∈ Finset.Icc 0 15,
          if colVal (C t) = i then (if C t j ≠ y t then 1 else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro t _
    have hsummand : (if bitXor (row C j) y t = true then 1 else 0) =
        if C t j ≠ y t then 1 else 0 := by
      by_cases h : bitXor (row C j) y t = true <;> by_cases hne : C t j ≠ y t <;>
        simp [hne, bitXor, row, colBit]
    rw [hsummand]
    rw [Finset.sum_ite_eq]
    simp [colVal_le_15]
  rw [hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter (s := (Finset.univ : Finset (Fin n)))
    (p := fun t : Fin n => colVal (C t) = i)
    (f := fun t : Fin n => if C t j ≠ y t then 1 else 0)]
  exact class_contribution C j y i
end N4Code
