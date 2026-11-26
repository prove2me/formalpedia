-- Prove2me | solution 1 for N4Code.class_contribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:56.884545+00:00
-- url     : https://prove2.me/submissions/e013e071-d95f-49bd-9611-cb75c8bd3e6a

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
import Theorems.Thm_N4Code_count_eq_card
import Theorems.Thm_N4Code_w_i_eq_card_onesOn
import Theorems.Thm_N4Code_colBit_eq_testBit


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) (i : ℕ) :
    (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
        if C t j ≠ y t then 1 else 0) =
      if i.testBit (3 - j.val) then count C i - w_i C i y else w_i C i y := by
  cases hbit : i.testBit (3 - j.val)
  · -- bit j of type i is 0: contribution is w_i
    have hb : ∀ t : Fin n, colVal (C t) = i → C t j = false := by
      intro t ht
      change colBit j (C t) = false
      rw [colBit_eq_testBit (C t) j, ht, hbit]
    have hsum : (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
        if C t j ≠ y t then 1 else 0) =
        ∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
          if y t = true then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      have hcol : colVal (C t) = i := (Finset.mem_filter.mp ht).2
      have hb' := hb t hcol
      cases hy : y t <;> simp [hb']
    have hw : (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
        if y t = true then 1 else 0) = w_i C i y := by
      rw [w_i_eq_card_onesOn]
      simp [onesOn, fiber]
    rw [hsum, hw]
    simp
  · -- bit j of type i is 1: contribution is count − w_i
    have hb : ∀ t : Fin n, colVal (C t) = i → C t j = true := by
      intro t ht
      change colBit j (C t) = true
      rw [colBit_eq_testBit (C t) j, ht, hbit]
    have hcard : (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i), 1) = count C i := by
      rw [count_eq_card]
      simp
    have hw : (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
        if y t = true then 1 else 0) = w_i C i y := by
      rw [w_i_eq_card_onesOn]
      simp [onesOn, fiber]
    have hsum : (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
        if y t = false then 1 else 0) = count C i - w_i C i y := by
      have hadd : (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
          if y t = false then 1 else 0) + w_i C i y = count C i := by
        rw [← hcard, ← hw, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro t _
        cases hy : y t <;> simp
      omega
    have hsum' : (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
        if C t j ≠ y t then 1 else 0) = count C i - w_i C i y := by
      rw [show (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
            if C t j ≠ y t then 1 else 0) =
          ∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
            if y t = false then 1 else 0 by
        apply Finset.sum_congr rfl
        intro t ht
        have hcol : colVal (C t) = i := (Finset.mem_filter.mp ht).2
        have hb' := hb t hcol
        cases hy : y t <;> simp [hb']]
      exact hsum
    rw [hsum']
    simp
end N4Code
