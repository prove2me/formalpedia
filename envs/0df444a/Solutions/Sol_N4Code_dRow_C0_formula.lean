-- Prove2me | solution 1 for N4Code.dRow_C0_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:11.523156+00:00
-- url     : https://prove2.me/submissions/a1a53ba7-22a1-4bcf-ba93-d6eafde00893

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_dRow_eq_sum_types

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n)
    (hC : ∀ u : Fin n, colVal (C u) = 0 ∨ colVal (C u) = 5 ∨ colVal (C u) = 6) :
    ∀ y : Word n,
      dRow C 0 y = w_i C 0 y + w_i C 5 y + w_i C 6 y ∧
      dRow C 1 y = w_i C 0 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) ∧
      dRow C 2 y = w_i C 0 y + w_i C 5 y + (count C 6 - w_i C 6 y) ∧
      dRow C 3 y = w_i C 0 y + (count C 5 - w_i C 5 y) + w_i C 6 y := by
  intro y
  have hS : ∀ t : Fin n, colVal (C t) ∈ ({0, 5, 6} : Finset ℕ) := by
    intro t
    rcases hC t with h | h | h <;> simp [h]
  have hSle : ({0, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by
    intro i hi
    simp at hi ⊢
    omega
  have hsum : ∀ j : Fin 4, dRow C j y = ∑ i ∈ ({0, 5, 6} : Finset ℕ),
      if i.testBit (3 - j.val) then count C i - w_i C i y else w_i C i y := by
    intro j
    exact dRow_eq_sum_types C j y {0, 5, 6} hSle hS
  have hb03 : (0 : ℕ).testBit 3 = false := by decide
  have hb02 : (0 : ℕ).testBit 2 = false := by decide
  have hb01 : (0 : ℕ).testBit 1 = false := by decide
  have hb00 : (0 : ℕ).testBit 0 = false := by decide
  have hb53 : (5 : ℕ).testBit 3 = false := by decide
  have hb52 : (5 : ℕ).testBit 2 = true := by decide
  have hb51 : (5 : ℕ).testBit 1 = false := by decide
  have hb50 : (5 : ℕ).testBit 0 = true := by decide
  have hb63 : (6 : ℕ).testBit 3 = false := by decide
  have hb62 : (6 : ℕ).testBit 2 = true := by decide
  have hb61 : (6 : ℕ).testBit 1 = true := by decide
  have hb60 : (6 : ℕ).testBit 0 = false := by decide
  have h0 : dRow C 0 y = w_i C 0 y + w_i C 5 y + w_i C 6 y := by
    rw [hsum (0 : Fin 4)]
    simp [Finset.sum_insert, hb03, hb53, hb63]
    ring
  have h1 : dRow C 1 y = w_i C 0 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) := by
    rw [hsum (1 : Fin 4)]
    simp [Finset.sum_insert, hb02, hb52, hb62]
    ring
  have h2 : dRow C 2 y = w_i C 0 y + w_i C 5 y + (count C 6 - w_i C 6 y) := by
    rw [hsum (2 : Fin 4)]
    simp [Finset.sum_insert, hb01, hb51, hb61]
    ring
  have h3 : dRow C 3 y = w_i C 0 y + (count C 5 - w_i C 5 y) + w_i C 6 y := by
    rw [hsum (3 : Fin 4)]
    simp [Finset.sum_insert]
    ring
  exact ⟨h0, h1, h2, h3⟩
end N4Code
