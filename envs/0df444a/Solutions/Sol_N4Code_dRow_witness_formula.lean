-- Prove2me | solution 1 for N4Code.dRow_witness_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:13.051898+00:00
-- url     : https://prove2.me/submissions/37b38fee-aca0-4082-b3b1-506613108b78

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_dRow_eq_sum_types
import Theorems.Thm_N4Code_Columns07_le7
import Theorems.Thm_N4Code_sum_Icc0_7

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (y : Word n) (h07 : Columns07 C)
    (hw123 : w_i C 1 y = 0 ∧ w_i C 2 y = 0 ∧ w_i C 3 y = 0)
    (_hw815 : ∀ i ∈ Finset.Icc 8 15, w_i C i y = 0) :
    dRow C 0 y = w_i C 0 y + w_i C 4 y + w_i C 5 y + w_i C 6 y + w_i C 7 y ∧
    dRow C 1 y = w_i C 0 y + (count C 4 - w_i C 4 y) + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) ∧
    dRow C 2 y = w_i C 0 y + count C 2 + count C 3 + w_i C 4 y + w_i C 5 y +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) ∧
    dRow C 3 y = w_i C 0 y + count C 1 + count C 3 + w_i C 4 y + (count C 5 - w_i C 5 y) +
      w_i C 6 y + (count C 7 - w_i C 7 y) := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ Finset.Icc 0 7 := by
    intro t
    have hle := Columns07_le7 C h07 t
    simp [Finset.mem_Icc, hle]
  have hSle : (Finset.Icc 0 7 : Finset ℕ) ⊆ Finset.Icc 0 15 := by
    intro i hi
    simp [Finset.mem_Icc] at hi ⊢
    omega
  have hsum : ∀ j : Fin 4, dRow C j y = ∑ i ∈ Finset.Icc 0 7,
      if i.testBit (3 - j.val) then count C i - w_i C i y else w_i C i y := by
    intro j
    exact dRow_eq_sum_types C j y (Finset.Icc 0 7) hSle hS
  have h13 : (1 : ℕ).testBit 3 = false := by decide
  have h23 : (2 : ℕ).testBit 3 = false := by decide
  have h33 : (3 : ℕ).testBit 3 = false := by decide
  have h43 : (4 : ℕ).testBit 3 = false := by decide
  have h53 : (5 : ℕ).testBit 3 = false := by decide
  have h63 : (6 : ℕ).testBit 3 = false := by decide
  have h73 : (7 : ℕ).testBit 3 = false := by decide
  have h12 : (1 : ℕ).testBit 2 = false := by decide
  have h22 : (2 : ℕ).testBit 2 = false := by decide
  have h32 : (3 : ℕ).testBit 2 = false := by decide
  have h42 : (4 : ℕ).testBit 2 = true := by decide
  have h52 : (5 : ℕ).testBit 2 = true := by decide
  have h62 : (6 : ℕ).testBit 2 = true := by decide
  have h72 : (7 : ℕ).testBit 2 = true := by decide
  have h11 : (1 : ℕ).testBit 1 = false := by decide
  have h21 : (2 : ℕ).testBit 1 = true := by decide
  have h31 : (3 : ℕ).testBit 1 = true := by decide
  have h41 : (4 : ℕ).testBit 1 = false := by decide
  have h51 : (5 : ℕ).testBit 1 = false := by decide
  have h61 : (6 : ℕ).testBit 1 = true := by decide
  have h71 : (7 : ℕ).testBit 1 = true := by decide
  have h10 : (1 : ℕ).testBit 0 = true := by decide
  have h20 : (2 : ℕ).testBit 0 = false := by decide
  have h30 : (3 : ℕ).testBit 0 = true := by decide
  have h40 : (4 : ℕ).testBit 0 = false := by decide
  have h50 : (5 : ℕ).testBit 0 = true := by decide
  have h60 : (6 : ℕ).testBit 0 = false := by decide
  have h70 : (7 : ℕ).testBit 0 = true := by decide
  have h0 : dRow C 0 y = w_i C 0 y + w_i C 4 y + w_i C 5 y + w_i C 6 y + w_i C 7 y := by
    rw [hsum (0 : Fin 4), sum_Icc0_7]
    simp [hw123, h13, h23, h33, h43, h53, h63, h73]
  have h1 : dRow C 1 y = w_i C 0 y + (count C 4 - w_i C 4 y) + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) := by
    rw [hsum (1 : Fin 4), sum_Icc0_7]
    simp [hw123, h12, h22, h32, h42, h52, h62, h72]
  have h2 : dRow C 2 y = w_i C 0 y + count C 2 + count C 3 + w_i C 4 y + w_i C 5 y +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) := by
    rw [hsum (2 : Fin 4), sum_Icc0_7]
    simp [hw123, h11, h21, h31, h41, h51, h61, h71]
  have h3 : dRow C 3 y = w_i C 0 y + count C 1 + count C 3 + w_i C 4 y + (count C 5 - w_i C 5 y) +
      w_i C 6 y + (count C 7 - w_i C 7 y) := by
    rw [hsum (3 : Fin 4), sum_Icc0_7]
    simp [hw123, h10, h20, h30, h40, h50, h60, h70]
  exact ⟨h0, h1, h2, h3⟩
end N4Code
