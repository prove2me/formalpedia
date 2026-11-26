-- Prove2me | solution 1 for N4Code.dRow03_columns07
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:51.470984+00:00
-- url     : https://prove2.me/submissions/e7e03b44-7076-44ed-adf5-76095c9942b9

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_Columns07_le7
import Theorems.Thm_N4Code_dRow_eq_sum_types
import Theorems.Thm_N4Code_sum_Icc0_7


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (y : Word n) (h07 : Columns07 C) :
    dRow C 0 y = w_i C 0 y + w_i C 1 y + w_i C 2 y + w_i C 3 y + w_i C 4 y +
      w_i C 5 y + w_i C 6 y + w_i C 7 y ∧
    dRow C 3 y = w_i C 0 y + w_i C 2 y + w_i C 4 y + w_i C 6 y +
      (count C 1 - w_i C 1 y) + (count C 3 - w_i C 3 y) +
      (count C 5 - w_i C 5 y) + (count C 7 - w_i C 7 y) := by
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
  have h03 : (0 : ℕ).testBit 3 = false := by decide
  have h13 : (1 : ℕ).testBit 3 = false := by decide
  have h23 : (2 : ℕ).testBit 3 = false := by decide
  have h33 : (3 : ℕ).testBit 3 = false := by decide
  have h43 : (4 : ℕ).testBit 3 = false := by decide
  have h53 : (5 : ℕ).testBit 3 = false := by decide
  have h63 : (6 : ℕ).testBit 3 = false := by decide
  have h73 : (7 : ℕ).testBit 3 = false := by decide
  have h00 : (0 : ℕ).testBit 0 = false := by decide
  have h10 : (1 : ℕ).testBit 0 = true := by decide
  have h20 : (2 : ℕ).testBit 0 = false := by decide
  have h30 : (3 : ℕ).testBit 0 = true := by decide
  have h40 : (4 : ℕ).testBit 0 = false := by decide
  have h50 : (5 : ℕ).testBit 0 = true := by decide
  have h60 : (6 : ℕ).testBit 0 = false := by decide
  have h70 : (7 : ℕ).testBit 0 = true := by decide
  have hd0 : dRow C 0 y = w_i C 0 y + w_i C 1 y + w_i C 2 y + w_i C 3 y + w_i C 4 y +
      w_i C 5 y + w_i C 6 y + w_i C 7 y := by
    rw [hsum (0 : Fin 4), sum_Icc0_7]
    simp [h03, h13, h23, h33, h43, h53, h63, h73]
  have hd4 : dRow C 3 y = w_i C 0 y + w_i C 2 y + w_i C 4 y + w_i C 6 y +
      (count C 1 - w_i C 1 y) + (count C 3 - w_i C 3 y) +
      (count C 5 - w_i C 5 y) + (count C 7 - w_i C 7 y) := by
    rw [hsum (3 : Fin 4), sum_Icc0_7]
    simp [h00, h10, h20, h30, h40, h50, h60, h70]
    ac_rfl
  exact ⟨hd0, hd4⟩
end N4Code
