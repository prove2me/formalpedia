-- Prove2me | solution 1 for N4Code.dRow12_columns07
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:46.393968+00:00
-- url     : https://prove2.me/submissions/8e603b1b-7186-4795-b045-42748991598e

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
    dRow C 1 y = w_i C 0 y + w_i C 1 y + w_i C 2 y + w_i C 3 y +
      (count C 4 - w_i C 4 y) + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) ∧
    dRow C 2 y = w_i C 0 y + w_i C 1 y + w_i C 4 y + w_i C 5 y +
      (count C 2 - w_i C 2 y) + (count C 3 - w_i C 3 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) := by
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
  have h12 : (1 : ℕ).testBit 2 = false := by decide
  have h22 : (2 : ℕ).testBit 2 = false := by decide
  have h32 : (3 : ℕ).testBit 2 = false := by decide
  have h42 : (4 : ℕ).testBit 2 = true := by decide
  have h52 : (5 : ℕ).testBit 2 = true := by decide
  have h62 : (6 : ℕ).testBit 2 = true := by decide
  have h72 : (7 : ℕ).testBit 2 = true := by decide
  have h02 : (0 : ℕ).testBit 2 = false := by decide
  have h11 : (1 : ℕ).testBit 1 = false := by decide
  have h21 : (2 : ℕ).testBit 1 = true := by decide
  have h31 : (3 : ℕ).testBit 1 = true := by decide
  have h41 : (4 : ℕ).testBit 1 = false := by decide
  have h51 : (5 : ℕ).testBit 1 = false := by decide
  have h61 : (6 : ℕ).testBit 1 = true := by decide
  have h71 : (7 : ℕ).testBit 1 = true := by decide
  have h01 : (0 : ℕ).testBit 1 = false := by decide
  have hd1 : dRow C 1 y = w_i C 0 y + w_i C 1 y + w_i C 2 y + w_i C 3 y +
      (count C 4 - w_i C 4 y) + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) := by
    rw [hsum (1 : Fin 4), sum_Icc0_7]
    simp [h02, h12, h22, h32, h42, h52, h62, h72]
  have hd2 : dRow C 2 y = w_i C 0 y + w_i C 1 y + w_i C 4 y + w_i C 5 y +
      (count C 2 - w_i C 2 y) + (count C 3 - w_i C 3 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) := by
    rw [hsum (2 : Fin 4), sum_Icc0_7]
    simp [h01, h11, h21, h31, h41, h51, h61, h71]
    ac_rfl
  exact ⟨hd1, hd2⟩
end N4Code
