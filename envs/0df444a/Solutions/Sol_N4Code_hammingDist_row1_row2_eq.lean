-- Prove2me | solution 1 for N4Code.hammingDist_row1_row2_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:30.297045+00:00
-- url     : https://prove2.me/submissions/66c91eb9-f6b0-409c-ab31-ead2dc876efb

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_Columns07_le7
import Theorems.Thm_N4Code_hammingDist_rows_of_types
import Theorems.Thm_N4Code_sum_Icc0_7


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    hammingDist (row1 C) (row2 C) = count C 2 + count C 3 + count C 4 + count C 5 := by
  have hS : ∀ t : Fin n, colVal (C t) ∈ Finset.Icc 0 7 := by
    intro t
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, Columns07_le7 C h07 t⟩
  unfold row1 row2
  rw [hammingDist_rows_of_types C ⟨1, by decide⟩ ⟨2, by decide⟩ (Finset.Icc 0 7) hS, sum_Icc0_7]
  have h20 : (2 : ℕ).testBit 2 = false := by decide
  have h21 : (2 : ℕ).testBit 1 = true := by decide
  have h30 : (3 : ℕ).testBit 2 = false := by decide
  have h31 : (3 : ℕ).testBit 1 = true := by decide
  have h40 : (4 : ℕ).testBit 2 = true := by decide
  have h41 : (4 : ℕ).testBit 1 = false := by decide
  have h50 : (5 : ℕ).testBit 2 = true := by decide
  have h51 : (5 : ℕ).testBit 1 = false := by decide
  have h10 : (1 : ℕ).testBit 2 = false := by decide
  have h11 : (1 : ℕ).testBit 1 = false := by decide
  have h60 : (6 : ℕ).testBit 2 = true := by decide
  have h61 : (6 : ℕ).testBit 1 = true := by decide
  have h70 : (7 : ℕ).testBit 2 = true := by decide
  have h71 : (7 : ℕ).testBit 1 = true := by decide
  have h00 : (0 : ℕ).testBit 2 = false := by decide
  have h01 : (0 : ℕ).testBit 1 = false := by decide
  simp [h00, h01, h10, h11, h20, h21, h30, h31, h40, h41, h50, h51, h60, h61, h70, h71]
end N4Code
