-- Prove2me | solution 1 for N4Code.z5_nonempty_of_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:26.341467+00:00
-- url     : https://prove2.me/submissions/6d7cf835-9ae0-4b75-ae89-61764e40494a

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dRow12_columns07
import Theorems.Thm_N4Code_exists_goodWord_fixed
import Theorems.Thm_N4Code_tableZ_bounds
import Theorems.Thm_N4Code_Z5_of_w
import Theorems.Thm_N4Code_w_i_le_count


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (a1 a2 a3 a4 a5 a6 a7 : ℕ) (c : ℕ) (hc : c ≤ 1)
    (ha1 : 1 ≤ a1) (ha7 : a7 + 1 ≤ count C 7)
    (hb1 : a1 ≤ count C 1) (hb2 : a2 ≤ count C 2) (hb3 : a3 ≤ count C 3)
    (hb4 : a4 ≤ count C 4) (hb5 : a5 ≤ count C 5) (hb6 : a6 ≤ count C 6)
    (hb7 : a7 ≤ count C 7)
    (h1eq : 2 * (a2 + a3) + count C 4 + count C 5 + c =
        2 * (a4 + a5) + count C 2 + count C 3)
    (h2ge : count C 2 + count C 3 + count C 6 + count C 7 - 1 ≤ 2 * (a2 + a3 + a6 + a7))
    (h3le : 2 * (a1 + a5) + count C 2 + count C 6 ≤
        2 * (a2 + a6) + count C 1 + count C 5 + 1) :
    ∃ y : Word n, Z5 C t₁ t₂ y := by
  let k : ℕ → ℕ := tableZ a1 a2 a3 a4 a5 a6 a7
  have hk1' : 1 ≤ k 1 := by simp [k, tableZ, ha1]
  have hk7' : k 7 + 1 ≤ count C 7 := by simp [k, tableZ, ha7]
  have hkfeas : ∀ i ∈ Finset.Icc 0 15, k i ≤ count C i := by
    apply tableZ_bounds C a1 a2 a3 a4 a5 a6 a7 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have ht1 : colVal (C t₁) = 1 := by rw [h1]; decide
  have ht2 : colVal (C t₂) = 7 := by rw [h7]; decide
  rcases exists_goodWord_fixed C k t₁ t₂ ht1 ht2 hk1' hk7' hkfeas with ⟨y, hy1, hy2, hw⟩
  have hw1 : w_i C 1 y = a1 := by
    have := hw 1 (by simp)
    simpa [k, tableZ] using this
  have hw2 : w_i C 2 y = a2 := by
    have := hw 2 (by simp)
    simpa [k, tableZ] using this
  have hw3 : w_i C 3 y = a3 := by
    have := hw 3 (by simp)
    simpa [k, tableZ] using this
  have hw4 : w_i C 4 y = a4 := by
    have := hw 4 (by simp)
    simpa [k, tableZ] using this
  have hw5 : w_i C 5 y = a5 := by
    have := hw 5 (by simp)
    simpa [k, tableZ] using this
  have hw6 : w_i C 6 y = a6 := by
    have := hw 6 (by simp)
    simpa [k, tableZ] using this
  have hw7 : w_i C 7 y = a7 := by
    have := hw 7 (by simp)
    simpa [k, tableZ] using this
  have hd12c : dRow C 1 y + c = dRow C 2 y := by
    rcases dRow12_columns07 C y h07 with ⟨hd1, hd2⟩
    rw [hd1, hd2]
    have hw2' : w_i C 2 y ≤ count C 2 := w_i_le_count C 2 y
    have hw3' : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
    have hw4' : w_i C 4 y ≤ count C 4 := w_i_le_count C 4 y
    have hw5' : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
    rw [hw2, hw3, hw4, hw5]
    omega
  refine ⟨y, ?_⟩
  apply Z5_of_w C t₁ t₂ htne h1 h7 h07 y hy1 hy2 c hc hd12c ?_ ?_
  · rw [hw2, hw3, hw6, hw7]
    omega
  · rw [hw1, hw2, hw5, hw6]
    omega
end N4Code
