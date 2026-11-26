-- Prove2me | solution 1 for N4Code.Z5_of_w
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:44.993805+00:00
-- url     : https://prove2.me/submissions/c81c3b83-d469-4c63-97c8-80b7084d554d

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dOp2_le_dO_of_htrue_hfalse
import Theorems.Thm_N4Code_dRow12_columns07
import Theorems.Thm_N4Code_dOp2_eq_min_of_htrue_hfalse
import Theorems.Thm_N4Code_dPp2_eq_sub_two_of_htrue_hfalse
import Theorems.Thm_N4Code_dRow_ge_two_of_mismatch
import Theorems.Thm_N4Code_dRow03_columns07
import Theorems.Thm_N4Code_add_eq_le
import Theorems.Thm_N4Code_sub_one_le_of_add_eq
import Theorems.Thm_N4Code_sub_two_mono
import Theorems.Thm_N4Code_sub_two_lt_sub_one
import Theorems.Thm_N4Code_le_succ_of_sub_one_le
import Theorems.Thm_N4Code_w_i_le_count


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false)
    (c : ℕ) (hc : c ≤ 1) (hd12c : dRow C 1 y + c = dRow C 2 y)
    (h2ge : count C 2 + count C 3 + count C 6 + count C 7 - 1 ≤
        2 * (w_i C 2 y + w_i C 3 y + w_i C 6 y + w_i C 7 y))
    (h3le : 2 * (w_i C 1 y + w_i C 5 y) + count C 2 + count C 6 ≤
        2 * (w_i C 2 y + w_i C 6 y) + count C 1 + count C 5 + 1) :
    Z5 C t₁ t₂ y := by
  have hd12 := dRow12_columns07 C y h07
  have hd03 := dRow03_columns07 C y h07
  rcases hd12 with ⟨hd1, hd2⟩
  rcases hd03 with ⟨hd0, hd4⟩
  have hd23 : dRow C 1 y ≤ dRow C 2 y := add_eq_le hd12c
  have hd31 : dRow C 2 y - 1 ≤ dRow C 1 y := sub_one_le_of_add_eq hd12c hc
  have hP_ge_2 : 2 ≤ dP C y := by
    have hne1 : y t₁ ≠ row C ⟨2, by decide⟩ t₁ := by
      simp [row, colBit, h1, col1, hy1]
    have hne2 : y t₂ ≠ row C ⟨2, by decide⟩ t₂ := by
      simp [row, colBit, h7, col7, hy2]
    change 2 ≤ dRow C ⟨2, by decide⟩ y
    exact dRow_ge_two_of_mismatch C ⟨2, by decide⟩ t₁ t₂ htne y hne1 hne2
  have hd30 : dRow C 2 y - 1 ≤ dRow C 0 y := by
    rw [hd2, hd0]
    have hw2 : w_i C 2 y ≤ count C 2 := w_i_le_count C 2 y
    have hw3 : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
    have hw6 : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
    have hw7 : w_i C 7 y ≤ count C 7 := w_i_le_count C 7 y
    omega
  have hd34 : dRow C 2 y - 1 ≤ dRow C 3 y := by
    rw [hd2, hd4]
    have hw1 : w_i C 1 y ≤ count C 1 := w_i_le_count C 1 y
    have hw2 : w_i C 2 y ≤ count C 2 := w_i_le_count C 2 y
    have hw5 : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
    have hw6 : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
    omega
  have hd3_le_dO : dRow C 2 y ≤ dO C y + 1 := by
    have hmin : dRow C 2 y - 1 ≤ min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) :=
      le_min hd30 (le_min hd31 hd34)
    have hO' : dRow C 2 y - 1 ≤ dO C y := by
      simpa [dO, dRow, row0, row1, row2, row3] using hmin
    exact le_succ_of_sub_one_le hO'
  have hOp := dOp2_eq_min_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hPp : dPp2 C t₁ t₂ y = dP C y - 2 :=
    dPp2_eq_sub_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hOp_le_d1m2 : dOp2 C t₁ t₂ y ≤ dRow C 1 y - 2 := by
    rw [hOp]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hOp_le_Pp : dOp2 C t₁ t₂ y ≤ dPp2 C t₁ t₂ y := by
    rw [hPp]
    exact le_trans hOp_le_d1m2 (sub_two_mono hd23)
  have hOp_le_O : dOp2 C t₁ t₂ y ≤ dO C y :=
    dOp2_le_dO_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  unfold Z5
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hy1, hy2]
  · have hmin : min (dP C y) (dP C y - 2) = dP C y - 2 := by
      apply min_eq_right
      omega
    rw [hPp, hmin]
    change dRow C 2 y - 2 < min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y))
    have hmin_ge : dRow C 2 y - 1 ≤ min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) :=
      le_min hd30 (le_min hd31 hd34)
    have hRow2_ge_2 : 2 ≤ dRow C 2 y := by
      simpa [dP, dRow, row2] using hP_ge_2
    exact lt_of_lt_of_le (sub_two_lt_sub_one hRow2_ge_2) hmin_ge
  · have hmin : min (dO C y) (dOp2 C t₁ t₂ y) = dOp2 C t₁ t₂ y := min_eq_right hOp_le_O
    rw [hmin]
    have hOp_lt_P : dOp2 C t₁ t₂ y < dP C y := by
      have hle2 : dOp2 C t₁ t₂ y ≤ dP C y - 2 := by
        rw [← hPp]
        exact hOp_le_Pp
      omega
    exact hOp_lt_P
  · have hmin : min (dO C y) (dOp2 C t₁ t₂ y) = dOp2 C t₁ t₂ y := min_eq_right hOp_le_O
    rw [hmin]
    exact hOp_le_Pp
end N4Code
