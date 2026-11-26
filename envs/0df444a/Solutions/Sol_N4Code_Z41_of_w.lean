-- Prove2me | solution 1 for N4Code.Z41_of_w
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:56.184419+00:00
-- url     : https://prove2.me/submissions/a8348704-0412-425a-92dc-ef83240214e0

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dRow12_columns07
import Theorems.Thm_N4Code_Z41_of_htrue_hfalse_d2_d3
import Theorems.Thm_N4Code_dRow03_columns07
import Theorems.Thm_N4Code_w_i_le_count


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false)
    (h1eq : 2 * (w_i C 2 y + w_i C 3 y) + count C 4 + count C 5 =
        2 * (w_i C 4 y + w_i C 5 y) + count C 2 + count C 3 + 1)
    (h2ge : count C 2 + count C 3 + count C 6 + count C 7 ≤
        2 * (w_i C 2 y + w_i C 3 y + w_i C 6 y + w_i C 7 y))
    (h3ge : 2 * (w_i C 2 y + w_i C 6 y) + count C 1 + count C 5 ≥
        2 * (w_i C 1 y + w_i C 5 y) + count C 2 + count C 6) :
    Z41 C t₁ t₂ y := by
  apply Z41_of_htrue_hfalse_d2_d3 C t₁ t₂ htne h1 h7 hy1 hy2
  · have hd12 := dRow12_columns07 C y h07
    rcases hd12 with ⟨hd1, hd2⟩
    rw [hd1, hd2]
    have hw2 : w_i C 2 y ≤ count C 2 := w_i_le_count C 2 y
    have hw3 : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
    have hw4 : w_i C 4 y ≤ count C 4 := w_i_le_count C 4 y
    have hw5 : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
    omega
  · have hd12 := dRow12_columns07 C y h07
    have hd03 := dRow03_columns07 C y h07
    rcases hd12 with ⟨hd1, hd2⟩
    rcases hd03 with ⟨hd0, hd4⟩
    rw [hd2, hd0, hd4]
    have hw2 : w_i C 2 y ≤ count C 2 := w_i_le_count C 2 y
    have hw3 : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
    have hw6 : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
    have hw7 : w_i C 7 y ≤ count C 7 := w_i_le_count C 7 y
    have hw1 : w_i C 1 y ≤ count C 1 := w_i_le_count C 1 y
    have hw5 : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
    exact le_min (by omega) (by omega)
end N4Code
