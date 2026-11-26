-- Prove2me | solution 1 for N4Code.z5_empty_case16
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:07.810984+00:00
-- url     : https://prove2.me/submissions/525fa203-bbc9-4aee-b882-3587c0fd2909

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dRow12_columns07
import Theorems.Thm_N4Code_dRow03_columns07
import Theorems.Thm_N4Code_count_pos_of_colVal
import Theorems.Thm_N4Code_z5_nonempty_of_table
import Theorems.Thm_N4Code_w_i_eq_of_single
import Theorems.Thm_N4Code_w_i_eq_zero_of_single_false
import Theorems.Thm_N4Code_odd_le_even_succ
import Theorems.Thm_N4Code_even_le_odd
import Theorems.Thm_N4Code_Z5_implies_dRow
import Theorems.Thm_N4Code_w_i_eq_zero_of_count_zero


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (hcase : Even (count C 2) ∧ Even (count C 4) ∧ Odd (count C 3) ∧ Odd (count C 5)) :
    ((∀ y : Word n, ¬ Z5 C t₁ t₂ y) ↔
      count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
        count C 6 = 0 ∧ Odd (count C 3) ∧ Odd (count C 5)) := by
  constructor
  · intro hE
    rcases hcase with ⟨h2e, h4e, h3o, h5o⟩
    rcases h2e with ⟨p2, hp2⟩
    rcases h4e with ⟨p4, hp4⟩
    rcases h3o with ⟨p3, hp3⟩
    rcases h5o with ⟨p5, hp5⟩
    have h1ge : 1 ≤ count C 1 := count_pos_of_colVal C t₁ (by rw [h1]; decide)
    have h7ge : 1 ≤ count C 7 := count_pos_of_colVal C t₂ (by rw [h7]; decide)
    constructor
    · by_contra h1ne
      have h1ge2 : 2 ≤ count C 1 := by omega
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 (p3 + 1) p4 (p5 + 1)
          (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact hE y hy
    constructor
    · by_contra h7ne
      have h7ge2 : 2 ≤ count C 7 := by omega
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 p4 p5
          (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact hE y hy
    constructor
    · by_contra h2ne
      have h2pos : 1 ≤ count C 2 := by omega
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 (p2 + 1) p3 p4 (p5 + 1)
          (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact hE y hy
    constructor
    · by_contra h4ne
      have h4pos : 1 ≤ count C 4 := by omega
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 (p3 + 1) (p4 + 1) p5
          (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact hE y hy
    · by_contra h6ne
      have h6ne' : count C 6 ≠ 0 := by
        intro h6
        exact h6ne ⟨h6, ⟨⟨p3, hp3⟩, ⟨p5, hp5⟩⟩⟩
      have h6pos : 1 ≤ count C 6 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h6ne')
      have hwit : ∃ y : Word n, Z5 C t₁ t₂ y := by
        refine z5_nonempty_of_table C t₁ t₂ htne h1 h7 h07 1 p2 p3 p4 p5
          (count C 6) (count C 7 - 1) 0 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · rfl
        · omega
        · omega
        · omega
        · omega
      rcases hwit with ⟨y, hy⟩
      exact hE y hy
  · rintro ⟨h1eq1, h7eq1, h2eq0, h4eq0, h6eq0, h3o, h5o⟩
    rcases h3o with ⟨p3, hp3⟩
    rcases h5o with ⟨p5, hp5⟩
    intro y hy
    have hz := Z5_implies_dRow C t₁ t₂ htne h1 h7 hy
    rcases hz with ⟨hy1, hy2, hd13, hd30, hd34, _⟩
    have hw1 : w_i C 1 y = 1 :=
      w_i_eq_of_single C 1 t₁ y h1eq1 (by rw [h1]; decide) hy1
    have hw7 : w_i C 7 y = 0 :=
      w_i_eq_zero_of_single_false C 7 t₂ y h7eq1 (by rw [h7]; decide) hy2
    have hw2 : w_i C 2 y = 0 := w_i_eq_zero_of_count_zero C 2 y h2eq0
    have hw4 : w_i C 4 y = 0 := w_i_eq_zero_of_count_zero C 4 y h4eq0
    have hw6 : w_i C 6 y = 0 := w_i_eq_zero_of_count_zero C 6 y h6eq0
    rcases dRow12_columns07 C y h07 with ⟨hd1, hd2'⟩
    rcases dRow03_columns07 C y h07 with ⟨hd0, hd4'⟩
    have he1 : 2 * w_i C 3 y + count C 5 ≤ 2 * w_i C 5 y + count C 3 := by
      rw [hd1, hd2'] at hd13
      rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h4eq0, h6eq0] at hd13
      omega
    have he2 : count C 3 ≤ 2 * w_i C 3 y := by
      rw [hd2', hd0] at hd30
      rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h6eq0] at hd30
      omega
    have he3 : 2 * w_i C 5 y ≤ count C 5 := by
      rw [hd2', hd4'] at hd34
      rw [hw1, hw2, hw4, hw6, hw7, h7eq1, h2eq0, h6eq0] at hd34
      omega
    have he2' : count C 3 + 1 ≤ 2 * w_i C 3 y := by
      rw [hp3] at he2
      have hsharp := odd_le_even_succ (a := p3) (b := w_i C 3 y) (by omega)
      rw [hp3]
      omega
    have he3' : 2 * w_i C 5 y ≤ count C 5 - 1 := by
      rw [hp5] at he3
      have hsharp := even_le_odd (a := w_i C 5 y) (b := p5) (by omega)
      rw [hp5]
      omega
    have hc1 : count C 5 + 1 ≤ 2 * w_i C 5 y := by omega
    omega
end N4Code
