-- Prove2me | solution 1 for N4Code.z4_empty_of_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:25.561171+00:00
-- url     : https://prove2.me/submissions/33cf5176-b3f9-44a5-a1ef-ca5fdc91ec22

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_hammingDist_row1_row2_eq
import Theorems.Thm_N4Code_dRow12_sum_decomp
import Theorems.Thm_N4Code_Z41_implies_htrue_hfalse_d2_d3

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (h : Even (hammingDist (row1 C) (row2 C))) :
    ∀ y : Word n, ¬ Z41 C t₁ t₂ y := by
  intro y hy
  have hw : hammingDist (row1 C) (row2 C) =
      count C 2 + count C 3 + count C 4 + count C 5 :=
    hammingDist_row1_row2_eq C h07
  have hsum_even : Even (count C 2 + count C 3 + count C 4 + count C 5) := by
    simpa [hw] using h
  have hz := Z41_implies_htrue_hfalse_d2_d3 C t₁ t₂ htne h1 h7 hy
  rcases hz with ⟨_hy1, _hy2, hd2, _⟩
  have hdecomp := dRow12_sum_decomp C y h07
  have hsum_odd : Odd (dRow C 1 y + dRow C 2 y) := by
    rw [hd2]
    exact ⟨dRow C 2 y, by omega⟩
  rcases hsum_even with ⟨m, hm⟩
  have heven : Even (dRow C 1 y + dRow C 2 y) := by
    rw [hdecomp, hm]
    exact ⟨m + (w_i C 0 y + w_i C 1 y + (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y)),
      by omega⟩
  rcases hsum_odd with ⟨k, hk⟩
  rcases heven with ⟨l, hl⟩
  omega
end N4Code
