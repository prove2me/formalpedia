-- Prove2me | solution 1 for N4Code.Z5_implies_dRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:08.537914+00:00
-- url     : https://prove2.me/submissions/f9e4ac17-670f-40bc-9a38-2d517027fa03

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dOp2_le_dO_of_htrue_hfalse
import Theorems.Thm_N4Code_Z5_implies_htrue_hfalse
import Theorems.Thm_N4Code_dOp2_eq_min_of_htrue_hfalse
import Theorems.Thm_N4Code_dPp2_eq_sub_two_of_htrue_hfalse
import Theorems.Thm_N4Code_dRow_ge_two_of_mismatch
import Theorems.Thm_N4Code_sub_one_le_contra
import Theorems.Thm_N4Code_sub_two_le_sub_two

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) {y : Word n} (hy : Z5 C t₁ t₂ y) :
    y t₁ = true ∧ y t₂ = false ∧ dRow C 1 y ≤ dRow C 2 y ∧
      dRow C 2 y - 1 ≤ dRow C 0 y ∧ dRow C 2 y - 1 ≤ dRow C 3 y ∧
        dRow C 2 y - 1 ≤ dO C y := by
  have hor := Z5_implies_htrue_hfalse C t₁ t₂ htne h1 h7 hy
  rcases hor with ⟨hy1, hy2⟩
  have hOp := dOp2_eq_min_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hPp : dPp2 C t₁ t₂ y = dP C y - 2 :=
    dPp2_eq_sub_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hOp_le_O : dOp2 C t₁ t₂ y ≤ dO C y :=
    dOp2_le_dO_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hP_ge_2 : 2 ≤ dP C y := by
    have hne1 : y t₁ ≠ row C ⟨2, by decide⟩ t₁ := by
      simp [row, colBit, h1, col1, hy1]
    have hne2 : y t₂ ≠ row C ⟨2, by decide⟩ t₂ := by
      simp [row, colBit, h7, col7, hy2]
    change 2 ≤ dRow C ⟨2, by decide⟩ y
    exact dRow_ge_two_of_mismatch C ⟨2, by decide⟩ t₁ t₂ htne y hne1 hne2
  have hOp_le_Pp : dOp2 C t₁ t₂ y ≤ dPp2 C t₁ t₂ y := by
    have hmin : min (dO C y) (dOp2 C t₁ t₂ y) = dOp2 C t₁ t₂ y := min_eq_right hOp_le_O
    have hle : min (dO C y) (dOp2 C t₁ t₂ y) ≤ dPp2 C t₁ t₂ y := hy.2.2.2
    rw [hmin] at hle
    exact hle
  have hO_ge : dO C y ≥ dP C y - 1 := by
    have hminP : min (dP C y) (dP C y - 2) = dP C y - 2 := by
      apply min_eq_right
      omega
    have hgt : dO C y > min (dP C y) (dPp2 C t₁ t₂ y) := hy.2.1
    rw [hPp, hminP] at hgt
    change dP C y - 2 < dO C y at hgt
    omega
  have hRow2_ge_2 : 2 ≤ dRow C 2 y := by
    simpa [dP, dRow, row2] using hP_ge_2
  have hd0_ge : dRow C 2 y - 1 ≤ dRow C 0 y := by
    have hO' : dRow C 2 y - 1 ≤ dO C y := by
      simpa [dO, dP, dRow, row0, row1, row2, row3] using hO_ge
    exact le_trans hO' (min_le_left _ _)
  have hd4_ge : dRow C 2 y - 1 ≤ dRow C 3 y := by
    have hO' : dRow C 2 y - 1 ≤ dO C y := by
      simpa [dO, dP, dRow, row0, row1, row2, row3] using hO_ge
    exact le_trans hO' (le_trans (min_le_right _ _) (min_le_right _ _))
  have hdO_ge : dRow C 2 y - 1 ≤ dO C y := by
    simpa [dO, dP, dRow, row0, row1, row2, row3] using hO_ge
  have hd13 : dRow C 1 y ≤ dRow C 2 y := by
    have hOp_le_Pp' : dOp2 C t₁ t₂ y ≤ dP C y - 2 := by
      rw [← hPp]
      exact hOp_le_Pp
    rw [hOp] at hOp_le_Pp'
    rcases (min_le_iff.mp hOp_le_Pp') with h0 | hrest
    · exfalso
      exact sub_one_le_contra hd0_ge h0 hRow2_ge_2
    · rcases (min_le_iff.mp hrest) with h1 | h4
      · exact sub_two_le_sub_two h1 hRow2_ge_2
      · exfalso
        exact sub_one_le_contra hd4_ge h4 hRow2_ge_2
  exact ⟨hy1, hy2, hd13, hd0_ge, hd4_ge, hdO_ge⟩
end N4Code
