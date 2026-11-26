-- Prove2me | solution 1 for N4Code.Z41_of_htrue_hfalse_d2_d3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:15.4668+00:00
-- url     : https://prove2.me/submissions/e88d2291-d1f0-4c73-b921-edf6f2070472

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dOp2_le_dO_of_htrue_hfalse
import Theorems.Thm_N4Code_dOp2_eq_min_of_htrue_hfalse
import Theorems.Thm_N4Code_dPp2_eq_sub_two_of_htrue_hfalse
import Theorems.Thm_N4Code_dRow_ge_two_of_mismatch
import Theorems.Thm_N4Code_min3_eq_middle_of_le

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) {y : Word n}
    (hy1 : y t₁ = true) (hy2 : y t₂ = false)
    (hd2 : dRow C 1 y = dRow C 2 y + 1)
    (hd3 : dRow C 2 y ≤ min (dRow C 0 y) (dRow C 3 y)) :
    Z41 C t₁ t₂ y := by
  have hOp := dOp2_eq_min_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hPp : dPp2 C t₁ t₂ y = dP C y - 2 :=
    dPp2_eq_sub_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hOp_le_O : dOp2 C t₁ t₂ y ≤ dO C y :=
    dOp2_le_dO_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hd0 : dRow C 2 y ≤ dRow C 0 y := le_trans hd3 (min_le_left _ _)
  have hd4 : dRow C 2 y ≤ dRow C 3 y := le_trans hd3 (min_le_right _ _)
  have hd1 : dRow C 2 y ≤ dRow C 1 y := by
    rw [hd2]
    omega
  have hP_ge_2 : 2 ≤ dP C y := by
    have hne1 : y t₁ ≠ row C ⟨2, by decide⟩ t₁ := by
      simp [row, colBit, h1, col1, hy1]
    have hne2 : y t₂ ≠ row C ⟨2, by decide⟩ t₂ := by
      simp [row, colBit, h7, col7, hy2]
    change 2 ≤ dRow C ⟨2, by decide⟩ y
    exact dRow_ge_two_of_mismatch C ⟨2, by decide⟩ t₁ t₂ htne y hne1 hne2
  have hO_ge_P : dO C y ≥ dP C y := by
    have hO' : dRow C 2 y ≤ min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) :=
      le_min hd0 (le_min hd1 hd4)
    simpa [dO, dP, dRow, row0, row1, row2, row3] using hO'
  have hOp_eq : dOp2 C t₁ t₂ y = dP C y - 1 := by
    have hd1m2 : dRow C 1 y - 2 = dRow C 2 y - 1 := by omega
    have hOp' : min (dRow C 0 y) (min (dRow C 1 y - 2) (dRow C 3 y)) = dRow C 2 y - 1 := by
      rw [hd1m2]
      apply min3_eq_middle_of_le
      · omega
      · omega
    rw [hOp]
    simpa [dP, dRow, row2] using hOp'
  have hgt1 : dO C y > min (dP C y) (dPp2 C t₁ t₂ y) := by
    have hmin : min (dP C y) (dP C y - 2) = dP C y - 2 := by
      apply min_eq_right
      omega
    rw [hPp, hmin]
    change dRow C 2 y - 2 < min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y))
    have hmin_ge : dRow C 2 y ≤ min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) :=
      le_min hd0 (le_min hd1 hd4)
    omega
  have hgt2 : dP C y > min (dO C y) (dOp2 C t₁ t₂ y) := by
    have hmin : min (dO C y) (dOp2 C t₁ t₂ y) = dOp2 C t₁ t₂ y := min_eq_right hOp_le_O
    rw [hmin, hOp_eq]
    omega
  have hgt3 : dPp2 C t₁ t₂ y < min (dO C y) (dOp2 C t₁ t₂ y) := by
    have hmin : min (dO C y) (dOp2 C t₁ t₂ y) = dOp2 C t₁ t₂ y := min_eq_right hOp_le_O
    rw [hmin, hOp_eq, hPp]
    omega
  have hgt4 : min (dO C y) (dP C y) > dOp2 C t₁ t₂ y := by
    have hmin : min (dO C y) (dP C y) = dP C y := by
      apply min_eq_right
      exact hO_ge_P
    rw [hmin, hOp_eq]
    omega
  unfold Z41
  refine ⟨⟨?_, hgt1, hgt2, hgt3⟩, hgt4⟩
  · simp [hy1, hy2]
end N4Code
