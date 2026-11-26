-- Prove2me | solution 1 for N4Code.Z41_implies_htrue_hfalse_d2_d3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:38.810829+00:00
-- url     : https://prove2.me/submissions/ffe10bda-5e9b-42ef-8e34-88e4dae93f3e

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dOp2_le_dO_of_htrue_hfalse
import Theorems.Thm_N4Code_dPp2_add_two_of_htrue_hfalse
import Theorems.Thm_N4Code_Z4_implies_htrue_hfalse
import Theorems.Thm_N4Code_dOp2_eq_min_of_htrue_hfalse
import Theorems.Thm_N4Code_min3_eq_of_gt

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) {y : Word n} (hy : Z41 C t₁ t₂ y) :
    y t₁ = true ∧ y t₂ = false ∧ dRow C 1 y = dRow C 2 y + 1 ∧
      dRow C 2 y ≤ min (dRow C 0 y) (dRow C 3 y) := by
  rcases hy with ⟨hz4, hgt⟩
  rcases Z4_implies_htrue_hfalse C t₁ t₂ htne h1 h7 hz4 with ⟨hy1, hy2⟩
  have hOp := dOp2_eq_min_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hPp_add : dPp2 C t₁ t₂ y + 2 = dP C y :=
    dPp2_add_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hOp_le_O : dOp2 C t₁ t₂ y ≤ dO C y :=
    dOp2_le_dO_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
  have hOp_lt_P : dOp2 C t₁ t₂ y < dP C y := by
    have hgt2 : dP C y > min (dO C y) (dOp2 C t₁ t₂ y) := hz4.2.2.1
    rw [min_eq_right hOp_le_O] at hgt2
    exact hgt2
  have hPp_lt_Op : dPp2 C t₁ t₂ y < dOp2 C t₁ t₂ y := by
    have hlt : dPp2 C t₁ t₂ y < min (dO C y) (dOp2 C t₁ t₂ y) := hz4.2.2.2
    rw [min_eq_right hOp_le_O] at hlt
    exact hlt
  have hOp_eq : dOp2 C t₁ t₂ y = dP C y - 1 := by omega
  have hO_ge_P : dO C y ≥ dP C y := by
    have hmin_gt : min (dO C y) (dP C y) > dOp2 C t₁ t₂ y := hgt
    rw [hOp_eq] at hmin_gt
    have hmin_ge : dP C y ≤ min (dO C y) (dP C y) := by
      cases hdP : dP C y with
      | zero => omega
      | succ k =>
          have : k < min (dO C y) (dP C y) := by
            simpa [hdP] using hmin_gt
          exact Nat.succ_le_of_lt (by simpa [hdP] using this)
    rcases le_total (dO C y) (dP C y) with hle | hge
    · have : min (dO C y) (dP C y) = dO C y := min_eq_left hle
      rw [this] at hmin_ge
      omega
    · omega
  have hd0 : dRow C 2 y ≤ dRow C 0 y := by
    have h := le_trans hO_ge_P (min_le_left _ _)
    simpa [dO, dP, dRow, row0, row1, row2, row3] using h
  have hd1le : dRow C 2 y ≤ dRow C 1 y :=
    by
      have h := le_trans hO_ge_P (le_trans (min_le_right _ _) (min_le_left _ _))
      simpa [dO, dP, dRow, row0, row1, row2, row3] using h
  have hd3 : dRow C 2 y ≤ dRow C 3 y :=
    by
      have h := le_trans hO_ge_P (le_trans (min_le_right _ _) (min_le_right _ _))
      simpa [dO, dP, dRow, row0, row1, row2, row3] using h
  have hd2_le_min : dRow C 2 y ≤ min (dRow C 0 y) (dRow C 3 y) := le_min hd0 hd3
  have hRow2_ge_2 : 2 ≤ dRow C 2 y := by
    have hOp_ge_1 : 1 ≤ dOp2 C t₁ t₂ y := by
      exact Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hPp_lt_Op)
    rw [hOp_eq] at hOp_ge_1
    have : 1 ≤ dRow C 2 y - 1 := by
      simpa [dP, dRow, row2] using hOp_ge_1
    omega
  have hOp' : min (dRow C 0 y) (min (dRow C 1 y - 2) (dRow C 3 y)) = dRow C 2 y - 1 := by
    rw [← hOp]
    simpa [dP, dRow, row2] using hOp_eq
  have hd1' : dRow C 1 y - 2 = dRow C 2 y - 1 := by
    exact min3_eq_of_gt (a := dRow C 0 y) (c := dRow C 3 y)
      (by omega) (by omega) hOp'
  have hd1eq : dRow C 1 y = dRow C 2 y + 1 := by omega
  exact ⟨hy1, hy2, hd1eq, hd2_le_min⟩
end N4Code
