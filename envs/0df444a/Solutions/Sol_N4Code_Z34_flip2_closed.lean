-- Prove2me | solution 1 for N4Code.Z34_flip2_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:39.631111+00:00
-- url     : https://prove2.me/submissions/f7751f9d-9c30-4fd8-9cf0-fd7e9d2b72ef

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_bool_ne_cases
import Theorems.Thm_N4Code_dOp2_le_dO_of_htrue_hfalse
import Theorems.Thm_N4Code_dO_le_dOp2_of_hfalse_htrue
import Theorems.Thm_N4Code_dPp2_add_two_of_htrue_hfalse
import Theorems.Thm_N4Code_dP_add_two_of_hfalse_htrue
import Theorems.Thm_N4Code_Z4_implies_htrue_hfalse
import Theorems.Thm_N4Code_distances_flip2_htrue_hfalse
import Theorems.Thm_N4Code_distances_flip2_hfalse_htrue

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n) :
    (Z3 C t₁ t₂ y ∨ Z4 C t₁ t₂ y) →
      (Z3 C t₁ t₂ (flipTwoBits t₁ t₂ y) ∨ Z4 C t₁ t₂ (flipTwoBits t₁ t₂ y)) := by
  intro hz
  have hne : y t₁ ≠ y t₂ := by
    rcases hz with hz | hz
    · exact hz.1
    · exact hz.1
  rcases bool_ne_cases hne with hyo | hyo
  · rcases hyo with ⟨hy1, hy2⟩
    have hd := distances_flip2_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
    have hdO' : dO C (flipTwoBits t₁ t₂ y) = dOp2 C t₁ t₂ y := hd.1
    have hdP' : dP C (flipTwoBits t₁ t₂ y) = dP C y - 2 := by omega
    have hdOp2' : dOp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dO C y := hd.2.2.1
    have hdPp2' : dPp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dP C y := hd.2.2.2
    have hPp_lt_P : dPp2 C t₁ t₂ y < dP C y := by
      have hPp := dPp2_add_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
      omega
    have hmin0 : min (dP C y) (dPp2 C t₁ t₂ y) = dPp2 C t₁ t₂ y :=
      min_eq_right (le_of_lt hPp_lt_P)
    have hOp_le_O : dOp2 C t₁ t₂ y ≤ dO C y :=
      dOp2_le_dO_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
    rcases hz with hz | hz
    · rcases hz with ⟨_, hgt, hle⟩
      left
      unfold Z3
      refine ⟨?_, ?_, ?_⟩
      · simp [flipTwoBits, hy1, hy2]
      · rw [hdO', hdP', hdPp2']
        have hmin : min (dP C y - 2) (dP C y) = dP C y - 2 := by
          apply min_eq_left
          omega
        rw [hmin]
        have hOp_ge_P : dOp2 C t₁ t₂ y ≥ dP C y := le_trans hle (min_le_right _ _)
        omega
      · rw [hdP', hdOp2', hdO']
        have hP_le_Op : dP C y ≤ dOp2 C t₁ t₂ y := le_trans hle (min_le_right _ _)
        have hP_le_O : dP C y ≤ dO C y := le_trans hle (min_le_left _ _)
        have hgt' : dO C y > dPp2 C t₁ t₂ y := by
          rw [hmin0] at hgt
          exact hgt
        have hdO_ge : dP C y - 2 ≤ dO C y := by omega
        have hdOp_ge : dP C y - 2 ≤ dOp2 C t₁ t₂ y := by omega
        exact le_min hdOp_ge hdO_ge
    · rcases hz with ⟨_, _, hgt24, hlt⟩
      left
      unfold Z3
      refine ⟨?_, ?_, ?_⟩
      · simp [flipTwoBits, hy1, hy2]
      · rw [hdO', hdP', hdPp2']
        have hmin0' : min (dO C y) (dOp2 C t₁ t₂ y) = dOp2 C t₁ t₂ y :=
          min_eq_right hOp_le_O
        have hPp_lt_Op : dPp2 C t₁ t₂ y < dOp2 C t₁ t₂ y := by
          rw [hmin0'] at hlt
          exact hlt
        have hOp_lt_P : dOp2 C t₁ t₂ y < dP C y := by
          rw [hmin0'] at hgt24
          exact hgt24
        have hPp' : dPp2 C t₁ t₂ y + 2 = dP C y :=
          dPp2_add_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
        have hOp_eq : dOp2 C t₁ t₂ y = dP C y - 1 := by omega
        have hmin : min (dP C y - 2) (dP C y) = dP C y - 2 := by
          apply min_eq_left
          omega
        rw [hmin, hOp_eq]
        omega
      · rw [hdP', hdOp2', hdO']
        have hmin0' : min (dO C y) (dOp2 C t₁ t₂ y) = dOp2 C t₁ t₂ y :=
          min_eq_right hOp_le_O
        have hPp_lt_Op : dPp2 C t₁ t₂ y < dOp2 C t₁ t₂ y := by
          rw [hmin0'] at hlt
          exact hlt
        have hOp_lt_P : dOp2 C t₁ t₂ y < dP C y := by
          rw [hmin0'] at hgt24
          exact hgt24
        have hPp' : dPp2 C t₁ t₂ y + 2 = dP C y :=
          dPp2_add_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
        have hOp_eq : dOp2 C t₁ t₂ y = dP C y - 1 := by omega
        have hO_ge : dO C y ≥ dP C y - 1 := by omega
        have hdP_ge : dP C y - 2 ≤ dOp2 C t₁ t₂ y := by omega
        have hdO_ge : dP C y - 2 ≤ dO C y := by omega
        exact le_min hdP_ge hdO_ge
  · rcases hyo with ⟨hy1, hy2⟩
    have hd := distances_flip2_hfalse_htrue C t₁ t₂ htne h1 h7 y hy1 hy2
    have hdO' : dO C (flipTwoBits t₁ t₂ y) = dOp2 C t₁ t₂ y := hd.1
    have hdP' : dP C (flipTwoBits t₁ t₂ y) = dP C y + 2 := hd.2.1
    have hdOp2' : dOp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dO C y := hd.2.2.1
    have hdPp2' : dPp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dP C y := hd.2.2.2
    rcases hz with hz | hz
    · rcases hz with ⟨_, hgt, hle⟩
      have hOp_ge_O : dO C y ≤ dOp2 C t₁ t₂ y :=
        dO_le_dOp2_of_hfalse_htrue C t₁ t₂ htne h1 h7 y hy1 hy2
      have hP_lt_Pp : dP C y < dPp2 C t₁ t₂ y := by
        have hP := dP_add_two_of_hfalse_htrue C t₁ t₂ htne h1 h7 y hy1 hy2
        omega
      have hmin0 : min (dP C y) (dPp2 C t₁ t₂ y) = dP C y :=
        min_eq_left (le_of_lt hP_lt_Pp)
      have hO_gt_P : dO C y > dP C y := by
        rw [hmin0] at hgt
        exact hgt
      have hmin2 : min (dOp2 C t₁ t₂ y) (dO C y) = dO C y := min_eq_right hOp_ge_O
      by_cases hbig : dO C y ≥ dP C y + 2
      · left
        unfold Z3
        refine ⟨?_, ?_, ?_⟩
        · simp [flipTwoBits, hy1, hy2]
        · rw [hdO', hdP', hdPp2']
          have hmin : min (dP C y + 2) (dP C y) = dP C y := by
            apply min_eq_right
            omega
          rw [hmin]
          omega
        · rw [hdP', hdOp2', hdO']
          rw [hmin2]
          omega
      · right
        have hO_eq : dO C y = dP C y + 1 := by omega
        unfold Z4
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [flipTwoBits, hy1, hy2]
        · rw [hdO', hdP', hdPp2']
          have hmin : min (dP C y + 2) (dP C y) = dP C y := by
            apply min_eq_right
            omega
          rw [hmin]
          omega
        · rw [hdP', hdOp2', hdO']
          rw [hmin2, hO_eq]
          omega
        · rw [hdPp2', hdO', hdOp2']
          rw [hmin2, hO_eq]
          omega
    · exfalso
      rcases Z4_implies_htrue_hfalse C t₁ t₂ htne h1 h7 hz with ⟨ht₁, _⟩
      have hb : (true : Bool) = false := by simpa [hy1] using ht₁.symm
      simp at hb
end N4Code
