-- Prove2me | solution 1 for N4Code.z_rel_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:49.786685+00:00
-- url     : https://prove2.me/submissions/c59c2365-8b75-4a63-9401-5ca275150cf5

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dPp2_add_two_of_htrue_hfalse
import Theorems.Thm_N4Code_dRow_replace_27_2
import Theorems.Thm_N4Code_dCode_replace_27
import Theorems.Thm_N4Code_replace_27_eq
import Theorems.Thm_N4Code_Z5_implies_htrue_hfalse
import Theorems.Thm_N4Code_dCode_eq_min_dO_dP


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7)
    (h3 : C' t₁ = col3) (h5 : C' t₂ = col5)
    (hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u) {y : Word n}
    (hy : Z5 C t₁ t₂ y) :
    dCode C y = min (dO C y) (dP C y) ∧ dP C y > dCode C' y ∧ dCode C' y = dP C' y := by
  have hrep : C' = replaceColumn (replaceColumn C t₁ col3) t₂ col5 :=
    replace_27_eq C C' t₁ t₂ htne h3 h5 hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC' : dCode C' y = min (dO C y) (dPp2 C t₁ t₂ y) := by
    rw [hrep, dCode_replace_27 C t₁ t₂ htne y h1 h7]
  have hor := Z5_implies_htrue_hfalse C t₁ t₂ htne h1 h7 hy
  rcases hor with ⟨hy1, hy2⟩
  have hPp_lt_O : dPp2 C t₁ t₂ y < dO C y := by
    have hP : dPp2 C t₁ t₂ y + 2 = dP C y :=
      dPp2_add_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
    have hPp_le_P : dPp2 C t₁ t₂ y ≤ dP C y := by omega
    have hmin : min (dP C y) (dPp2 C t₁ t₂ y) = dPp2 C t₁ t₂ y :=
      min_eq_right hPp_le_P
    have hgt : dO C y > min (dP C y) (dPp2 C t₁ t₂ y) := hy.2.1
    rw [hmin] at hgt
    exact hgt
  constructor
  · exact hdC
  · constructor
    · rw [hdC', min_eq_right (le_of_lt hPp_lt_O)]
      have hP : dPp2 C t₁ t₂ y + 2 = dP C y :=
        dPp2_add_two_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
      omega
    · rw [hdC', min_eq_right (le_of_lt hPp_lt_O)]
      rw [hrep]
      change dRow C ⟨2, by decide⟩ (flipTwoBits t₁ t₂ y) =
        dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) ⟨2, by decide⟩ y
      rw [dRow_replace_27_2 C t₁ t₂ htne y h1 h7]
end N4Code
