-- Prove2me | solution 1 for N4Code.z_rel_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:29.132531+00:00
-- url     : https://prove2.me/submissions/5c2e920c-a2e7-41ce-bc72-62634f21c385

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dOp2_le_dO_of_htrue_hfalse
import Theorems.Thm_N4Code_dCode_replace_flip_27
import Theorems.Thm_N4Code_replace_27_eq
import Theorems.Thm_N4Code_Z4_implies_htrue_hfalse
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
    (hy : Z4 C t₁ t₂ y) :
    dCode C y = min (dO C y) (dP C y) ∧
      dCode C' (flipTwoBits t₁ t₂ y) = dOp2 C t₁ t₂ y ∧
        dP C y ≥ dCode C' (flipTwoBits t₁ t₂ y) := by
  have hrep : C' = replaceColumn (replaceColumn C t₁ col3) t₂ col5 :=
    replace_27_eq C C' t₁ t₂ htne h3 h5 hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC'f : dCode C' (flipTwoBits t₁ t₂ y) = min (dOp2 C t₁ t₂ y) (dP C y) := by
    rw [hrep, dCode_replace_flip_27 C t₁ t₂ htne y h1 h7]
  have hor := Z4_implies_htrue_hfalse C t₁ t₂ htne h1 h7 hy
  rcases hor with ⟨hy1, hy2⟩
  have hOp_lt_P : dOp2 C t₁ t₂ y < dP C y := by
    have hle : dOp2 C t₁ t₂ y ≤ dO C y :=
      dOp2_le_dO_of_htrue_hfalse C t₁ t₂ htne h1 h7 y hy1 hy2
    have hgt : dP C y > min (dO C y) (dOp2 C t₁ t₂ y) := hy.2.2.1
    rw [min_eq_right hle] at hgt
    exact hgt
  constructor
  · exact hdC
  · constructor
    · rw [hdC'f, min_eq_left (le_of_lt hOp_lt_P)]
    · rw [hdC'f, min_eq_left (le_of_lt hOp_lt_P)]
      exact le_of_lt hOp_lt_P
end N4Code
