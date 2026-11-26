-- Prove2me | solution 1 for N4Code.z_rel_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:27.839351+00:00
-- url     : https://prove2.me/submissions/a2c87fe3-56d3-4763-aff4-f43e386993ac

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dCode_replace_27
import Theorems.Thm_N4Code_replace_27_eq
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
    (hy : Z2 C t₁ t₂ y) : dCode C y = dCode C' y ∧ dCode C y = dO C y := by
  have hrep : C' = replaceColumn (replaceColumn C t₁ col3) t₂ col5 :=
    replace_27_eq C C' t₁ t₂ htne h3 h5 hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC' : dCode C' y = min (dO C y) (dPp2 C t₁ t₂ y) := by
    rw [hrep, dCode_replace_27 C t₁ t₂ htne y h1 h7]
  rcases hy with ⟨_hne, hle⟩
  have hOleP : dO C y ≤ dP C y := le_trans hle (min_le_left _ _)
  have hOlePp : dO C y ≤ dPp2 C t₁ t₂ y := le_trans hle (min_le_right _ _)
  constructor
  · rw [hdC, hdC', min_eq_left hOleP, min_eq_left hOlePp]
  · rw [hdC, min_eq_left hOleP]
end N4Code
