-- Prove2me | solution 1 for N4Code.dCode_replace_27
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:00.850981+00:00
-- url     : https://prove2.me/submissions/d8156378-c97b-4ec6-8b8b-a1a9218913de

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dRow_replace_27_eq
import Theorems.Thm_N4Code_dRow_replace_27_2

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂) (y : Word n)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    dCode (replaceColumn (replaceColumn C t₁ col3) t₂ col5) y =
      min (dO C y) (dPp2 C t₁ t₂ y) := by
  unfold dCode dO dPp2 dP
  change min (dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) ⟨0, by decide⟩ y)
      (min (dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) ⟨1, by decide⟩ y)
        (min (dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) ⟨2, by decide⟩ y)
          (dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) ⟨3, by decide⟩ y))) =
    min (min (dRow C ⟨0, by decide⟩ y) (min (dRow C ⟨1, by decide⟩ y) (dRow C ⟨3, by decide⟩ y)))
      (dRow C ⟨2, by decide⟩ (flipTwoBits t₁ t₂ y))
  rw [dRow_replace_27_eq C t₁ t₂ htne ⟨0, by decide⟩ (by decide) y h1 h7,
    dRow_replace_27_eq C t₁ t₂ htne ⟨1, by decide⟩ (by decide) y h1 h7,
    dRow_replace_27_2 C t₁ t₂ htne y h1 h7,
    dRow_replace_27_eq C t₁ t₂ htne ⟨3, by decide⟩ (by decide) y h1 h7]
  omega
end N4Code
