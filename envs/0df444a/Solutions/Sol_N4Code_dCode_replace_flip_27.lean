-- Prove2me | solution 1 for N4Code.dCode_replace_flip_27
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:00.780874+00:00
-- url     : https://prove2.me/submissions/f3e401e3-4b3c-4405-af88-e45902ae6736

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_flipTwoBits_involutive
import Theorems.Thm_N4Code_dCode_replace_27

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂) (y : Word n)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    dCode (replaceColumn (replaceColumn C t₁ col3) t₂ col5) (flipTwoBits t₁ t₂ y) =
      min (dOp2 C t₁ t₂ y) (dP C y) := by
  rw [dCode_replace_27 C t₁ t₂ htne (flipTwoBits t₁ t₂ y) h1 h7]
  unfold dOp2 dPp2
  rw [flipTwoBits_involutive t₁ t₂ y]
end N4Code
