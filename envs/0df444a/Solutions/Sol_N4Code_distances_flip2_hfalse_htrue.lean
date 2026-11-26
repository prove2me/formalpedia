-- Prove2me | solution 1 for N4Code.distances_flip2_hfalse_htrue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:37.64631+00:00
-- url     : https://prove2.me/submissions/d57152de-740a-4433-a54c-0acc311fe441

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_flipTwoBits_involutive
import Theorems.Thm_N4Code_dRow12_flip2_add_two

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = false) (hy2 : y t₂ = true) :
    dO C (flipTwoBits t₁ t₂ y) = dOp2 C t₁ t₂ y ∧
      dP C (flipTwoBits t₁ t₂ y) = dP C y + 2 ∧
      dOp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dO C y ∧
      dPp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dP C y := by
  constructor
  · rfl
  · constructor
    · unfold dP
      exact (dRow12_flip2_add_two C t₁ t₂ htne h1 h7 y hy1 hy2).2
    · constructor
      · unfold dOp2
        rw [flipTwoBits_involutive t₁ t₂ y]
      · unfold dPp2
        rw [flipTwoBits_involutive t₁ t₂ y]
end N4Code
