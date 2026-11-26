-- Prove2me | solution 1 for N4Code.g2_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:24.39804+00:00
-- url     : https://prove2.me/submissions/c2e6ecda-61c2-49f7-ba23-53842cfbce7c

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_flipTwoBits_involutive
import Theorems.Thm_N4Code_z_not_A_implies_34
import Theorems.Thm_N4Code_Z34_flip2_closed
import Theorems.Thm_N4Code_z_34_implies_not_A

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C _C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    Function.Bijective (g2 C t₁ t₂) := by
  have hcl : ∀ y : Word n, (Z3 C t₁ t₂ y ∨ Z4 C t₁ t₂ y) →
      (Z3 C t₁ t₂ (flipTwoBits t₁ t₂ y) ∨ Z4 C t₁ t₂ (flipTwoBits t₁ t₂ y)) :=
    Z34_flip2_closed C t₁ t₂ htne h1 h7
  have hinv : ∀ y : Word n, g2 C t₁ t₂ (g2 C t₁ t₂ y) = y := by
    intro y
    by_cases hy : Z1 C t₁ t₂ y ∨ Z2 C t₁ t₂ y ∨ Z5 C t₁ t₂ y
    · simp [g2, hy]
    · have hz : Z3 C t₁ t₂ y ∨ Z4 C t₁ t₂ y := z_not_A_implies_34 C t₁ t₂ y hy
      have hcl' := hcl y hz
      have hnotA : ¬ (Z1 C t₁ t₂ (flipTwoBits t₁ t₂ y) ∨ Z2 C t₁ t₂ (flipTwoBits t₁ t₂ y) ∨
          Z5 C t₁ t₂ (flipTwoBits t₁ t₂ y)) :=
        z_34_implies_not_A C t₁ t₂ (flipTwoBits t₁ t₂ y) hcl'
      simp [g2, hy, hnotA, flipTwoBits_involutive t₁ t₂ y]
  refine ⟨?_, ?_⟩
  · intro a b hab
    rw [← hinv a, ← hinv b, hab]
  · intro z
    exact ⟨g2 C t₁ t₂ z, hinv z⟩
end N4Code
