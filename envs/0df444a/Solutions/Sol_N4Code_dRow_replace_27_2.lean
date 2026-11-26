-- Prove2me | solution 1 for N4Code.dRow_replace_27_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:13.76077+00:00
-- url     : https://prove2.me/submissions/6d4c0d49-b912-47db-a351-a6c9897277ea

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dRow_eq_indicator_sum


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (y : Word n) (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) ⟨2, by decide⟩ y =
      dRow C ⟨2, by decide⟩ (flipTwoBits t₁ t₂ y) := by
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu1 : u = t₁
  · by_cases hu2 : u = t₂
    · exfalso
      exact htne (hu1.symm.trans hu2)
    · have ht' : ¬ t₁ = t₂ := fun h => hu2 (hu1.trans h)
      by_cases hyu : y u = true <;>
        simp [replaceColumn, flipTwoBits, hu1, h1, colBit, col1, col3, ht']
  · by_cases hu2 : u = t₂
    · have ht' : ¬ t₁ = t₂ := fun h => hu1 (hu2.trans h.symm)
      by_cases hyu : y u = true <;>
        simp [replaceColumn, flipTwoBits, hu2, h7, colBit, col7, col5]
    · by_cases hyu : y u = true <;>
        simp [replaceColumn, flipTwoBits, hu1, hu2, hyu]
end N4Code
