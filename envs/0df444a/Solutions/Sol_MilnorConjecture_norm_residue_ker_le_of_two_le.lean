-- Prove2me | solution 1 for MilnorConjecture.norm_residue_ker_le_of_two_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-26T12:26:37.032987+00:00
-- url     : https://prove2.me/submissions/685c82d3-0afd-4860-8967-abb118f45167
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol
import Theorems.Thm_MilnorConjecture_norm_residue_ker_le_two
import Theorems.Thm_MilnorConjecture_norm_residue_ker_le_of_three_le

open MilnorConjecture

theorem solution (F : Type) [Field F] [NeZero (2 : F)] (n : ℕ) (hn : 2 ≤ n)
    (φ : MilnorK F n →+ H F n) (hφ : ∀ a : Fin n → Fˣ, φ (symbol a) = galoisSymbol a)
    (x : MilnorK F n) (hx : φ x = 0) : ∃ y : MilnorK F n, x = 2 • y := by
  obtain rfl | h3 := hn.eq_or_lt
  · exact norm_residue_ker_le_two F φ hφ x hx
  · exact norm_residue_ker_le_of_three_le F n h3 φ hφ x hx
