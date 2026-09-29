-- Prove2me | solution 1 for MilnorConjecture.norm_residue_ker_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-26T03:50:51.608398+00:00
-- url     : https://prove2.me/submissions/32624388-9910-4895-a93e-750261870710
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol
import Theorems.Thm_MilnorConjecture_norm_residue_ker_le_of_le_one
import Theorems.Thm_MilnorConjecture_norm_residue_ker_le_of_two_le

open MilnorConjecture

theorem solution (F : Type) [Field F] [NeZero (2 : F)] (n : ℕ)
    (φ : MilnorK F n →+ H F n) (hφ : ∀ a : Fin n → Fˣ, φ (symbol a) = galoisSymbol a)
    (x : MilnorK F n) (hx : φ x = 0) : ∃ y : MilnorK F n, x = 2 • y := by
  rcases Nat.lt_or_ge n 2 with h | h
  · exact norm_residue_ker_le_of_le_one F n (by omega) φ hφ x hx
  · exact norm_residue_ker_le_of_two_le F n h φ hφ x hx
