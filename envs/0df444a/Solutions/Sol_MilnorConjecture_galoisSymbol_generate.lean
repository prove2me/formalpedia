-- Prove2me | solution 1 for MilnorConjecture.galoisSymbol_generate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-26T03:50:51.001525+00:00
-- url     : https://prove2.me/submissions/1d2e1c5f-f2ff-4dd5-9ed6-ada0ce3b4719
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol
import Theorems.Thm_MilnorConjecture_galoisSymbol_generate_of_le_one
import Theorems.Thm_MilnorConjecture_galoisSymbol_generate_of_two_le

open MilnorConjecture

theorem solution (F : Type) [Field F] [NeZero (2 : F)] (n : ℕ) :
    AddSubgroup.closure (Set.range (galoisSymbol (F := F) (n := n))) = ⊤ := by
  rcases Nat.lt_or_ge n 2 with h | h
  · exact galoisSymbol_generate_of_le_one F n (by omega)
  · exact galoisSymbol_generate_of_two_le F n h
