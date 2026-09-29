-- Prove2me | solution 1 for Leopoldt.galois_totallyReal_injection
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:19:47.598869+00:00
-- url     : https://prove2.me/submissions/629f4d29-fdb8-4837-b696-ea273de6cb22
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Leopoldt_leopoldtConjecture_of_units_rank_le_one
import Theorems.Thm_Leopoldt_leopoldtConjecture_iff_exists_continuous_injection
import Theorems.Thm_Leopoldt_galois_totallyReal_injection_of_three_le_finrank

open NumberField

theorem solution (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (L : Type*) [Field L] [NumberField L] [IsTotallyReal L] [IsGalois ℚ L] :
    ∃ f : Multiplicative (Fin (Units.rank L) → ℤ_[p]) →* Leopoldt.SemilocalUnits p L,
      Function.Injective f ∧ Continuous f ∧ ∀ x, f x ∈ Leopoldt.unitClosure p L := by
  by_cases hL : 3 ≤ Module.finrank ℚ L
  · exact Leopoldt.galois_totallyReal_injection_of_three_le_finrank p hp L hL
  · apply (Leopoldt.leopoldtConjecture_iff_exists_continuous_injection p L).mp
    apply Leopoldt.leopoldtConjecture_of_units_rank_le_one
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank L
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces L
    have h3 : InfinitePlace.nrComplexPlaces L = 0 := IsTotallyReal.nrComplexPlaces_eq_zero _
    unfold NumberField.Units.rank
    omega
