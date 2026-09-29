-- Prove2me | solution 1 for Leopoldt.leopoldt_realQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:19:46.889988+00:00
-- url     : https://prove2.me/submissions/2c2f9d0b-1524-49d5-9f90-f83365df36b2

import Theorems.Thm_Leopoldt_leopoldtConjecture_of_units_rank_le_one

open NumberField

theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hK : Module.finrank ℚ K = 2) :
    Leopoldt.LeopoldtConjecture p K := by
  apply Leopoldt.leopoldtConjecture_of_units_rank_le_one
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  have h3 : InfinitePlace.nrComplexPlaces K = 0 := IsTotallyReal.nrComplexPlaces_eq_zero _
  unfold NumberField.Units.rank
  omega
