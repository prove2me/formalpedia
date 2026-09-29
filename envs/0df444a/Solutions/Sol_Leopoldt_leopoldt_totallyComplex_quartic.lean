-- Prove2me | solution 1 for Leopoldt.leopoldt_totallyComplex_quartic
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:18:12.780241+00:00
-- url     : https://prove2.me/submissions/46fe4e01-e4ef-4b90-9971-f20fde33d61d

import Theorems.Thm_Leopoldt_units_rank_of_isTotallyComplex
import Theorems.Thm_Leopoldt_leopoldtConjecture_of_units_rank_le_one

open NumberField

theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 4) :
    Leopoldt.LeopoldtConjecture p K := by
  apply Leopoldt.leopoldtConjecture_of_units_rank_le_one p K
  rw [Leopoldt.units_rank_of_isTotallyComplex K, hK]
