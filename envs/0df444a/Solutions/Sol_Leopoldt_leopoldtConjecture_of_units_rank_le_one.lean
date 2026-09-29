-- Prove2me | solution 1 for Leopoldt.leopoldtConjecture_of_units_rank_le_one
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:18:03.251865+00:00
-- url     : https://prove2.me/submissions/9c603553-6cc1-4785-b7a6-5b02bb450b5a

import Theorems.Thm_Leopoldt_defect_le_units_rank_sub_one

open NumberField

theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] (h : Units.rank K ≤ 1) :
    Leopoldt.LeopoldtConjecture p K := by
  have := Leopoldt.defect_le_units_rank_sub_one p K
  unfold Leopoldt.LeopoldtConjecture
  omega
