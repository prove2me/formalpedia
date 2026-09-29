-- Prove2me | solution 1 for Leopoldt.defect_eq_zero_cyclotomicField
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:18:29.351238+00:00
-- url     : https://prove2.me/submissions/a11387b2-fd56-44b9-aa55-d36109d247cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_LeopoldtDefect
import Theorems.Thm_Leopoldt_defect_le_units_rank_sub_one
import Theorems.Thm_Leopoldt_units_rank_cyclotomicField
import Theorems.Thm_Leopoldt_defect_eq_zero_cyclotomicField_of_four_lt_totient

open NumberField

theorem solution (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Leopoldt.defect p (CyclotomicField n ℚ) = 0 := by
  by_cases h : 4 < n.totient
  · exact Leopoldt.defect_eq_zero_cyclotomicField_of_four_lt_totient p n h
  · have h1 := Leopoldt.defect_le_units_rank_sub_one p (CyclotomicField n ℚ)
    have h2 := Leopoldt.units_rank_cyclotomicField n
    have h3 : n.totient / 2 - 1 ≤ 1 := by omega
    omega
