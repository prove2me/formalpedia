-- Prove2me | solution 1 for Leopoldt.defect_le_rank_div_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:09:22.735077+00:00
-- url     : https://prove2.me/submissions/3cb8eb69-f689-4ea9-9e76-2b71d1b95dce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Leopoldt_defect_le_units_rank_sub_one
import Theorems.Thm_Leopoldt_defect_le_rank_div_two_of_three_le_rank

open NumberField

/-- Waldschmidt's bound `𝒟_L(K) ≤ r/2`: for `r ≤ 2` it follows from the elementary bound
`𝒟_L(K) ≤ r - 1`, and for `r ≥ 3` it is the transcendence-theoretic case. -/
theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] :
    Leopoldt.defect p K ≤ Units.rank K / 2 := by
  by_cases hr : 3 ≤ Units.rank K
  · exact Leopoldt.defect_le_rank_div_two_of_three_le_rank p K hr
  · have h := Leopoldt.defect_le_units_rank_sub_one p K
    omega
