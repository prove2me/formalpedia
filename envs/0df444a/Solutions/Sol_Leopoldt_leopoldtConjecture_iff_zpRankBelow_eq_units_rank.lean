-- Prove2me | solution 1 for Leopoldt.leopoldtConjecture_iff_zpRankBelow_eq_units_rank
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:15:04.039897+00:00
-- url     : https://prove2.me/submissions/0dce9302-24de-42b3-b70a-4add240d9bf3

import Definitions.Def_LeopoldtDefect
import Theorems.Thm_Leopoldt_zpRankBelow_unitClosure_le_units_rank

open NumberField

theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] :
    Leopoldt.LeopoldtConjecture p K ↔
      Leopoldt.zpRankBelow p (Module.finrank ℚ K) (Leopoldt.unitClosure p K) =
        Units.rank K := by
  have hr := Leopoldt.zpRankBelow_unitClosure_le_units_rank p K
  constructor
  · intro h
    change Units.rank K -
      Leopoldt.zpRankBelow p (Module.finrank ℚ K) (Leopoldt.unitClosure p K) = 0 at h
    omega
  · intro h
    change Units.rank K -
      Leopoldt.zpRankBelow p (Module.finrank ℚ K) (Leopoldt.unitClosure p K) = 0
    omega
