-- Prove2me | solution 2 for Leopoldt.leopoldt_CM
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:02:35.427059+00:00
-- url     : https://prove2.me/submissions/b604d2dd-1f4b-4212-af97-59bbcd5bb79b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Leopoldt_leopoldtConjecture_iff_maximalRealSubfield
import Theorems.Thm_Leopoldt_leopoldt_totallyReal

open NumberField

theorem solution (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (K : Type*) [Field K] [NumberField K] [IsCMField K] :
    Leopoldt.LeopoldtConjecture p K := by
  apply (Leopoldt.leopoldtConjecture_iff_maximalRealSubfield p K).2
  exact Leopoldt.leopoldt_totallyReal p hp (maximalRealSubfield K)
