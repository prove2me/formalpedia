-- Prove2me | solution 1 for Leopoldt.leopoldt_totallyReal_galois
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-09T23:56:37.451033+00:00
-- url     : https://prove2.me/submissions/df43116e-1a81-45d8-adc8-d9a809263b06
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Leopoldt_galois_totallyReal_injection
import Theorems.Thm_Leopoldt_leopoldtConjecture_iff_exists_continuous_injection
import Definitions.Def_LeopoldtDefect

open NumberField

theorem solution (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (L : Type*) [Field L] [NumberField L] [IsTotallyReal L] [IsGalois ℚ L] :
    Leopoldt.LeopoldtConjecture p L :=
  (Leopoldt.leopoldtConjecture_iff_exists_continuous_injection p L).mpr
    (Leopoldt.galois_totallyReal_injection p hp L)
