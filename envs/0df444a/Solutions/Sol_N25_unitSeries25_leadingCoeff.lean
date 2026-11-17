-- Prove2me | solution 1 for N25.unitSeries25_leadingCoeff
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:56.17998+00:00
-- url     : https://prove2.me/submissions/143ccc26-2d72-4a13-b66c-0c7abc6fc127

import Mathlib
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_unitSeries25_normalization

set_option autoImplicit false

namespace N25

theorem _root_.solution (K : Type*) [Field K] (i : Fin 5) :
    (unitSeries25 K i).coeff (unitQOrder25 i) = 1 :=
  ((unitSeries25_normalization K).2 i).2

end N25
