-- Prove2me | solution 1 for N25.unitSeries25_order
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:02.993941+00:00
-- url     : https://prove2.me/submissions/00a4c06d-27ab-4eb4-9026-5b260ed822d0

import Mathlib
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_unitSeries25_normalization

set_option autoImplicit false

namespace N25

theorem _root_.solution (K : Type*) [Field K] (i : Fin 5) :
    (unitSeries25 K i).order = unitQOrder25 i :=
  ((unitSeries25_normalization K).2 i).1

end N25
