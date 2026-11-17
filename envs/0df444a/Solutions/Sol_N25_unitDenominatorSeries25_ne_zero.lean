-- Prove2me | solution 1 for N25.unitDenominatorSeries25_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:54.854001+00:00
-- url     : https://prove2.me/submissions/14b1eb4c-1075-40b0-9aa3-9b891f302a73

import Mathlib
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_unitSeries25_normalization

set_option autoImplicit false

namespace N25

theorem _root_.solution (K : Type*) [Field K] :
    ModularCurve.intSeriesC K unitDenominatorSeries25 ≠ 0 :=
  (unitSeries25_normalization K).1

end N25
