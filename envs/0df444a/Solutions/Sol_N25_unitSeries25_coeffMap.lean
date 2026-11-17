-- Prove2me | solution 1 for N25.unitSeries25_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:51.458571+00:00
-- url     : https://prove2.me/submissions/48bbf01d-0880-4dda-ac77-749b6e606f31

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_N25_intSeriesC_coeffMap25

/-! Coefficient extension of the two modular units and the fields they generate. -/
noncomputable section

namespace N25

/-- The integral numerator and denominator make each unit compatible with coefficient extension. -/
theorem _root_.solution (k K : Type*) [Field k] [Field K] [Algebra k K]
    (i : Fin 5) :
    ModularCurve.coeffMap (algebraMap k K) (unitSeries25 k i) = unitSeries25 K i := by
  rw [unitSeries25, map_div₀, intSeriesC_coeffMap25, intSeriesC_coeffMap25]
  rfl

end N25
