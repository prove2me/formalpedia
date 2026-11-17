-- Prove2me | solution 1 for N25.intSeriesC_coeffMap25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:54.674984+00:00
-- url     : https://prove2.me/submissions/3058bcd3-e85b-4a0c-a52f-783af0f73dee

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

/-! Coefficient extension of the two modular units and the fields they generate. -/
noncomputable section

namespace N25

/-- Integral series commute with every coefficient-field extension. -/
theorem _root_.solution (k K : Type*) [Field k] [Field K] [Algebra k K]
    (s : PowerSeries ℤ) :
    ModularCurve.coeffMap (algebraMap k K) (ModularCurve.intSeriesC k s) =
      ModularCurve.intSeriesC K s := by
  ext n
  simp only [ModularCurve.intSeriesC, ModularCurve.coeffMap_coeff]
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs <;> simp [PowerSeries.coeff_map, map_intCast]

end N25
