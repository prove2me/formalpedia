-- Prove2me | solution 1 for N25.unitLaurentField25C_eq_modularField_of_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:53.161532+00:00
-- url     : https://prove2.me/submissions/04e7a5fb-de81-4f01-abd4-6235c501e356

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_N25_unitLaurentField25C_adjoin_coeffMap

/-! Coefficient extension of the two modular units and the fields they generate. -/
noncomputable section

namespace N25

/-- Generation by the two units is preserved by arbitrary coefficient-field extension. -/
theorem _root_.solution (k K : Type*)
    [Field k] [Field K] [Algebra k K]
    (h : unitLaurentField25C k = ModularCurve.qExpFunctionFieldC k N25.Endgame.Γ25) :
    unitLaurentField25C K = ModularCurve.qExpFunctionFieldC K N25.Endgame.Γ25 := by
  rw [ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC k K,
    ← h, unitLaurentField25C_adjoin_coeffMap]

end N25
