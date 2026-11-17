-- Prove2me | solution 1 for N25.unitLaurentField25C_eq_modularField_iff
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:01.685209+00:00
-- url     : https://prove2.me/submissions/161e7275-1965-4c4b-bbef-2ef1f4d8a914

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_N25_modularField_top_map_val25
import Theorems.Thm_N25_unitLaurentField25C_eq_map

/-! Coefficient extension of the two modular units and the fields they generate. -/
noncomputable section

namespace N25

/-- Generation in the modular field is equivalent to equality of its Laurent-series subfields. -/
theorem _root_.solution (K : Type*) [Field K] :
    unitLaurentField25C K = ModularCurve.qExpFunctionFieldC K N25.Endgame.Γ25 ↔
      IntermediateField.adjoin K
        ({U25C K 0, U25C K 0 / U25C K 1} : Set (N25.Endgame.FBase K)) = ⊤ := by
  rw [unitLaurentField25C_eq_map, ← modularField_top_map_val25]
  exact (IntermediateField.map_injective (N25.Endgame.FBase K).val).eq_iff

end N25
