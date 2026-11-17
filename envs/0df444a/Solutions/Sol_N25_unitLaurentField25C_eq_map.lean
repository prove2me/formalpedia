-- Prove2me | solution 1 for N25.unitLaurentField25C_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:58:05.760254+00:00
-- url     : https://prove2.me/submissions/8b8b6315-616c-42fb-a767-57897b4bfbc2

import Mathlib
import Theorems.Thm_N25_U25C_eq_mk
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

/-! Coefficient extension of the two modular units and the fields they generate. -/
noncomputable section

namespace N25

/-- The unit-generated Laurent field is the image of the unit-generated modular subfield. -/
theorem _root_.solution (K : Type*) [Field K] :
    unitLaurentField25C K =
      (IntermediateField.adjoin K
        ({U25C K 0, U25C K 0 / U25C K 1} : Set (N25.Endgame.FBase K))).map
          (N25.Endgame.FBase K).val := by
  rw [U25C_eq_mk K 0, U25C_eq_mk K 1, IntermediateField.adjoin_map]
  simp only [Set.image_pair]
  rfl

end N25
