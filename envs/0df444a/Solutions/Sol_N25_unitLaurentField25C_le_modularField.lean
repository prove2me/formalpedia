-- Prove2me | solution 1 for N25.unitLaurentField25C_le_modularField
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:02.252685+00:00
-- url     : https://prove2.me/submissions/106a2bef-d246-4f6e-acc5-c385058e0ad6

import Mathlib
import Definitions.Def_N25_Units
import Theorems.Thm_N25_unitSeries25_mem
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

/-! Coefficient extension of the two modular units and the fields they generate. -/
noncomputable section

namespace N25

/-- The two plane coordinates remain inside the modular Laurent-series field. -/
theorem _root_.solution (K : Type*) [Field K] :
    unitLaurentField25C K ≤ ModularCurve.qExpFunctionFieldC K N25.Endgame.Γ25 := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · exact unitSeries25_mem K 0
  · have he : z = unitSeries25 K 0 / unitSeries25 K 1 := Set.mem_singleton_iff.mp hz
    subst z
    exact div_mem (unitSeries25_mem K 0) (unitSeries25_mem K 1)

end N25
