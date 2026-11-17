-- Prove2me | solution 1 for N25.modularField_top_map_val25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:40.439842+00:00
-- url     : https://prove2.me/submissions/15deb130-523b-4043-b335-4767eb3bca28

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

/-! Coefficient extension of the two modular units and the fields they generate. -/
noncomputable section

namespace N25

/-- The inclusion of the whole modular field has its literal Laurent-series field as image. -/
theorem _root_.solution (K : Type*) [Field K] :
    (⊤ : IntermediateField K (N25.Endgame.FBase K)).map
      (N25.Endgame.FBase K).val =
        ModularCurve.qExpFunctionFieldC K N25.Endgame.Γ25 := by
  ext x
  change (∃ y : N25.Endgame.FBase K, y ∈ (⊤ : IntermediateField K _) ∧
    (y : LaurentSeries K) = x) ↔ x ∈ ModularCurve.qExpFunctionFieldC K N25.Endgame.Γ25
  constructor
  · rintro ⟨y, _, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩

end N25
