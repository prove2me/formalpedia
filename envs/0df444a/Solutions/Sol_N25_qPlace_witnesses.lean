-- Prove2me | solution 1 for N25.qPlace_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:46.750181+00:00
-- url     : https://prove2.me/submissions/380280a8-1ab8-4cc6-a185-99fb7d7cfc7d

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_order_coeffMap

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

namespace N25

/-- The rational j-series and its coefficient embedding are actual elements
of the two level function fields, each with a simple pole at q=0. -/
theorem _root_.solution :
    let K := AlgebraicClosure ℚ
    let F₀ := xHFunctionField 25 H25
    let F := xHFunctionFieldBar 25 H25
    ∃ j₀ : F₀, ∃ j : F,
      (j₀ : LaurentSeries ℚ) = jqModC ℚ ∧
      (j : LaurentSeries K) = jqModC K ∧
      (j : LaurentSeries K) = coeffEmb K (j₀ : LaurentSeries ℚ) ∧
      (qSeriesBar ℚ F₀ j₀).order = -1 ∧
      (qSeriesBar K F j).order = -1 := by
  dsimp only
  have hj₀ : jqModC ℚ ∈ xHFunctionField 25 H25 :=
    intFormRatiosC_subset ℚ (CohCarrier.GammaH 25 H25)
      (jqModC_mem_intFormRatiosC ℚ (CohCarrier.GammaH 25 H25))
  let j₀ : xHFunctionField 25 H25 := ⟨jqModC ℚ,hj₀⟩
  let j : xHFunctionFieldBar 25 H25 :=
    ⟨coeffEmb (AlgebraicClosure ℚ) (j₀ : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) j₀.2⟩
  refine ⟨j₀,j,rfl,?_,rfl,?_,?_⟩
  · change (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)
    exact map_jqModC _
  · change (jqModC ℚ).order = -1
    rw [jqModC_rat]
    exact order_jq
  · change (coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ)).order = -1
    rw [order_coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective, jqModC_rat]
    exact order_jq

end N25
