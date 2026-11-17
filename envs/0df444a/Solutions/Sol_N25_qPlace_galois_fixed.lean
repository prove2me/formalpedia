-- Prove2me | solution 1 for N25.qPlace_galois_fixed
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:45.511202+00:00
-- url     : https://prove2.me/submissions/aa55e282-57a6-4bab-b58f-6619ac1bdc55

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_order_coeffMap

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

open scoped Pointwise

namespace N25

/-- Coefficientwise arithmetic Galois preserves the actual q-adic place. -/
theorem _root_.solution
    (h : ∃ j : xHFunctionFieldBar 25 H25,
      (qSeriesBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) j).order = -1)
    (σ : Gal) :
    arithmeticGalois (xHFunctionField 25 H25) σ •
      qInftyPlaceBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) h =
      qInftyPlaceBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) h := by
  let g := arithmeticGalois (xHFunctionField 25 H25) σ
  have ho (x : xHFunctionFieldBar 25 H25) :
      (qSeriesBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) (g • x)).order =
      (qSeriesBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) x).order := by
    change (coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)
      (x : LaurentSeries (AlgebraicClosure ℚ))).order =
      (x : LaurentSeries (AlgebraicClosure ℚ)).order
    exact order_coeffMap σ.injective _
  apply Place.toValuationSubring_injective
  change g • qIntegersBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) =
    qIntegersBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25)
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  change (0 ≤ (qSeriesBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) (g⁻¹ • x)).order) ↔
    0 ≤ (qSeriesBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) x).order
  have hi : (qSeriesBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) (g⁻¹ • x)).order =
      (qSeriesBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) x).order := by
    simpa only [smul_inv_smul] using (ho (g⁻¹ • x)).symm
  rw [hi]

end N25
