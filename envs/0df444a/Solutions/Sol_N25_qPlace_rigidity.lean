-- Prove2me | solution 1 for N25.qPlace_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:46.131654+00:00
-- url     : https://prove2.me/submissions/f7a11bdf-b0b8-4b00-bc91-bfdc1fcb3c64

import Mathlib
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_N25_laurent_order_rigidity
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

namespace N25

/-- A q-place-preserving automorphism fixing a simple pole is the identity. -/
theorem _root_.solution
    (K : Type*) [Field K] (F : IntermediateField K (LaurentSeries K))
    (h : ∃ j : F, (qSeriesBar K F j).order = -1)
    (τ : F ≃ₐ[K] F) (j : F)
    (hj : (qSeriesBar K F j).order = -1)
    (hτj : τ j = j)
    (hfix : SemilinearAut.ofAlgAut τ • qInftyPlaceBar K F h =
      qInftyPlaceBar K F h) :
    τ = 1 := by
  apply laurent_order_rigidity K F τ j⁻¹ (order_inv_of_order_eq_neg_one hj)
  · rw [map_inv₀,hτj]
  · intro x
    have ho := SemilinearAut.ord_smul (SemilinearAut.ofAlgAut τ) (qInftyPlaceBar K F h) x
    rw [hfix,SemilinearAut.ofAlgAut_smul] at ho
    rw [ord_qInftyPlaceBar,ord_qInftyPlaceBar] at ho
    exact ho

end N25
