-- Prove2me | solution 1 for N25.U25_geometric_ord_eq_zero_of_not_isCusp
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:00.421197+00:00
-- url     : https://prove2.me/submissions/4d5e7af3-a743-4ce2-8012-3f55249b8552

import Mathlib
import Theorems.Thm_N25_coe_U25C
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_Endgame
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_N25_cusp_constant_place_lift
import Definitions.Def_N25
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_N25_unitSeries25_coeffEmb
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_N25_U25_complex_ord_eq_zero_of_j_mem
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve N25.Endgame

namespace N25

/-- Every geometric noncusp has zero order on the original rational unit. -/
theorem _root_.solution (i : Fin 5) (P : GPlace)
    (hP : ¬ ModularCurve.IsCusp (emb25 j25) P) :
    P.ord (emb25 (U25 i)) = 0 := by
  letI : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  let ι : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  obtain ⟨κ, hκ, hlift⟩ := N25.cusp_constant_place_lift ι.toRingHom
  obtain ⟨W, hmem, hord, _⟩ := hlift P
  have hcomp : ι.toRingHom.comp (algebraMap ℚ Qbar) = algebraMap ℚ ℂ :=
    RingHom.ext_rat _ _
  have hu : (κ (emb25 (U25 i)) : LaurentSeries ℂ) = unitSeries25 ℂ i := by
    rw [hκ, coe_emb25, show (U25 i).1 = unitSeries25 ℚ i from coe_U25C ℚ i]
    change coeffMap ι.toRingHom (coeffMap (algebraMap ℚ Qbar) (unitSeries25 ℚ i)) = _
    rw [coeffMap_coeffMap, hcomp]
    exact unitSeries25_coeffEmb ℂ i
  have hj : (κ (emb25 j25) : LaurentSeries ℂ) = jqModC ℂ := by
    rw [hκ, coe_emb25]
    change coeffMap ι.toRingHom (coeffMap (algebraMap ℚ Qbar) (jqModC ℚ)) = _
    change ((jqModC ℚ).map (algebraMap ℚ Qbar)).map ι.toRingHom = _
    rw [map_jqModC, map_jqModC]
  have hjmem : κ (emb25 j25) ∈ W.toValuationSubring := by
    change emb25 j25 ∈ W.toValuationSubring.comap κ
    rw [hmem]
    exact not_not.mp hP
  rw [← hord (emb25 (U25 i))]
  exact U25_complex_ord_eq_zero_of_j_mem i (κ (emb25 (U25 i))) hu W
    (κ (emb25 j25)) hj hjmem

end N25
