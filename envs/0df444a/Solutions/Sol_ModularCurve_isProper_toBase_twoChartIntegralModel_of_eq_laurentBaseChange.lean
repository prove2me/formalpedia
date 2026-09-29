-- Prove2me | solution 1 for ModularCurve.isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1b60ee72-9f15-5896-ae2f-3a03773a5c68

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one"

set_option autoImplicit false

open AlgebraicGeometry

theorem solution
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [UniqueFactorizationMonoid A]
    [Algebra A L] [IsFractionRing A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    IsProper (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) := by
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange Γ hT L K hK j hj
  haveI := hFD
  haveI : PerfectField ↥(IntermediateField.adjoin L ({j} : Set ↥K)) := PerfectField.ofCharZero
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨hfin, hinf⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep
  haveI := hfin
  haveI := hinf
  exact AlgebraicCurve.TwoChartIntegralModel.isProper_toBase A (↥K) j

end S_ModularCurve_isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange (solution)
