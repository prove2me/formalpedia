-- Prove2me | solution 1 for ModularCurve.qExpansionDiffAlong_traceAlong_pullbackAlong_eq_heckeT
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/35d03b43-e95b-541c-abfd-07620e6e01d3

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_LaurentSeries_HeckeV
import Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC
import Theorems.Thm_AlgebraicCurve_Differential_traceAlong_eq_traceDiff
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpansionDiffAlong_traceAlong_pullbackAlong_eq_heckeT
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open ModularCurve AlgebraicCurve

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hpNq : ¬ p ∣ N * q) (hqN : ¬ q ∣ N)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) q)
    (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) :
    qExpansionDiffAlong (modularFunctionFieldC K N).val
        (Differential.traceAlong (heckeAlphaC K N q) (Differential.pullbackAlong (heckeBetaC K N q) ω))
      = LaurentSeries.heckeT K q (Fact.out : q.Prime).pos 2
          (qExpansionDiffAlong (modularFunctionFieldC K N).val ω) := by
  have hp : p.Prime := Fact.out
  have hN : (N : K) ≠ 0 := fun h0 =>
    hpNq (dvd_mul_of_dvd_left ((CharP.cast_eq_zero_iff K p N).mp h0) q)
  have hsep : SeparableAlong K (heckeAlphaC K N q) := (separableAlong_heckeAlphaC_heckeBetaC K N q hpNq).1
  rw [Differential.traceAlong_eq_traceDiff _ _ _ (heckeAlphaC K N q) hsep]
  ext n
  rw [LaurentSeries.coeff_heckeT, show (2 - 1 : ℕ) = 1 from rfl, pow_one, mul_ite, mul_zero]
  exact coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC K N q hN hqN ζ hζ ω n

end S_ModularCurve_qExpansionDiffAlong_traceAlong_pullbackAlong_eq_heckeT
end P2MW
export P2MW.S_ModularCurve_qExpansionDiffAlong_traceAlong_pullbackAlong_eq_heckeT (solution)
