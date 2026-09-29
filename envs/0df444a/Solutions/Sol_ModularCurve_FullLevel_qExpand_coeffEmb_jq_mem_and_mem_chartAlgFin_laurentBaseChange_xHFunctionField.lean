-- Prove2me | solution 1 for ModularCurve.FullLevel.qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/8b26fa78-3362-5499-a83e-12331b6f8228

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open ModularCurve

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K] :
    ∃ (hj : ModularCurve.coeffEmb L ModularCurve.jq ∈ K) (hj0 : (⟨_, hj⟩ : ↥K) ≠ 0)
      (hjK : ModularCurve.qExpand L ℓ (ModularCurve.coeffEmb L ModularCurve.jq) ∈ K),
      haveI : Fact ((⟨_, hj⟩ : ↥K) ≠ 0) := ⟨hj0⟩
      (⟨_, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) ⟨_, hj⟩ := by
  classical
  haveI : NeZero ((q * ℓ) ^ 2 * M') := ⟨Nat.mul_ne_zero (pow_ne_zero _ (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)) (NeZero.ne M')⟩
  have hjfull : jq ∈ modularFunctionFieldFull 1 := modularFunctionField_le_full 1 (jq_mem 1)

  have hj1 := ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
    L 1 1 ((q * ℓ) ^ 2 * M') (one_dvd _) (ModularCurve.FullLevel.levelH (q * ℓ) M') jq hjfull
  rw [qExpand_one_apply] at hj1
  have hjℓ := ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
    L 1 ℓ ((q * ℓ) ^ 2 * M') (by rw [one_mul]; exact ⟨ℓ * q ^ 2 * M', by ring⟩) (ModularCurve.FullLevel.levelH (q * ℓ) M') jq hjfull
  have hj : coeffEmb L jq ∈ K := by rw [hK]; exact hj1
  have hjK : qExpand L ℓ (coeffEmb L jq) ∈ K := by rw [hK]; exact hjℓ
  have hne : coeffEmb L jq ≠ 0 := by
    intro h0
    have h1 : (coeffEmb L jq).coeff (-1) = 1 := by rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]
    rw [h0] at h1
    simp at h1
  have hj0 : (⟨_, hj⟩ : ↥K) ≠ 0 := fun h => hne (congrArg Subtype.val h)
  refine ⟨hj, hj0, hjK, ?_⟩

  haveI : Fact ((⟨_, hj⟩ : ↥K) ≠ 0) := ⟨hj0⟩
  obtain ⟨Φ⟩ := ModularCurve.nonempty_modularPolynomialData ℓ
  set j : ↥K := ⟨_, hj⟩ with hjdef
  set j' : ↥K := ⟨_, hjK⟩ with hj'def
  let B : Subalgebra A ↥K := Algebra.adjoin A {j}
  have hjB : j ∈ B := Algebra.self_mem_adjoin_singleton A j

  let φ : Polynomial ℤ →+* ↥B := Polynomial.eval₂RingHom (Int.castRingHom ↥B) ⟨j, hjB⟩
  have hφX : φ Polynomial.X = ⟨j, hjB⟩ := by simp [φ]

  have hcomp : (K.val.toRingHom.comp ((algebraMap ↥B ↥K).comp φ)) = (coeffEmb L).comp evalAtJ := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [show (Polynomial.C a : Polynomial ℤ) = (a : Polynomial ℤ) by rw [← Polynomial.C_eq_intCast, Int.cast_id],
        map_intCast, map_intCast]
    · rw [RingHom.comp_apply, RingHom.comp_apply, hφX, RingHom.comp_apply, evalAtJ_X]
      rfl
  change IsIntegral ↥B j'
  refine ⟨Φ.Φ.map φ, Φ.monic.map φ, ?_⟩
  apply Subtype.ext
  rw [Polynomial.eval₂_map]
  change K.val.toRingHom (Polynomial.eval₂ ((algebraMap ↥B ↥K).comp φ) j' Φ.Φ) = 0
  rw [Polynomial.hom_eval₂, hcomp]
  change Polynomial.eval₂ ((coeffEmb L).comp evalAtJ) (qExpand L ℓ (coeffEmb L jq)) Φ.Φ = 0
  have h0 := congrArg (coeffEmb L) Φ.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂] at h0
  convert h0 using 2
  change qExpand L ℓ (coeffEmb L jq) = coeffEmb L (qExpand ℚ ℓ jq)
  change qExpand L ℓ (coeffMap (algebraMap ℚ L) jq) = coeffMap (algebraMap ℚ L) (qExpand ℚ ℓ jq)
  rw [ModularCurve.coeffMap_qExpand]

end S_ModularCurve_FullLevel_qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField
end P2MW
export P2MW.S_ModularCurve_FullLevel_qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField (solution)
