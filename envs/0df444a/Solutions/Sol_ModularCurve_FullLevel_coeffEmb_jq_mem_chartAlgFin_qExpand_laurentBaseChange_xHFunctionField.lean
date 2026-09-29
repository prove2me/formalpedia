-- Prove2me | solution 1 for ModularCurve.FullLevel.coeffEmb_jq_mem_chartAlgFin_qExpand_laurentBaseChange_xHFunctionField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/9405d55d-c085-5b75-b0b0-76c517d3b6e7

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_coeffEmb_jq_mem_chartAlgFin_qExpand_laurentBaseChange_xHFunctionField
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.ProjectiveLine.map_mk ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open Polynomial in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K] :
    ∃ (hj : ModularCurve.coeffEmb L ModularCurve.jq ∈ K)
      (hjK : ModularCurve.qExpand L q (ModularCurve.coeffEmb L ModularCurve.jq) ∈ K) (hjK0 : (⟨_, hjK⟩ : ↥K) ≠ 0),
      haveI : Fact ((⟨_, hjK⟩ : ↥K) ≠ 0) := ⟨hjK0⟩
      (⟨_, hj⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) ⟨_, hjK⟩ := by
  classical

  have hK' : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((ℓ * q) ^ 2 * M') (ModularCurve.FullLevel.levelH (ℓ * q) M')) := by
    rw [hK, Nat.mul_comm q ℓ]
  obtain ⟨hj, hj0, hjK, -⟩ :=
    ModularCurve.FullLevel.qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField ℓ M' q L K hK' A
  have hjq0 : ModularCurve.coeffEmb L ModularCurve.jq ≠ 0 := fun h => hj0 (Subtype.ext h)
  have hjK0 : (⟨_, hjK⟩ : ↥K) ≠ 0 := by
    intro h
    have h' : ModularCurve.qExpand L q (ModularCurve.coeffEmb L ModularCurve.jq) = ModularCurve.qExpand L q 0 := by
      rw [map_zero]
      exact congrArg Subtype.val h
    exact hjq0 (ModularCurve.qExpand_injective q h')
  refine ⟨hj, hjK, hjK0, ?_⟩
  haveI hF : Fact ((⟨_, hjK⟩ : ↥K) ≠ 0) := ⟨hjK0⟩
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData q
  have hsymm := ModularCurve.ModularPolynomialData.evalSymm_of_prime q data

  have h0 : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (ModularCurve.qExpand ℚ q ModularCurve.jq)).toRingHom ModularCurve.jq = 0 :=
    (hsymm _ _).trans data.eval_eq_zero

  have h1 : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (ModularCurve.qExpand L q (ModularCurve.coeffEmb L ModularCurve.jq))).toRingHom
      (ModularCurve.coeffEmb L ModularCurve.jq) = 0 := by
    have h := congrArg (ModularCurve.coeffEmb L) h0
    rw [map_zero, Polynomial.hom_eval₂] at h
    convert h using 2
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
      show ModularCurve.qExpand L q (ModularCurve.coeffEmb L ModularCurve.jq) =
        ModularCurve.coeffMap (algebraMap ℚ L) (ModularCurve.qExpand ℚ q ModularCurve.jq)
      rw [ModularCurve.coeffMap_qExpand]
      rfl

  have h2 : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (⟨_, hjK⟩ : ↥K)).toRingHom (⟨_, hj⟩ : ↥K) = 0 := by
    apply (algebraMap ↥K (LaurentSeries L)).injective
    rw [map_zero, Polynomial.hom_eval₂]
    convert h1 using 2 <;> try with_reducible_and_instances rfl
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
      rfl
    all_goals rfl

  show IsIntegral ↥(Algebra.adjoin A ({(⟨_, hjK⟩ : ↥K)} : Set ↥K)) (⟨_, hj⟩ : ↥K)
  let θ : Polynomial ℤ →+* ↥(Algebra.adjoin A ({(⟨_, hjK⟩ : ↥K)} : Set ↥K)) :=
    (Polynomial.aeval (R := ℤ)
      (⟨(⟨_, hjK⟩ : ↥K), Algebra.self_mem_adjoin_singleton A _⟩ : ↥(Algebra.adjoin A ({(⟨_, hjK⟩ : ↥K)} : Set ↥K)))).toRingHom
  refine ⟨data.Φ.map θ, data.monic.map θ, ?_⟩
  rw [Polynomial.eval₂_map]
  convert h2 using 2 <;> try with_reducible_and_instances rfl
  apply Polynomial.ringHom_ext
  · intro a
    simp [θ]
  · simp only [θ, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
    rfl
  all_goals rfl

end S_ModularCurve_FullLevel_coeffEmb_jq_mem_chartAlgFin_qExpand_laurentBaseChange_xHFunctionField
end P2MW
export P2MW.S_ModularCurve_FullLevel_coeffEmb_jq_mem_chartAlgFin_qExpand_laurentBaseChange_xHFunctionField (solution)
