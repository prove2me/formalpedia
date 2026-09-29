-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.coeffEmb_jq_mem_and_qExpand_mem_and_mem_chartAlgFin_xHFunctionField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/b043507e-08e7-5d56-9afe-8d584161b8b2

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_coeffEmb_jq_mem_and_qExpand_mem_and_mem_chartAlgFin_xHFunctionField
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.ProjectiveLine.map_mk ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K] :
    ∃ (hj : ModularCurve.coeffEmb L ModularCurve.jq ∈ K) (hj0 : (⟨_, hj⟩ : ↥K) ≠ 0)
      (hjK : ModularCurve.qExpand L q (ModularCurve.coeffEmb L ModularCurve.jq) ∈ K) (hjK0 : (⟨_, hjK⟩ : ↥K) ≠ 0),
      (haveI : Fact ((⟨_, hjK⟩ : ↥K) ≠ 0) := ⟨hjK0⟩
       (⟨_, hj⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) ⟨_, hjK⟩) ∧
      (haveI : Fact ((⟨_, hj⟩ : ↥K) ≠ 0) := ⟨hj0⟩
       (⟨_, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) ⟨_, hj⟩) := by
  classical
  haveI : NeZero (q ^ 2 * M') := ⟨Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  have hjfull : ModularCurve.jq ∈ ModularCurve.modularFunctionFieldFull 1 := ModularCurve.modularFunctionField_le_full 1 (ModularCurve.jq_mem 1)

  have hj1 := ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
    L 1 1 (q ^ 2 * M') (one_dvd _) H₁ ModularCurve.jq hjfull
  rw [ModularCurve.qExpand_one_apply] at hj1
  have hjq := ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
    L 1 q (q ^ 2 * M') (by rw [one_mul]; exact ⟨q * M', by ring⟩) H₁ ModularCurve.jq hjfull
  have hj : ModularCurve.coeffEmb L ModularCurve.jq ∈ K := by rw [hK]; exact hj1
  have hjK : ModularCurve.qExpand L q (ModularCurve.coeffEmb L ModularCurve.jq) ∈ K := by rw [hK]; exact hjq
  have hne : ModularCurve.coeffEmb L ModularCurve.jq ≠ 0 := by
    intro h0
    have h1 : (ModularCurve.coeffEmb L ModularCurve.jq).coeff (-1) = 1 := by
      rw [ModularCurve.coeffEmb_coeff, ModularCurve.coeff_jq_neg_one, map_one]
    rw [h0] at h1
    simp at h1
  have hj0 : (⟨_, hj⟩ : ↥K) ≠ 0 := fun h => hne (congrArg Subtype.val h)
  have hjK0 : (⟨_, hjK⟩ : ↥K) ≠ 0 := by
    intro h
    have h' : ModularCurve.qExpand L q (ModularCurve.coeffEmb L ModularCurve.jq) = ModularCurve.qExpand L q 0 := by
      rw [map_zero]
      exact congrArg Subtype.val h
    exact hne (ModularCurve.qExpand_injective q h')
  refine ⟨hj, hj0, hjK, hjK0, ?_, ?_⟩
  ·
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
      convert h1 using 2 <;> try rfl
      apply Polynomial.ringHom_ext
      · intro a
        simp
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
        rfl
    show IsIntegral ↥(Algebra.adjoin A ({(⟨_, hjK⟩ : ↥K)} : Set ↥K)) (⟨_, hj⟩ : ↥K)
    let θ : Polynomial ℤ →+* ↥(Algebra.adjoin A ({(⟨_, hjK⟩ : ↥K)} : Set ↥K)) :=
      (Polynomial.aeval (R := ℤ)
        (⟨(⟨_, hjK⟩ : ↥K), Algebra.self_mem_adjoin_singleton A _⟩ : ↥(Algebra.adjoin A ({(⟨_, hjK⟩ : ↥K)} : Set ↥K)))).toRingHom
    refine ⟨data.Φ.map θ, data.monic.map θ, ?_⟩
    rw [Polynomial.eval₂_map]
    convert h2 using 2 <;> try rfl
    apply Polynomial.ringHom_ext
    · intro a
      simp [θ]
    · simp only [θ, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
      rfl
  ·
    haveI : Fact ((⟨_, hj⟩ : ↥K) ≠ 0) := ⟨hj0⟩
    obtain ⟨Φ⟩ := ModularCurve.nonempty_modularPolynomialData q
    set j : ↥K := ⟨_, hj⟩ with hjdef
    set j' : ↥K := ⟨_, hjK⟩ with hj'def
    let B : Subalgebra A ↥K := Algebra.adjoin A {j}
    have hjB : j ∈ B := Algebra.self_mem_adjoin_singleton A j
    let φ : Polynomial ℤ →+* ↥B := Polynomial.eval₂RingHom (Int.castRingHom ↥B) ⟨j, hjB⟩
    have hφX : φ Polynomial.X = ⟨j, hjB⟩ := by simp [φ]
    have hcomp : (K.val.toRingHom.comp ((algebraMap ↥B ↥K).comp φ)) = (ModularCurve.coeffEmb L).comp ModularCurve.evalAtJ := by
      apply Polynomial.ringHom_ext
      · intro a
        rw [show (Polynomial.C a : Polynomial ℤ) = (a : Polynomial ℤ) by rw [← Polynomial.C_eq_intCast, Int.cast_id],
          map_intCast, map_intCast]
      · rw [RingHom.comp_apply, RingHom.comp_apply, hφX, RingHom.comp_apply, ModularCurve.evalAtJ_X]
        rfl
    change IsIntegral ↥B j'
    refine ⟨Φ.Φ.map φ, Φ.monic.map φ, ?_⟩
    apply Subtype.ext
    rw [Polynomial.eval₂_map]
    change K.val.toRingHom (Polynomial.eval₂ ((algebraMap ↥B ↥K).comp φ) j' Φ.Φ) = 0
    rw [Polynomial.hom_eval₂, hcomp]
    change Polynomial.eval₂ ((ModularCurve.coeffEmb L).comp ModularCurve.evalAtJ) (ModularCurve.qExpand L q (ModularCurve.coeffEmb L ModularCurve.jq)) Φ.Φ = 0
    have h0 := congrArg (ModularCurve.coeffEmb L) Φ.eval_eq_zero
    rw [map_zero, Polynomial.hom_eval₂] at h0
    convert h0 using 2
    change ModularCurve.qExpand L q (ModularCurve.coeffEmb L ModularCurve.jq) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ q ModularCurve.jq)
    change ModularCurve.qExpand L q (ModularCurve.coeffMap (algebraMap ℚ L) ModularCurve.jq) = ModularCurve.coeffMap (algebraMap ℚ L) (ModularCurve.qExpand ℚ q ModularCurve.jq)
    rw [ModularCurve.coeffMap_qExpand]

end S_ModularCurve_FullLevel_Diamond_coeffEmb_jq_mem_and_qExpand_mem_and_mem_chartAlgFin_xHFunctionField
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_coeffEmb_jq_mem_and_qExpand_mem_and_mem_chartAlgFin_xHFunctionField (solution)
