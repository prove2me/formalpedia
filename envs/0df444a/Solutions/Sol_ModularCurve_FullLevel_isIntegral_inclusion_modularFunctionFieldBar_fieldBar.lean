-- Prove2me | solution 1 for ModularCurve.FullLevel.isIntegral_inclusion_modularFunctionFieldBar_fieldBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/793d7a9b-c49e-5b02-a1f4-dc19867a2a81

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isIntegral_inclusion_modularFunctionFieldBar_fieldBar
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X"
p2m_attr_erase "simp" "ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M') :
    (IntermediateField.inclusion hle).toRingHom.IsIntegral := by
  classical

  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  haveI hfi : (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')).FiniteIndex := ⟨by
    rw [CohCarrier.index_gammaH_eq_index_gamma0_mul_index]
    exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.index_ne_zero_of_finite⟩
  have hT0 : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (q ^ 2 * M') := by
    simp [CongruenceSubgroup.Gamma0_mem, ModularGroup.T]
  have hT : ModularGroup.T ∈ CohCarrier.GammaH (q ^ 2 * M') (levelH q M') := by
    refine CohCarrier.mem_GammaH_iff.mpr ⟨hT0, ?_⟩
    have h1 : CohCarrier.gamma0Units (q ^ 2 * M') ⟨ModularGroup.T, hT0⟩ = 1 :=
      Units.ext (by simp [CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map, ModularGroup.T])
    rw [h1]
    exact one_mem _

  let j0 : ↥(modularFunctionFieldBar M') := ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩
  let y : ↥(fieldBar q M') := IntermediateField.inclusion hle j0
  have hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    show coeffEmb (AlgebraicClosure ℚ) jq = _
    rw [← jqModC_rat]; exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  obtain ⟨-, hfd⟩ :=
    ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      (AlgebraicClosure ℚ) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) hT y hy
  haveI : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set ↥(fieldBar q M'))) ↥(fieldBar q M') := hfd

  intro z
  have hint : IsIntegral ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set ↥(fieldBar q M'))) z :=
    IsIntegral.of_finite _ z
  have hsub : IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set ↥(fieldBar q M')) ≤
      (IntermediateField.inclusion hle).fieldRange := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨j0, rfl⟩
  have hlifts : (minpoly ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set ↥(fieldBar q M'))) z).map
      (algebraMap ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set ↥(fieldBar q M'))) ↥(fieldBar q M')) ∈
      Polynomial.lifts (IntermediateField.inclusion hle).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact hsub ((minpoly (↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set ↥(fieldBar q M')))) z).coeff n).2
  obtain ⟨r, hrmap, -, hrmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts ((minpoly.monic hint).map _)
  refine ⟨r, hrmonic, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hrmap, Polynomial.eval_map_algebraMap]
  exact minpoly.aeval _ z

end S_ModularCurve_FullLevel_isIntegral_inclusion_modularFunctionFieldBar_fieldBar
end P2MW
export P2MW.S_ModularCurve_FullLevel_isIntegral_inclusion_modularFunctionFieldBar_fieldBar (solution)
