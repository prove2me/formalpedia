-- Prove2me | solution 1 for ModularCurve.mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/039758f5-cf34-5f0c-9d83-0ffe48496e71

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_ModularCurve_isCurveOver_x1FunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_x1FunctionFieldBar
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_AlgebraicCurve_regularDiffs_eq_regularDifferentials
import Theorems.Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul_D_nonneg_of_ord_pow_six_mul_pow_four_mul_sub_1728_pow_three_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_one
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul
import Theorems.Thm_AlgebraicCurve_Place_D_ne_zero_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk
import Theorems.Thm_ModularCurve_isIntegral_adjoin_of_isIntegral_adjoin_coeffMap
import Theorems.Thm_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_mul_thetaL_eq_qExpansion_of_finiteIndex
import Theorems.Thm_ModularCurve_one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion_of_gamma_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

open UpperHalfPlane ModularCurve AlgebraicCurve
open scoped MatrixGroups

namespace SolB8bd4cf51

theorem thetaL_coeff' {L : Type*} [Field L] (x : LaurentSeries L) (n : ℤ) :
    (thetaL L x).coeff n = (n : L) * x.coeff n := by
  rw [thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp only [Nat.cast_one, sub_add_cancel, Ring.choose_one_right, zsmul_eq_mul]

theorem qEuler_eq_thetaL {L : Type*} [Field L] (x : LaurentSeries L) :
    qEuler L x = thetaL L x := by
  ext n
  rw [qEuler_coeff, thetaL_coeff']

theorem coeffMap_thetaL {L₁ L₂ : Type*} [Field L₁] [Field L₂] (σ : L₁ →+* L₂)
    (x : LaurentSeries L₁) :
    coeffMap σ (thetaL L₁ x) = thetaL L₂ (coeffMap σ x) := by
  ext n
  simp only [coeffMap_coeff, thetaL_coeff', map_mul, map_intCast]

theorem coeffMap_coeffEmb' {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra ℚ L₁] [Algebra ℚ L₂]
    (σ : L₁ →+* L₂) (x : LaurentSeries ℚ) :
    coeffMap σ (coeffEmb L₁ x) = coeffEmb L₂ x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap,
    Subsingleton.elim (σ.comp (algebraMap ℚ L₁)) (algebraMap ℚ L₂)]

theorem jq_mem_x1FunctionField (M : ℕ) [NeZero M] : jq ∈ x1FunctionField M := by
  rw [← jqModC_rat]
  exact intFormRatiosC_subset ℚ _ (jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 M))

theorem coeffEmb_jq_eq_jqModC (K : Type*) [Field K] [Algebra ℚ K] :
    coeffEmb K jq = jqModC K := by
  rw [jqModC_eq_map_intCast (K := K), ← jqModC_rat, jqModC_eq_map_intCast (K := ℚ)]
  ext n
  simp only [coeffEmb_coeff, HahnSeries.map_coeff, eq_intCast, map_intCast]

theorem one_mem_strictPeriods_Gamma1 (M : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1

theorem Gamma_le_Gamma1 (M : ℕ) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma1 M := by
  intro A hA
  rw [CongruenceSubgroup.Gamma_mem] at hA
  rw [CongruenceSubgroup.Gamma1_mem]
  exact ⟨hA.1, hA.2.2.2, hA.2.2.1⟩

end SolB8bd4cf51

open SolB8bd4cf51 in
theorem solution
    (M : ℕ) [NeZero M] (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ])
    (hω : ModularCurve.coeffMap ι₀ (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M) ω) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f)) :
    ω ∈ AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) := by

  set K := AlgebraicClosure ℚ with hK
  let F : IntermediateField K (LaurentSeries K) := x1FunctionFieldBar M
  let jb : F := ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_x1FunctionField M)⟩
  have hjb : (jb : LaurentSeries K) = jqModC K := coeffEmb_jq_eq_jqModC K

  haveI := essFiniteType_x1FunctionFieldBar M
  haveI := isCurveOver_x1FunctionFieldBar M
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  obtain ⟨hjT, hjfd⟩ :=
    transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      K (CongruenceSubgroup.Gamma1 M) hT jb hjb
  haveI : FiniteDimensional (IntermediateField.adjoin K ({jb} : Set F)) F := hjfd
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({jb} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({jb} : Set F)) F :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField

  obtain ⟨y, hyω, -⟩ :=
    @KaehlerDifferential.exists_unique_smul_D_of_transcendental K _ F _ _ jb hjT hsep ω
  by_cases hy0 : y = 0
  · rw [hyω, hy0, zero_smul]; exact Submodule.zero_mem _

  have hθ : coeffMap ι₀ ((y : LaurentSeries K) * thetaL K (coeffEmb K jq)) =
      ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    rw [← qEuler_eq_thetaL, ← hω, hyω]
    show _ = coeffMap ι₀ (diffQExp F (y • KaehlerDifferential.D K F jb))
    rw [diffQExp_smul_D]

  show ω ∈ regularDifferentials K F
  rw [← regularDiffs_eq_regularDifferentials]
  refine mem_regularDiffs_of_isRegularDiff fun v => ?_
  rw [hyω]
  by_cases hv : v.ord jb < 0
  ·
    have hle := ModularCurve.one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion_of_gamma_le F jb rfl M
      (CongruenceSubgroup.Gamma1 M) (Gamma_le_Gamma1 M) (one_mem_strictPeriods_Gamma1 M) ι₀ f y hy0 hθ v hv
    have hD0 : KaehlerDifferential.D K F jb ≠ 0 := Place.D_ne_zero_of_ord_ne_zero jb v hv.ne
    have h1 : v.ordDiff (y • KaehlerDifferential.D K F jb) =
        v.ord y + v.ordDiff (KaehlerDifferential.D K F jb) :=
      Place.ordDiff_smul jb v hy0 hD0
    have h2 : v.ordDiff (KaehlerDifferential.D K F jb) = v.ord jb - 1 :=
      Place.ordDiff_D_eq_ord_sub_one jb v hv.ne
    have h3 : v.ordDiff (y • KaehlerDifferential.D K F jb) = v.ord y + (v.ord jb - 1) := by
      rw [h1, h2]
    have h4 : (0 : ℤ) ≤ v.ord y + (v.ord jb - 1) := by omega
    exact le_of_le_of_eq h4 h3.symm
  ·
    push Not at hv
    haveI : PerfectField K := PerfectField.ofCharZero
    have h1728 : (1728 : K) ≠ 0 := by norm_num
    refine Place.ordDiff_smul_D_nonneg_of_ord_pow_six_mul_pow_four_mul_sub_1728_pow_three_nonneg
      v jb y jb h1728 (Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg v ?_ hv)

    set u : F := y ^ 6 * jb ^ 4 * (jb - algebraMap K F 1728) ^ 3 with hu
    have hI := ModularCurve.isIntegral_adjoin_coeffEmb_jq_of_mul_thetaL_eq_qExpansion_of_finiteIndex
      (CongruenceSubgroup.Gamma1 M) (one_mem_strictPeriods_Gamma1 M) f
      (coeffMap ι₀ (y : LaurentSeries K)) (by
      rw [← coeffMap_coeffEmb' ι₀, ← coeffMap_thetaL, ← map_mul, hθ])
    have hD : IsIntegral (Algebra.adjoin K ({(jb : LaurentSeries K)} : Set (LaurentSeries K)))
        (u : LaurentSeries K) := by
      refine isIntegral_adjoin_of_isIntegral_adjoin_coeffMap ι₀ _ _ ?_
      have hcoe : ((u : F) : LaurentSeries K) =
          (y : LaurentSeries K) ^ 6 * coeffEmb K jq ^ 4 * (coeffEmb K jq - 1728) ^ 3 := by
        show F.val u = _
        simp only [hu, map_mul, map_pow, map_sub, map_ofNat]
        rfl
      have hj : ((jb : F) : LaurentSeries K) = coeffEmb K jq := rfl
      rw [hcoe, hj, map_mul, map_mul, map_pow, map_pow, map_pow, map_sub, coeffMap_coeffEmb',
        map_ofNat]
      exact hI
    simpa using isIntegral_adjoin_intermediateField_mk F jb.2 u.2 hD

#print axioms solution

end S_ModularCurve_mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion
end P2MW
export P2MW.S_ModularCurve_mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion (solution)
