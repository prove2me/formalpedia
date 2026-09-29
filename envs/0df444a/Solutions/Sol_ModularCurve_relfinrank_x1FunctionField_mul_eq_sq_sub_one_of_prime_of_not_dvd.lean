-- Prove2me | solution 1 for ModularCurve.relfinrank_x1FunctionField_mul_eq_sq_sub_one_of_prime_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/69dc74e6-52ab-532e-86bf-1846ecfa41e0

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_CongruenceSubgroup_two_mul_index_gamma1_sup_zpowers_neg_one
import Theorems.Thm_CongruenceSubgroup_index_gamma1_mul_eq_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma1_eq_index
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_relfinrank_x1FunctionField_mul_eq_sq_sub_one_of_prime_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec"
p2m_attr_erase "simp" "GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open ModularCurve CongruenceSubgroup
open scoped MatrixGroups

namespace DegQ

theorem jq_mem (Γ : Subgroup SL(2, ℤ)) : jq ∈ qExpFunctionFieldC ℚ Γ := by
  have h := jqModC_mem_intFormRatiosC ℚ Γ
  rw [jqModC_rat] at h
  exact intFormRatiosC_subset ℚ Γ h

theorem relfinrank_adjoin_jq (M : ℕ) [NeZero M] :
    IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        (qExpFunctionFieldC ℚ (Gamma1 M)) =
      (Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  classical
  set K := AlgebraicClosure ℚ
  set F₀ := qExpFunctionFieldC ℚ (Gamma1 M) with hF₀

  rw [← relfinrank_laurentBaseChange K F₀ jq (jq_mem (Gamma1 M)) transcendental_jq]

  have hymem : coeffEmb K jq ∈ laurentBaseChange K F₀ := coeffEmb_mem_laurentBaseChange K (jq_mem (Gamma1 M))
  set y : ↥(laurentBaseChange K F₀) := ⟨coeffEmb K jq, hymem⟩ with hy_def
  have hy : (y : LaurentSeries K) = jqModC K := by
    show (jqModC ℚ).map (algebraMap ℚ K) = jqModC K
    exact map_jqModC (algebraMap ℚ K)

  have hA : IntermediateField.adjoin K ({coeffEmb K jq} : Set (LaurentSeries K)) =
      (IntermediateField.adjoin K ({y} : Set ↥(laurentBaseChange K F₀))).map (laurentBaseChange K F₀).val := by
    have h := IntermediateField.adjoin_map (F := K) ({y} : Set ↥(laurentBaseChange K F₀)) (laurentBaseChange K F₀).val
    rw [Set.image_singleton] at h
    exact h.symm
  have hcomap : (IntermediateField.adjoin K ({coeffEmb K jq} : Set (LaurentSeries K))).comap (laurentBaseChange K F₀).val =
      IntermediateField.adjoin K ({y} : Set ↥(laurentBaseChange K F₀)) := by
    rw [hA, IntermediateField.comap_map]
  have h1 := IntermediateField.finrank_comap (IntermediateField.adjoin K ({coeffEmb K jq} : Set (LaurentSeries K)))
    (laurentBaseChange K F₀).val
  rw [IntermediateField.fieldRange_val, hcomap] at h1
  rw [← h1]
  exact finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma1_eq_index K M y hy

end DegQ

open DegQ in
theorem solution
    (N ℓ : ℕ) [NeZero N] (hN : 3 ≤ N) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    IntermediateField.relfinrank (ModularCurve.x1FunctionField N) (ModularCurve.x1FunctionField (N * ℓ)) = ℓ ^ 2 - 1 := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : NeZero (N * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne N) hℓ.ne_zero⟩

  have h01 : IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) ≤ qExpFunctionFieldC ℚ (Gamma1 N) :=
    IntermediateField.adjoin_simple_le_iff.mpr (jq_mem (Gamma1 N))
  have h12 : qExpFunctionFieldC ℚ (Gamma1 N) ≤ qExpFunctionFieldC ℚ (Gamma1 (N * ℓ)) :=
    x1FunctionFieldC_le_of_dvd ℚ (dvd_mul_right N ℓ)
  have htower := IntermediateField.relfinrank_mul_relfinrank h01 h12
  rw [relfinrank_adjoin_jq N, relfinrank_adjoin_jq (N * ℓ)] at htower

  have hNℓ : 3 ≤ N * ℓ := le_trans hN (Nat.le_mul_of_pos_right N hℓ.pos)
  have h2N := two_mul_index_gamma1_sup_zpowers_neg_one N hN
  have h2Nℓ := two_mul_index_gamma1_sup_zpowers_neg_one (N * ℓ) hNℓ
  have hidx := index_gamma1_mul_eq_of_prime_of_not_dvd N ℓ hℓN
  have hpos : 0 < (Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
    haveI : (Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).FiniteIndex :=
      Subgroup.finiteIndex_of_le (le_sup_left : Gamma1 N ≤ _)
    exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

  have hkey : (Gamma1 (N * ℓ) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      (ℓ ^ 2 - 1) * (Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
    have : 2 * (Gamma1 (N * ℓ) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
        2 * ((ℓ ^ 2 - 1) * (Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index) := by
      calc 2 * (Gamma1 (N * ℓ) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index
          = (ℓ ^ 2 - 1) * (2 * (Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index) := by rw [h2Nℓ, hidx, h2N]
        _ = 2 * ((ℓ ^ 2 - 1) * (Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index) := by ring
    omega
  rw [hkey] at htower

  show IntermediateField.relfinrank (qExpFunctionFieldC ℚ (Gamma1 N)) (qExpFunctionFieldC ℚ (Gamma1 (N * ℓ))) = ℓ ^ 2 - 1
  have := Nat.eq_of_mul_eq_mul_left hpos (htower.trans (mul_comm _ _))
  exact this

end S_ModularCurve_relfinrank_x1FunctionField_mul_eq_sq_sub_one_of_prime_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_relfinrank_x1FunctionField_mul_eq_sq_sub_one_of_prime_of_not_dvd (solution)
