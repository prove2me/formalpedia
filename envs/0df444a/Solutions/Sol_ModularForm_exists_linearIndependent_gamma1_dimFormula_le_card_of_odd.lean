-- Prove2me | solution 1 for ModularForm.exists_linearIndependent_gamma1_dimFormula_le_card_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/32af4b01-b7fd-5b8e-81f4-0fc04c36576c

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma1_eq_index
import Theorems.Thm_ModularCurve_ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1
import Theorems.Thm_ModularCurve_twelve_mul_genusFF_laurentBaseChange_gamma1_add_six_mul_natCard_doubleCoset_eq_index_add_twelve_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_qExpFunctionFieldC_gamma1
import Theorems.Thm_ModularCurve_finiteDimensional_riemannRochSpace_laurentBaseChange_qExpFunctionFieldC_gamma1
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_AlgebraicCurve_exists_divisor_forall_eq_weightFloor
import Theorems.Thm_ModularCurve_isIntegral_and_isIntegral_of_mem_riemannRochSpace_weightFloor
import Theorems.Thm_ModularCurve_exists_modularForm_gamma1_qExpansion_eq_mul_thetaL_pow_of_isIntegral
import Theorems.Thm_AlgebraicCurve_six_mul_degree_eq_mul_finrank_of_forall_eq_weightFloor_of_ord_eq_three_two
import Theorems.Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
import Theorems.Thm_ModularForm_exists_gamma1_weightOne_ne_zero_and_mul_thetaL_eq_qExpansion_sq
import Theorems.Thm_ModularCurve_exists_divisor_two_mul_eq_ord_add_weightFloor_one_laurentBaseChange_gamma1
import Theorems.Thm_ModularCurve_exists_modularForm_gamma1_qExpansion_eq_mul_pow_of_qExpansion_eq_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_linearIndependent_gamma1_dimFormula_le_card_of_odd
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateLaurent"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg"
p2m_attr_erase "simp" "WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.ProjectiveLine.map_mk ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "ModularCurve CongruenceSubgroup AlgebraicCurve~genus UpperHalfPlane"
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace DimLBOddE96

theorem finite_doubleCoset_quotient {G : Type*} [Group G] (H K : Subgroup G) [H.FiniteIndex] :
    Finite (DoubleCoset.Quotient (H : Set G) (K : Set G)) := by
  classical
  haveI : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  refine Finite.of_surjective (fun q : Quotient (QuotientGroup.rightRel H) => Quotient.liftOn' q (fun g => DoubleCoset.mk H K g) ?_) ?_
  · intro a b hab
    rw [QuotientGroup.rightRel_apply] at hab
    apply DoubleCoset.mk_eq_of_doubleCoset_eq
    refine DoubleCoset.doubleCoset_eq_of_mem ?_
    refine DoubleCoset.mem_doubleCoset.mpr ⟨a * b⁻¹, by simpa using H.inv_mem hab, 1, K.one_mem, by group⟩
  · intro q
    induction q using Quotient.inductionOn' with
    | h g => exact ⟨Quotient.mk'' g, rfl⟩

theorem exists_coe_eq_jqModC (M : ℕ) [NeZero M] :
    ∃ y : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))),
      (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ := by
  have hmem : ModularCurve.jq ∈ ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M) := by
    rw [← ModularCurve.jqModC_rat]
    exact ModularCurve.intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
  refine ⟨⟨ModularCurve.coeffEmb ℂ ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange ℂ hmem⟩, ?_⟩
  show ModularCurve.coeffEmb ℂ ModularCurve.jq = _
  rw [← ModularCurve.jqModC_rat]
  exact ModularCurve.map_jqModC (algebraMap ℚ ℂ)

variable (M : ℕ) [NeZero M]

local notation "Γ₁ℝ" => ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_gamma1 : (1 : ℝ) ∈ (Γ₁ℝ).strictPeriods := by
  simp

theorem analyticAt_cuspFunction {k : ℤ} (g : ModularForm Γ₁ℝ k) : AnalyticAt ℂ (cuspFunction 1 (⇑g : ℍ → ℂ)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero g one_pos (one_mem_strictPeriods_gamma1 M)

theorem qExpansion_sum_smul {k : ℤ} {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → ModularForm Γ₁ℝ k) :
    qExpansion 1 (⇑(∑ i ∈ s, c i • f i) : ℍ → ℂ) = ∑ i ∈ s, c i • qExpansion 1 (⇑(f i) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert a s ha ih =>
    have hcoe : (⇑(c a • f a + ∑ i ∈ s, c i • f i) : ℍ → ℂ) = (⇑(c a • f a) : ℍ → ℂ) + (⇑(∑ i ∈ s, c i • f i) : ℍ → ℂ) := rfl
    have hcoe2 : (⇑(c a • f a) : ℍ → ℂ) = (c a) • (⇑(f a) : ℍ → ℂ) := rfl
    have h1 : qExpansion 1 (⇑(c a • f a) : ℍ → ℂ) = c a • qExpansion 1 (⇑(f a) : ℍ → ℂ) := by
      rw [hcoe2]; exact qExpansion_smul (analyticAt_cuspFunction M (f a)) (c a)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hcoe,
      qExpansion_add (analyticAt_cuspFunction M (c a • f a)) (analyticAt_cuspFunction M (∑ i ∈ s, c i • f i)), ih, h1]

theorem eq_zero_of_qExpansion_eq_zero {k : ℤ} (g : ModularForm Γ₁ℝ k) (h : qExpansion 1 (⇑g : ℍ → ℂ) = 0) : g = 0 := by
  apply DFunLike.ext
  intro τ
  have hs := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex g (one_mem_strictPeriods_gamma1 M))
    g.holo' (ModularFormClass.bdd_at_infty g) τ
  rw [h] at hs
  simpa using hs.tsum_eq.symm

theorem ofPowerSeries_smul (a : ℂ) (p : PowerSeries ℂ) :
    HahnSeries.ofPowerSeries ℤ ℂ (a • p) = algebraMap ℂ (LaurentSeries ℂ) a * HahnSeries.ofPowerSeries ℤ ℂ p := by
  rw [PowerSeries.smul_eq_C_mul, map_mul]
  congr 1 <;> first
    | rfl
    | (rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply]; simp)
    | simp [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply]

end DimLBOddE96

end

open DimLBOddE96 in
theorem solution
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (k : ℕ) (hk : 3 ≤ k) (hko : Odd k) :
    ∃ (d : ℕ) (f : Fin d → ModularForm (Gamma1 M) (k : ℤ)), LinearIndependent ℂ f ∧
      (k - 1) * (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index +
          6 * Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
            ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)))
        ≤ 12 * d := by
  classical
  have hk1 : 1 ≤ k := by omega

  haveI hfi' : (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).FiniteIndex :=
    Subgroup.finiteIndex_of_le le_sup_left

  obtain ⟨y, hy⟩ := exists_coe_eq_jqModC M
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  obtain ⟨htr, hfin⟩ :=
    ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      ℂ (CongruenceSubgroup.Gamma1 M) hT y hy
  haveI := hfin
  have hfull := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma1_eq_index ℂ M y hy
  haveI hsep : Algebra.IsSeparable
      ↥(IntermediateField.adjoin ℂ ({y} : Set ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))))
      ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) := inferInstance
  obtain ⟨h0, h1728⟩ :=
    ModularCurve.ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1 ℂ M (by omega) y hy
  haveI : IsCurveOver ℂ ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) :=
    ModularCurve.isCurveOver_laurentBaseChange_qExpFunctionFieldC_gamma1 ℂ M
  have hg := ModularCurve.twelve_mul_genusFF_laurentBaseChange_gamma1_add_six_mul_natCard_doubleCoset_eq_index_add_twelve_of_isAlgClosed ℂ M hM

  obtain ⟨w, v0, hw0, hv0mem, hv0⟩ :=
    ModularForm.exists_gamma1_weightOne_ne_zero_and_mul_thetaL_eq_qExpansion_sq M hM
  let v : ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) := ⟨v0, hv0mem⟩
  obtain ⟨Dw, hDw⟩ :=
    ModularCurve.exists_divisor_two_mul_eq_ord_add_weightFloor_one_laurentBaseChange_gamma1 M hM y hy w hw0 v hv0

  obtain ⟨Dk, hDk⟩ := AlgebraicCurve.exists_divisor_forall_eq_weightFloor ℂ y k
  have hdegk := AlgebraicCurve.six_mul_degree_eq_mul_finrank_of_forall_eq_weightFloor_of_ord_eq_three_two
    ℂ y htr hfin hsep h0 h1728 k Dk hDk
  rw [hfull] at hdegk

  set W : LaurentSeries ℂ := HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 w) with hWdef
  have hW : W ≠ 0 := by
    intro h0
    apply hw0
    apply eq_zero_of_qExpansion_eq_zero M
    exact HahnSeries.ofPowerSeries_injective (by rw [← hWdef, h0, map_zero])
  have hvne : v ≠ 0 := by
    intro h0
    have : (v : LaurentSeries ℂ) = 0 := by rw [h0]; rfl
    apply pow_ne_zero 2 hW
    rw [← hv0]
    show v0 * _ = 0
    rw [show v0 = (v : LaurentSeries ℂ) from rfl, this, zero_mul]

  obtain ⟨Pv, hPv, hdegPv⟩ := AlgebraicCurve.HasPrincipalDivisors.exists_divisor (K := ℂ) v hvne
  obtain ⟨D1, hD1⟩ := AlgebraicCurve.exists_divisor_forall_eq_weightFloor ℂ y 1
  have hdeg1 := AlgebraicCurve.six_mul_degree_eq_mul_finrank_of_forall_eq_weightFloor_of_ord_eq_three_two
    ℂ y htr hfin hsep h0 h1728 1 D1 hD1
  rw [hfull] at hdeg1
  have h2Dw : (2 : ℕ) • Dw = Pv + D1 := by
    ext P
    rw [Finsupp.smul_apply, Finsupp.add_apply, nsmul_eq_mul, hPv P, hD1 P]
    push_cast
    rw [hDw P]
    ring_nf
  have hdegDw : 2 * Dw.degree = D1.degree := by
    have := congrArg AlgebraicCurve.Divisor.degree h2Dw
    rw [map_nsmul, map_add, hdegPv, zero_add, nsmul_eq_mul] at this
    exact_mod_cast this
  have hdegw : 12 * (k • Dw).degree =
      (k : ℤ) * (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
    rw [map_nsmul, nsmul_eq_mul]
    have : (12 : ℤ) * Dw.degree = (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
      have e := hdeg1
      push_cast at e
      linarith [hdegDw]
    calc (12 : ℤ) * ((k : ℤ) * Dw.degree) = k * (12 * Dw.degree) := by ring
      _ = _ := by rw [this]

  set μ : ℕ := (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index with hμdef
  set cc : ℕ := Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
      ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) with hccdef
  set gg : ℕ := genusFF ℂ ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) with hggdef
  have hgZ : (12 : ℤ) * gg + 6 * cc = μ + 12 := by exact_mod_cast hg
  have hcpos : 1 ≤ cc := by
    haveI := finite_doubleCoset_quotient (CongruenceSubgroup.Gamma1 M)
      (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ))
    haveI : Nonempty (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
      ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) :=
      ⟨DoubleCoset.mk _ _ 1⟩
    exact Nat.card_pos
  have hcZ : (1 : ℤ) ≤ cc := by exact_mod_cast hcpos
  have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hμZ : (0 : ℤ) ≤ μ := by exact_mod_cast Nat.zero_le μ
  have hRRhyp : 2 * (gg : ℤ) - 1 ≤ (k • Dw).degree := by nlinarith [hdegw, hgZ, hμZ, hkZ, hcZ]
  have hRR := AlgebraicCurve.ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable ℂ y htr hfin hsep (k • Dw) hRRhyp
  haveI := ModularCurve.finiteDimensional_riemannRochSpace_laurentBaseChange_qExpFunctionFieldC_gamma1 ℂ M (k • Dw)
  set d : ℕ := Module.finrank ℂ ↥(riemannRochSpace (k • Dw)) with hddef
  have hell : (ell (k • Dw) : ℤ) = d := rfl
  let b := Module.finBasis ℂ ↥(riemannRochSpace (k • Dw))

  have hEk : ∀ P : AlgebraicCurve.Place ℂ ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))),
      (k : ℤ) * D1 P = Dk P := by
    intro P
    rw [hD1 P, hDk P]
    push_cast
    have t1 : (k : ℤ) * (if 0 < P.ord y then (2 * 1 * P.ord y) / 3 else 0) =
        (if 0 < P.ord y then (2 * (k : ℤ) * P.ord y) / 3 else 0) := by
      split_ifs with hc
      · rw [h0 P hc]; omega
      · simp
    have t2 : (k : ℤ) * (if 0 < P.ord (y - 1728) then (1 * P.ord (y - 1728)) / 2 else 0) =
        (if 0 < P.ord (y - 1728) then ((k : ℤ) * P.ord (y - 1728)) / 2 else 0) := by
      split_ifs with hc
      · rw [h1728 P hc]; omega
      · simp
    have t3 : (k : ℤ) * (if P.ord y < 0 then 1 * P.ord y else 0) = (if P.ord y < 0 then (k : ℤ) * P.ord y else 0) := by
      split_ifs <;> simp
    rw [← t1, ← t2, ← t3]
    ring
  have hmemk : ∀ G : ↥(riemannRochSpace (k • Dw)),
      ((G : ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) ^ 2 * v ^ k)
        ∈ riemannRochSpace Dk := by
    intro G
    rw [AlgebraicCurve.mem_riemannRochSpace_iff]
    intro P
    have hG := (AlgebraicCurve.mem_riemannRochSpace_iff.mp G.2) P
    by_cases hG0 : (G : ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) = 0
    · left; rw [hG0]; ring
    · right
      rcases hG with hG | hG
      · exact absurd hG hG0
      rw [P.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hvne), ← zpow_natCast, P.ord_zpow, ← zpow_natCast,
        P.ord_zpow]
      rw [Finsupp.smul_apply, nsmul_eq_mul] at hG
      have e2 : 2 * Dw P = P.ord v + D1 P := by
        have := congrArg (fun D : AlgebraicCurve.Divisor ℂ _ => D P) h2Dw
        simp only [Finsupp.smul_apply, Finsupp.add_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
        rw [hPv P] at this
        exact_mod_cast this
      have e3 := hEk P
      push_cast
      nlinarith [hG, e2, e3]
  have hshape : ∀ i : Fin d, _ := fun i =>
    ModularCurve.isIntegral_and_isIntegral_of_mem_riemannRochSpace_weightFloor ℂ
      (laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) y hy k Dk hDk _ (hmemk (b i))
  choose F₂ hF₂ using fun i : Fin d =>
    ModularCurve.exists_modularForm_gamma1_qExpansion_eq_mul_thetaL_pow_of_isIntegral M k hk1
      ((((b i : ↥(riemannRochSpace (k • Dw))) :
          ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) ^ 2 * v ^ k :
          ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) : LaurentSeries ℂ)
      (((b i : ↥(riemannRochSpace (k • Dw))) :
          ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) ^ 2 * v ^ k).2
      (hshape i).1 (hshape i).2

  have hsq : ∀ i : Fin d,
      HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (F₂ i)) =
        ((((b i : ↥(riemannRochSpace (k • Dw))) :
            ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) : LaurentSeries ℂ) *
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 w) ^ k) ^ 2 := by
    intro i
    rw [hF₂ i]
    push_cast
    rw [show ((v : ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) : LaurentSeries ℂ) = v0
      from rfl, ← hWdef, mul_assoc, ← mul_pow, hv0]
    ring
  choose f hf using fun i : Fin d =>
    ModularCurve.exists_modularForm_gamma1_qExpansion_eq_mul_pow_of_qExpansion_eq_sq M k w
      ((((b i : ↥(riemannRochSpace (k • Dw))) :
          ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) : LaurentSeries ℂ))
      ((b i : ↥(riemannRochSpace (k • Dw))) :
          ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))).2
      (F₂ i) (hsq i)
  refine ⟨d, f, ?_, ?_⟩
  ·
    rw [Fintype.linearIndependent_iff]
    intro g hg0 i
    have hq : qExpansion 1 (⇑(∑ i, g i • f i) : ℍ → ℂ) = 0 := by
      rw [hg0]; exact qExpansion_zero 1
    rw [qExpansion_sum_smul M] at hq
    have h3 : (((∑ i, g i • b i : ↥(riemannRochSpace (k • Dw))) :
          ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) : LaurentSeries ℂ) =
        ∑ i, algebraMap ℂ (LaurentSeries ℂ) (g i) *
          (((b i : ↥(riemannRochSpace (k • Dw))) :
            ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) : LaurentSeries ℂ) := by
      rw [Submodule.coe_sum, AddSubmonoidClass.coe_finset_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, IntermediateField.coe_smul]
      first
        | rw [Algebra.smul_def]
        | (rw [← HahnSeries.C_mul_eq_smul, HahnSeries.C_eq_algebraMap])
    have hL : (((∑ i, g i • b i : ↥(riemannRochSpace (k • Dw))) :
          ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) : LaurentSeries ℂ) * W ^ k = 0 := by
      have h1 := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) hq
      rw [map_sum, map_zero] at h1
      have h2 : ∀ i, HahnSeries.ofPowerSeries ℤ ℂ (g i • qExpansion 1 (⇑(f i) : ℍ → ℂ)) =
          (algebraMap ℂ (LaurentSeries ℂ) (g i) *
            (((b i : ↥(riemannRochSpace (k • Dw))) :
              ↥(laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) : LaurentSeries ℂ)) * W ^ k :=
        fun i => by rw [ofPowerSeries_smul, hf i, hWdef, mul_assoc]
      simp only [h2] at h1
      rw [← Finset.sum_mul] at h1
      rw [h3]; exact h1
    have hsum := (mul_eq_zero.1 hL).resolve_right (pow_ne_zero _ hW)
    have hsumF : (∑ i, g i • b i) = 0 := by
      apply Subtype.val_injective; apply Subtype.val_injective
      rw [hsum]; rfl
    exact Fintype.linearIndependent_iff.1 b.linearIndependent g hsumF i
  ·
    have h12 : (12 : ℤ) * d = k * μ - μ + 6 * cc := by
      rw [← hell, hRR]; linarith [hdegw, hgZ]
    zify [show 1 ≤ k by omega]
    push_cast
    nlinarith [h12, hμZ]

end S_ModularForm_exists_linearIndependent_gamma1_dimFormula_le_card_of_odd
end P2MW
export P2MW.S_ModularForm_exists_linearIndependent_gamma1_dimFormula_le_card_of_odd (solution)
