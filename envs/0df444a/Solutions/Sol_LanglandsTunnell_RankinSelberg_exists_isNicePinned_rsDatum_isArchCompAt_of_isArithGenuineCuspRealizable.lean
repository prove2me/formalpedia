-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_isNicePinned_rsDatum_isArchCompAt_of_isArithGenuineCuspRealizable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/007b6d89-59e9-55d3-b20d-74c0921a4df6

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_M4aHerbrand_ArchSemilocal
import Definitions.Def_M4aHerbrand_GenuineBeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Theorems.Thm_LanglandsTunnell_RankinSelberg_eq_comp_idelicNorm_of_forall_uniformizerIdele_eq_pow_inertiaDeg
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt_apply_ne
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_LanglandsTunnell_exists_realArchParam_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_continuous_realization
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unitIdele_over_idelicNorm_eq_one_and_apply_ne_one_of_ne
import Theorems.Thm_NumberField_exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one
import Theorems.Thm_LanglandsTunnell_Converse_exists_sPartDual_eq_of_forall_cancel_units
import Theorems.Thm_LanglandsTunnell_RankinSelberg_isNicePinned_rsDatum_of_centralInduced_of_localWhittaker_of_not_exists_eq_pow_inertiaDeg_of_normPin_archTrivial
import Theorems.Thm_LanglandsTunnell_Converse_exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Theorems.Thm_LanglandsTunnell_Converse_isAdmissibleTwist_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_of_finrank_eq_three
import Theorems.Thm_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_norm_centralChar_eq_ideleNorm_of_forall_norm_b_eq_one
import Theorems.Thm_LanglandsTunnell_RankinSelberg_eq_comp_idelicNorm_of_forall_under_notMem_uniformizerIdele_eq_pow_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_isNicePinned_rsDatum_isArchCompAt_of_isArithGenuineCuspRealizable
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.SpectralSide.instCompactSpaceMatrix FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SmoothVectors.nonarchimedeanGroup_gl2Padic LocalGL2.Kirillov.fintype_Qm LocalGL2.Kirillov.fintype_Ch LocalGL2.Kirillov.addCommGroup_Ch LocalGL2.Kirillov.finite_Qm LocalGL2.Kirillov.addCommGroup_additive_Qm"
p2m_attr_erase "instance" "LocalGL2.Kirillov.decidableEq_Ch LocalGL2.Kirillov.finite_additive_Qm IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions IsDedekindDomain.HeightOneSpectrum.instSeparableSpaceAdicCompletionOfCountable_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.mem_sigmaCentralizer_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.Converse.ArchDatumC.mk.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LanglandsTunnell.RankinSelberg.rsGlobalIntegral_zero_left LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk LanglandsTunnell.deltaLiftSystem_level LanglandsTunnell.deltaLiftSystem_toRawCentral AutomorphicForm.gl2Weyl_val LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.fnTwist3_apply LanglandsTunnell.CubicInduction.CubicInductionData.mk.sizeOf_spec LanglandsTunnell.CubicInduction.CubicInductionData.mk.injEq FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one"
p2m_attr_erase "simp" "groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv FLT.SmoothVectors.coe_gl2UnipotentPadic_inv FLT.SmoothVectors.coe_gl2UnipotentPadic LocalNewvector.unitValuation_apply LocalNewvector.valChar_apply LocalGL2.Kirillov.zG_coe LocalGL2.Kirillov.wG_coe LocalGL2.Kirillov.dg_coe LocalGL2.Kirillov.rT_apply"
p2m_attr_erase "simp" "LocalGL2.Kirillov.rT_one Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star AutomorphicForm.mem_inducedSectionSubmodule_iff LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right AutomorphicForm.cpowChar_apply_val ContinuousAddEquiv.preimage_mulLeft_smul MeasureTheory.L2.kernelIntegralLM_apply LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply ArtinL.Abelian.coeff_zero IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf AutomorphicForm.gl3LFactorPoly_def AutomorphicForm.JPSSGL3Factored.mk.injEq AutomorphicForm.coeff_three_gl3LFactorPoly AutomorphicForm.coeff_one_gl3LFactorPoly AutomorphicForm.coeff_zero_gl3LFactorPoly AutomorphicForm.JPSSGL3Factored.mk.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.JPSSConverseFactored.mk.sizeOf_spec AutomorphicForm.coeff_two_gl3LFactorPoly AutomorphicForm.JPSSConverseFactored.mk.injEq AutomorphicForm.coeff_zero_heckeLFactorPoly AutomorphicForm.coeff_two_heckeLFactorPoly AutomorphicForm.heckeLFactorPoly_def AutomorphicForm.HeckeEigensystem.localLFactor_def AutomorphicForm.coeff_one_heckeLFactorPoly AutomorphicForm.satakePow_two"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.Converse NumberField.TateGlobal

noncomputable section

namespace EBCSol

namespace NormPin

open LanglandsTunnell.TateLocal M4aHerbrand.GenuineDescent
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

theorem localChar_mul_inv_apply (μ η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) :
    localChar (μ * η⁻¹) v t = localChar μ v t * (localChar η v t)⁻¹ := by
  simp only [localChar_apply, MonoidHom.mul_apply, MonoidHom.inv_apply]

theorem hasConductorExponentAt_congr_units (v : HeightOneSpectrum (𝓞 K))
    {χ χ' : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ}
    (h : ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 → χ' t = χ t)
    (hχ : HasConductorExponentAt K v χ c) : HasConductorExponentAt K v χ' c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [h u ((mem_higherUnitsAt_iff K v).mp hu).1]
    exact hχ.1 u hu
  · obtain ⟨u, hu, hne⟩ := hχ.2 m hm
    exact ⟨u, hu, by rwa [h u ((mem_higherUnitsAt_iff K v).mp hu).1]⟩

theorem hasConductorExponentAt_inv (v : HeightOneSpectrum (𝓞 K))
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ} (hχ : HasConductorExponentAt K v χ c) :
    HasConductorExponentAt K v χ⁻¹ c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.inv_apply, hχ.1 u hu, inv_one]
  · obtain ⟨u, hu, hne⟩ := hχ.2 m hm
    exact ⟨u, hu, by rwa [MonoidHom.inv_apply, Ne, inv_eq_one]⟩

theorem continuous_inv_char (v : HeightOneSpectrum (𝓞 K)) {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : Continuous χ) : Continuous (χ⁻¹ : (v.adicCompletion K)ˣ →* ℂˣ) := by
  have : (⇑(χ⁻¹ : (v.adicCompletion K)ˣ →* ℂˣ)) = fun t => (χ t)⁻¹ := by
    funext t; rfl
  rw [this]
  exact hχ.inv

theorem epsS_package (χN : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (hχNc : ∀ v, Continuous (χN v))
    (W : Finset (HeightOneSpectrum (𝓞 K))) (c' : HeightOneSpectrum (𝓞 K) → ℕ)
    (hχNH : ∀ v ∈ W, HasConductorExponentAt K v (χN v) (c' v))
    (w₀ : HeightOneSpectrum (𝓞 K)) (hw₀ : w₀ ∈ W)
    (ξ : (w₀.adicCompletion K)ˣ →* ℂˣ) (hξc : Continuous ξ) (c₀ : ℕ)
    (hξH : HasConductorExponentAt K w₀ ξ c₀) (hc₀ : c₀ < c' w₀)
    (hmul : ∀ (lam nu : (w₀.adicCompletion K)ˣ →* ℂˣ) (a b : ℕ),
      HasConductorExponentAt K w₀ lam a → HasConductorExponentAt K w₀ nu b → b < a →
        HasConductorExponentAt K w₀ (lam * nu) a) :
    (∀ v, Continuous (Function.update (fun v => (χN v)⁻¹) w₀ ((χN w₀)⁻¹ * ξ) v)) ∧
    (∀ v ∈ W, HasConductorExponentAt K v (Function.update (fun v => (χN v)⁻¹) w₀ ((χN w₀)⁻¹ * ξ) v) (c' v)) ∧
    (∀ t : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ,
      ∏ w ∈ W, Function.update (fun v => (χN v)⁻¹) w₀ ((χN w₀)⁻¹ * ξ) w (t w)
        = (∏ w ∈ W, χN w (t w))⁻¹ * ξ (t w₀)) ∧
    (∀ v, v ≠ w₀ → ∀ t, Function.update (fun v => (χN v)⁻¹) w₀ ((χN w₀)⁻¹ * ξ) v t = (χN v t)⁻¹) ∧
    (∀ t, Function.update (fun v => (χN v)⁻¹) w₀ ((χN w₀)⁻¹ * ξ) w₀ t = (χN w₀ t)⁻¹ * ξ t) := by
  classical
  set epsS := Function.update (fun v => (χN v)⁻¹) w₀ ((χN w₀)⁻¹ * ξ) with hepsS
  have hoff : ∀ v, v ≠ w₀ → epsS v = (χN v)⁻¹ := fun v hv => by
    rw [hepsS, Function.update_of_ne hv]
  have hon : epsS w₀ = (χN w₀)⁻¹ * ξ := by rw [hepsS, Function.update_self]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v = w₀
    · subst hv
      rw [hon]
      have : (⇑((χN v)⁻¹ * ξ : (v.adicCompletion K)ˣ →* ℂˣ)) = fun t => (χN v t)⁻¹ * ξ t := by
        funext t; rfl
      rw [this]
      exact ((hχNc v).inv).mul hξc
    · rw [hoff v hv]
      exact continuous_inv_char K v (hχNc v)
  · intro v hvW
    by_cases hv : v = w₀
    · subst hv
      rw [hon]
      exact hmul _ _ _ _ (hasConductorExponentAt_inv K v (hχNH v hvW)) hξH hc₀
    · rw [hoff v hv]
      exact hasConductorExponentAt_inv K v (hχNH v hvW)
  · intro t
    have hsplit : ∏ w ∈ W, epsS w (t w) = epsS w₀ (t w₀) * ∏ w ∈ W.erase w₀, epsS w (t w) :=
      (Finset.mul_prod_erase W (fun w => epsS w (t w)) hw₀).symm
    have hsplit' : ∏ w ∈ W, χN w (t w) = χN w₀ (t w₀) * ∏ w ∈ W.erase w₀, χN w (t w) :=
      (Finset.mul_prod_erase W (fun w => χN w (t w)) hw₀).symm
    have herase : ∏ w ∈ W.erase w₀, epsS w (t w) = (∏ w ∈ W.erase w₀, χN w (t w))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun w hw => by
        rw [hoff w (Finset.ne_of_mem_erase hw), MonoidHom.inv_apply]
    rw [hsplit, hsplit', herase, hon, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  · intro v hv t
    rw [hoff v hv, MonoidHom.inv_apply]
  · intro t
    rw [hon, MonoidHom.mul_apply, MonoidHom.inv_apply]

theorem hasConductorExponentAt_zero_of_cancel (μ η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (epsSv : (v.adicCompletion K)ˣ →* ℂˣ)
    (heps : ∀ t, epsSv t = (localChar η v t)⁻¹)
    (hcancel : ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 → localChar μ v t * epsSv t = 1) :
    HasConductorExponentAt K v (localChar (μ * η⁻¹) v) 0 := by
  rw [hasConductorExponentAt_zero_iff]
  intro t ht
  have h := hcancel t ht
  rw [heps] at h
  rw [localChar_mul_inv_apply]
  exact h

theorem hasConductorExponentAt_of_cancel_aux (μ η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (epsSv ξ : (v.adicCompletion K)ˣ →* ℂˣ) (c₀ : ℕ) (hξ : HasConductorExponentAt K v ξ c₀)
    (heps : ∀ t, epsSv t = (localChar η v t)⁻¹ * ξ t)
    (hcancel : ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 → localChar μ v t * epsSv t = 1) :
    HasConductorExponentAt K v (localChar (μ * η⁻¹) v) c₀ := by
  refine hasConductorExponentAt_congr_units K v (χ := ξ⁻¹) ?_ (hasConductorExponentAt_inv K v hξ)
  intro t ht
  have h := hcancel t ht
  rw [heps] at h
  rw [localChar_mul_inv_apply, MonoidHom.inv_apply]

  rw [← mul_assoc] at h
  exact eq_inv_of_mul_eq_one_left h

theorem exists_levelExp {R : Type} [CommRing R] [IsDedekindDomain R] (I : Ideal R) (hI : I ≠ ⊥) :
    ∃ b : HeightOneSpectrum R → ℕ, ∀ p : HeightOneSpectrum R, p.asIdeal ^ b p ∣ I ∧ ¬ p.asIdeal ^ (b p + 1) ∣ I :=
  ⟨fun p => multiplicity p.asIdeal I, fun p => ⟨pow_multiplicity_dvd _ _,
    (FiniteMultiplicity.of_prime_left p.prime hI).not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)⟩⟩

theorem exists_chiA_epsS (hdeg : Module.finrank ℚ K = 3)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hSK : ∀ w ∈ SK, w.under (𝓞 ℚ) ∈ SQ)
    (depth : HeightOneSpectrum (𝓞 K) → ℕ) (fl : HeightOneSpectrum (𝓞 ℚ) → ℤ)
    (w₀ : HeightOneSpectrum (𝓞 K)) (hw₀ : w₀ ∈ SK)
    (ξ : (w₀.adicCompletion K)ˣ →* ℂˣ) (hξc : Continuous ξ) (c₀ : ℕ) (hξH : HasConductorExponentAt K w₀ ξ c₀) :
    ∃ (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (kχ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
      (c' : HeightOneSpectrum (𝓞 K) → ℕ) (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ),
      IsAdmissibleTwist ℚ χA ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → IsUnramifiedCharAt χA v) ∧
      (∀ p ∈ SQ, HasConductorExponentAt ℚ p (localChar χA p) (kχ p)) ∧
      (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ χA v 0 0) ∧
      (∀ p ∈ SQ, fl p ≤ (kχ p : ℤ)) ∧
      (∀ v, Continuous (epsS v)) ∧
      (∀ v ∈ SK, HasConductorExponentAt K v (epsS v) (c' v)) ∧
      (∀ v ∈ SK, depth v ≤ c' v) ∧
      (∀ t : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ,
        ∏ w ∈ SK, epsS w (t w)
          = (∏ w ∈ SK, localChar (χA.comp (genuineBaseChange ℚ K).idelicNorm) w (t w))⁻¹ * ξ (t w₀)) ∧
      (∀ v, v ≠ w₀ → ∀ t, epsS v t = (localChar (χA.comp (genuineBaseChange ℚ K).idelicNorm) v t)⁻¹) ∧
      (∀ t, epsS w₀ t = (localChar (χA.comp (genuineBaseChange ℚ K).idelicNorm) w₀ t)⁻¹ * ξ t) := by
  classical

  let m : HeightOneSpectrum (𝓞 K) → ℕ := fun w => max 12 (max (depth w) (c₀ + 1))

  let kχ : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun p => 3 + (fl p).toNat + ∑ w ∈ SK, m w
  have hk3 : ∀ p ∈ SQ, 3 ≤ kχ p := fun p _ => by simp only [kχ]; omega
  have hkfl : ∀ p ∈ SQ, fl p ≤ (kχ p : ℤ) := fun p _ => by
    have h1 : (fl p).toNat ≤ kχ p := by simp only [kχ]; omega
    exact (Int.self_le_toNat (fl p)).trans (by exact_mod_cast h1)
  have hkm : ∀ w ∈ SK, m w ≤ kχ (w.under (𝓞 ℚ)) := fun w hw => by
    have := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) hw
    simp only [kχ]; omega
  obtain ⟨χA, hχA, hkχ, hχoff, hχinf⟩ :=
    LanglandsTunnell.Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le SQ kχ hk3

  have hc : ∀ w ∈ SK, ∃ c : ℕ, max (depth w) (c₀ + 1) ≤ c ∧
      HasConductorExponentAt K w (localChar (χA.comp (genuineBaseChange ℚ K).idelicNorm) w) c := by
    intro w hw
    have hk := hkχ _ (hSK w hw)
    have h12 : 12 ≤ kχ (w.under (𝓞 ℚ)) := (le_max_left _ _).trans (hkm w hw)
    obtain ⟨a, hka, ha, -⟩ :=
      LanglandsTunnell.TateLocal.hasConductorExponentAt_comp_norm_of_finrank_eq_three K hdeg (w.under (𝓞 ℚ))
        ⟨w, rfl⟩ (localChar χA (w.under (𝓞 ℚ))) _ h12 hk
    refine ⟨a, ((le_max_right _ _).trans (hkm w hw)).trans hka, ?_⟩
    have key := NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K 1 χA (w.under (𝓞 ℚ))
      ⟨w, rfl⟩
    refine hasConductorExponentAt_congr_units K w (fun t _ => ?_) ha
    have := congrArg (fun f => f t) key
    simpa only [localChar_apply, MonoidHom.mul_apply, MonoidHom.one_apply, one_mul,
      MonoidHom.comp_apply] using this
  choose! c' hc'le hc'H using hc
  have hNadm : IsAdmissibleTwist K (χA.comp (genuineBaseChange ℚ K).idelicNorm) :=
    LanglandsTunnell.Converse.isAdmissibleTwist_comp_idelicNorm_genuineBaseChange ℚ K χA hχA
  have hχNc : ∀ v, Continuous (localChar (χA.comp (genuineBaseChange ℚ K).idelicNorm) v) :=
    fun v => NumberField.TateGlobal.continuous_localChar _ hNadm.2.1 v
  obtain ⟨hcont, hH, hprod, hoffw, honw⟩ := epsS_package K (fun v => localChar (χA.comp (genuineBaseChange ℚ K).idelicNorm) v)
    hχNc SK c' hc'H w₀ hw₀ ξ hξc c₀ hξH
    (lt_of_lt_of_le (Nat.lt_succ_self c₀) ((le_max_right _ _).trans (hc'le w₀ hw₀)))
    (fun lam nu a b hl hn hlt =>
      LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt K w₀ lam nu a b hl hn hlt)
  exact ⟨χA, kχ, c', _, hχA, hχoff, hkχ, hχinf, hkfl, hcont, hH,
    fun v hv => (le_max_left _ _).trans (hc'le v hv), hprod, hoffw, honw⟩

end NormPin

private theorem subsingleton_algebra_ratRingOfIntegers (R : Type) [Semiring R] :
    Subsingleton (Algebra (𝓞 ℚ) R) := by
  refine ⟨fun a b => ?_⟩
  refine Algebra.algebra_ext a b fun x => ?_
  obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
  have h := RingHom.ext_int
    ((@algebraMap (𝓞 ℚ) R _ _ a).comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ))
    ((@algebraMap (𝓞 ℚ) R _ _ b).comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ))
  exact RingHom.congr_fun h n

section canonical
variable (K : Type) [Field K] [NumberField K]

private noncomputable abbrev canonAlg : Algebra (𝓞 ℚ) (𝓞 K) := inferInstance

private theorem finite_fibre_canonical (p : HeightOneSpectrum (𝓞 ℚ)) :
    Finite {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 ℚ) = p} :=
  HeightOneSpectrum.Extension.finite (𝓞 ℚ) ℚ K (𝓞 K) p

end canonical

private theorem finite_fibre_bound (K : Type) [Field K] [NumberField K]
    [inst : Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (p : HeightOneSpectrum (𝓞 ℚ)) :
    Finite {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 ℚ) = p} := by
  haveI := subsingleton_algebra_ratRingOfIntegers (𝓞 K)
  obtain rfl : inst = canonAlg K := Subsingleton.elim _ _
  exact finite_fibre_canonical K p

open Classical in
private def deltaZero (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (↥S → ℤ) → ℂ :=
  fun n => if n = 0 then 1 else 0

private theorem sPart_deltaZero (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) :
    sPart K S (deltaZero K S) μ = fun _ => 1 := by
  funext s
  unfold sPart deltaZero
  rw [tsum_eq_single (0 : ↥S → ℤ)]
  · simp
  · intro n hn
    simp [hn]

private theorem deltaZero_norm_le (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ↥S → ℤ) : ‖deltaZero K S n‖ ≤ 1 := by
  unfold deltaZero
  split_ifs <;> simp

private theorem deltaZero_eq_zero_of_neg (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ↥S → ℤ) (h : ∃ v, n v < 0) : deltaZero K S n = 0 := by
  unfold deltaZero
  obtain ⟨v, hv⟩ := h
  have hn : n ≠ 0 := fun h0 => by simp [h0] at hv
  simp [hn]

private theorem deltaZero_ne_zero (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    deltaZero K S ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [deltaZero] at h0

section Witness

open Classical

variable (K : Type) [Field K] [NumberField K]

private noncomputable def ramQ : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  (Ideal.finite_factors (I := differentIdeal (𝓞 ℚ) (𝓞 K)) differentIdeal_ne_bot).toFinset.image
    (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ))

variable {K}

private theorem isUnramifiedAt_of_under_notMem_ramQ (𝔓 : HeightOneSpectrum (𝓞 K))
    (h : 𝔓.under (𝓞 ℚ) ∉ ramQ K) : Algebra.IsUnramifiedAt (𝓞 ℚ) 𝔓.asIdeal := by
  refine (not_dvd_differentIdeal_iff (A := 𝓞 ℚ) (B := 𝓞 K)).mp ?_
  intro hdvd
  apply h
  unfold ramQ
  refine Finset.mem_image.mpr ⟨𝔓, ?_, rfl⟩
  simpa using hdvd

private theorem ramificationIdx_eq_one_of_under_notMem_ramQ (𝔓 : HeightOneSpectrum (𝓞 K))
    (h : 𝔓.under (𝓞 ℚ) ∉ ramQ K) :
    Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1 := by
  haveI := isUnramifiedAt_of_under_notMem_ramQ 𝔓 h
  change (𝔓.asIdeal.under (𝓞 ℚ)).ramificationIdx' 𝔓.asIdeal = 1
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.asIdeal.under (𝓞 ℚ)) 𝔓.asIdeal (Ideal.under_ne_bot (𝓞 ℚ) 𝔓.ne_bot)]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 ℚ) (p := 𝔓.asIdeal)

private noncomputable def levelPrimes (Φ : HeckeEigensystem ℚ ℂ) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  (Ideal.finite_factors Φ.level_ne_bot).toFinset

private theorem mem_levelPrimes (Φ : HeckeEigensystem ℚ ℂ) (p : HeightOneSpectrum (𝓞 ℚ))
    (h : Φ.level ≤ p.asIdeal) : p ∈ levelPrimes Φ := by
  unfold levelPrimes
  rw [Set.Finite.mem_toFinset]
  exact Ideal.dvd_iff_le.mpr h

variable (K) in
private theorem fibreSet_finite (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ((fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ)) ⁻¹' (↑SQ : Set (HeightOneSpectrum (𝓞 ℚ)))).Finite :=
  Set.Finite.preimage' SQ.finite_toSet fun p _ => Set.finite_coe_iff.mp (finite_fibre_canonical K p)

variable (K) in
private noncomputable def fibreFinset (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (fibreSet_finite K SQ).toFinset

private theorem mem_fibreFinset (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    𝔓 ∈ fibreFinset K SQ ↔ 𝔓.under (𝓞 ℚ) ∈ SQ := by
  unfold fibreFinset
  rw [Set.Finite.mem_toFinset]
  simp

end Witness

private theorem norm_le_of_single_support {ι : Type} (Ad : ι → ℂ) (n₀ : ι) (hsupp : ∀ n, n ≠ n₀ → Ad n = 0)
    (n : ι) : ‖Ad n‖ ≤ ‖Ad n₀‖ := by
  by_cases h : n = n₀
  · subst h; exact le_rfl
  · rw [hsupp n h, norm_zero]; exact norm_nonneg _

private theorem eq_zero_of_lt_of_single_support (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (Ad : (↥SK → ℤ) → ℂ) (n₀ : ↥SK → ℤ)
    (hsupp : ∀ n, n ≠ n₀ → Ad n = 0) (n : ↥SK → ℤ) (hn : ∃ v, n v < n₀ v) : Ad n = 0 := by
  obtain ⟨v, hv⟩ := hn
  exact hsupp n (fun h => by subst h; exact lt_irrefl _ hv)

section RegionB
open M4aHerbrand
open scoped TensorProduct NumberField.LiesOver
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver
open Module

private theorem norm_transport {ι R S R' S' : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] [Algebra R S] [CommRing R'] [CommRing S'] [Algebra R' S']
    (bS : Module.Basis ι R S) (c : Module.Basis ι R' S') (π : R →+* R') (P : S →+* S')
    (hP : ∀ (r : R) (s : S), P (r • s) = π r • P s) (hb : ∀ i, P (bS i) = c i) (x : S) :
    π (Algebra.norm R x) = Algebra.norm R' (P x) := by
  rw [Algebra.norm_eq_matrix_det bS, Algebra.norm_eq_matrix_det c, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul]
  have hx : P x * c j = ∑ k, π (bS.repr (x * bS j) k) • c k := by
    rw [← hb j, ← map_mul]
    conv_lhs => rw [← bS.sum_repr (x * bS j)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hP, hb]
  rw [hx, c.repr_sum_self]

universe u v

section DetPi

variable {R : Type*} [CommRing R] {ι : Type*}
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

private def piMap (f : ∀ i, M i →ₗ[R] M i) : (∀ i, M i) →ₗ[R] (∀ i, M i) :=
  LinearMap.pi fun i => (f i).comp (LinearMap.proj i)

@[scoped simp] private theorem piMap_apply (f : ∀ i, M i →ₗ[R] M i) (x : ∀ i, M i) (i : ι) :
    piMap f x i = f i (x i) :=
  rfl

end DetPi

section DetPiInduction

variable {R : Type*} [CommRing R]

private theorem det_pi' (ι₀ : Type u) [Fintype ι₀] :
    ∀ {M : ι₀ → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
      (f : ∀ i, M i →ₗ[R] M i), (piMap f).det = ∏ i, (f i).det := by
  refine Fintype.induction_empty_option
    (P := fun γ instγ =>
      ∀ {M : γ → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
        [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
        (f : ∀ i, M i →ₗ[R] M i),
        (piMap f).det = (@Finset.univ γ instγ).prod fun i => (f i).det)
    ?of_equiv ?h_empty ?h_option ι₀
  case of_equiv =>
    intro α β _ e ih M _ _ _ _ f
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let E := LinearEquiv.piCongrLeft R M e
    have hE : ∀ (y : ∀ a, M (e a)) (a), E y (e a) = y a := fun y a =>
      show Equiv.piCongrLeft M e y (e a) = y a from Equiv.piCongrLeft_apply_apply M e y a
    have hEs : ∀ (x : ∀ b, M b) (a), E.symm x a = x (e a) := fun x a =>
      show Equiv.piCongrLeft' M e.symm x a = x (e a) from rfl
    have hconj : piMap f
        = (E : (∀ a, M (e a)) →ₗ[R] ∀ b, M b) ∘ₗ (piMap fun a => f (e a))
            ∘ₗ (E.symm : (∀ b, M b) →ₗ[R] ∀ a, M (e a)) := by
      apply LinearMap.ext
      intro x
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      show f (e a) (x (e a)) = E ((piMap fun a => f (e a)) (E.symm x)) (e a)
      rw [hE]
      show f (e a) (x (e a)) = f (e a) (E.symm x a)
      rw [hEs]
    rw [hconj, LinearMap.det_conj, ih]
    exact Fintype.prod_equiv e (fun a => (f (e a)).det) (fun b => (f b).det) fun a => rfl
  case h_empty =>
    intro M _ _ _ _ f
    haveI : Subsingleton (∀ i : PEmpty, M i) := ⟨fun a b => funext fun i => i.elim⟩
    rw [LinearMap.det_eq_one_of_subsingleton, Finset.prod_of_isEmpty]
  case h_option =>
    intro α _ ih M _ _ _ _ f
    let E : (M none × ∀ a, M (some a)) ≃ₗ[R] ∀ i, M i :=
      (LinearEquiv.piOptionEquivProd R).symm
    have hconj : piMap f
        = (E : _ →ₗ[R] ∀ i, M i) ∘ₗ ((f none).prodMap (piMap fun a => f (some a)))
            ∘ₗ (E.symm : (∀ i, M i) →ₗ[R] _) := by
      apply LinearMap.ext
      intro x
      funext i
      cases i <;> rfl
    rw [hconj, LinearMap.det_conj, LinearMap.det_prodMap, ih, Fintype.prod_option]

end DetPiInduction

section NormPi

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
variable {S : ι → Type*} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]

omit [Fintype ι] in
private theorem lmul_pi (x : ∀ i, S i) :
    Algebra.lmul R (∀ i, S i) x = piMap fun i => Algebra.lmul R (S i) (x i) := by
  apply LinearMap.ext
  intro y
  rfl

private theorem norm_pi [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)] (x : ∀ i, S i) :
    Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  rw [Algebra.norm_apply, show Algebra.lmul R (∀ i, S i) x
      = piMap fun i => Algebra.lmul R (S i) (x i) from lmul_pi x, det_pi']
  rfl

end NormPi

section Arch

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private def evalInf (w : InfinitePlace L) : AdeleRing (𝓞 L) L →+* w.Completion where
  toFun x := x.1 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private def projPiInf (v : InfinitePlace K) :
    AdeleRing (𝓞 L) L →+* (∀ w : v.Extension L, w.1.Completion) :=
  RingHom.pi fun w => evalInf L w.1

omit [NumberField K] in
private theorem projPiInf_apply (v : InfinitePlace K) (x : AdeleRing (𝓞 L) L) (w : v.Extension L) :
    projPiInf K L v x w = x.1 w.1 := rfl

private def adeleBasis (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    letI := B.β.toAlgebra
    Module.Basis (Fin (Module.finrank K L)) (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
  letI := B.β.toAlgebra
  (Algebra.TensorProduct.basis (AdeleRing (𝓞 K) K) (Module.finBasis K L)).map B.tensorEquiv.toLinearEquiv

private theorem adeleBasis_apply (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (i : Fin (Module.finrank K L)) :
    (letI := B.β.toAlgebra; adeleBasis K L B i) = algebraMap L (AdeleRing (𝓞 L) L) (Module.finBasis K L i) := by
  letI := B.β.toAlgebra
  show ((Algebra.TensorProduct.basis (AdeleRing (𝓞 K) K) (Module.finBasis K L)).map
    B.tensorEquiv.toLinearEquiv) i = _
  rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.basis_apply]
  exact B.tensorEquiv_one_tmul _

private def piBasisInf (v : InfinitePlace K) :
    Module.Basis (Fin (Module.finrank K L)) v.Completion (∀ w : v.Extension L, w.1.Completion) :=
  (Algebra.TensorProduct.basis v.Completion (Module.finBasis K L)).map
    (ArchSemilocal.placeEquivAlg (K := K) (L := L) v).toLinearEquiv

private theorem piBasisInf_apply (v : InfinitePlace K) (i : Fin (Module.finrank K L)) :
    piBasisInf K L v i =
      algebraMap L (∀ w : v.Extension L, w.1.Completion) (Module.finBasis K L i) := by
  rw [piBasisInf, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.basis_apply]
  funext w
  simp [ArchSemilocal.placeEquivAlg]

omit [NumberField K] in
private theorem projPiInf_algebraMap (v : InfinitePlace K) (l : L) :
    projPiInf K L v (algebraMap L (AdeleRing (𝓞 L) L) l) =
      algebraMap L (∀ w : v.Extension L, w.1.Completion) l := by
  funext w
  rfl

private theorem projPiInf_smul (v : InfinitePlace K) (r : AdeleRing (𝓞 K) K) (s : AdeleRing (𝓞 L) L) :
    projPiInf K L v ((GenuineDescent.genuineBaseChange K L).β r * s) =
      algebraMap v.Completion (∀ w : v.Extension L, w.1.Completion) (r.1 v) * projPiInf K L v s := by
  rw [map_mul]
  congr 1
  funext w
  rw [projPiInf_apply, Pi.algebraMap_apply, GenuineDescent.genuineBaseChange_β]
  obtain ⟨w, hw⟩ := w
  subst hw
  show (ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).conorm r.1 w = _
  rw [FLT.InfiniteAdeleBaseChange.InfinitePlaceData.conorm_apply,
    FLT.InfiniteAdeleBaseChange.InfinitePlaceData.baseChangeRingEquiv_apply,
    FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply]
  simp [ArchSemilocal.genuineInfinitePlaceData, ArchSemilocal.placeEquivAlg,
    NumberField.InfinitePlace.Completion.ext_iff, UniformSpace.Completion.coe_one]

private theorem adelicNorm_fst_apply (v : InfinitePlace K) (x : AdeleRing (𝓞 L) L) :
    ((GenuineDescent.genuineBaseChange K L).adelicNorm x).1 v =
      Algebra.norm v.Completion (projPiInf K L v x) := by
  letI : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) := (GenuineDescent.genuineBaseChange K L).β.toAlgebra
  exact norm_transport (adeleBasis K L (GenuineDescent.genuineBaseChange K L)) (piBasisInf K L v)
    (evalInf K v) (projPiInf K L v)
    (fun r s => by
      rw [Algebra.smul_def, Algebra.smul_def]
      exact projPiInf_smul K L v r s)
    (fun i => by rw [adeleBasis_apply, piBasisInf_apply, projPiInf_algebraMap]) x

private theorem adelicNorm_fst_apply_of_eq_one (v : InfinitePlace K) (w : v.Extension L)
    (x : AdeleRing (𝓞 L) L) (hx : ∀ w' : v.Extension L, w' ≠ w → x.1 w'.1 = 1) :
    ((GenuineDescent.genuineBaseChange K L).adelicNorm x).1 v =
      Algebra.norm v.Completion (x.1 w.1) := by
  classical
  haveI : ∀ w' : v.Extension L, Module.Free v.Completion w'.1.Completion :=
    fun _ => Module.Free.of_divisionRing _ _
  haveI : ∀ w' : v.Extension L, Module.Finite v.Completion w'.1.Completion :=
    fun w' => ArchSemilocal.finiteDimensional_completion v w'.1
  rw [adelicNorm_fst_apply, norm_pi]
  rw [Finset.prod_eq_single w]
  · rfl
  · intro w' _ hw'
    rw [projPiInf_apply, hx w' hw']
    exact map_one _
  · intro h
    exact absurd (Finset.mem_univ w) h

end Arch

section ProdBase

variable {ι R₁ R₂ S₁ S₂ : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing R₁] [CommRing R₂] [CommRing S₁] [CommRing S₂]
  [Algebra (R₁ × R₂) (S₁ × S₂)] [Algebra R₁ S₁] [Algebra R₂ S₂]

private theorem norm_snd_of_prod (b : Module.Basis ι (R₁ × R₂) (S₁ × S₂))
    (h₁ : ∀ (r : R₁ × R₂) (s : S₁ × S₂), (r • s).1 = r.1 • s.1)
    (h₂ : ∀ (r : R₁ × R₂) (s : S₁ × S₂), (r • s).2 = r.2 • s.2) (x : S₁ × S₂) :
    (Algebra.norm (R₁ × R₂) x).2 = Algebra.norm R₂ x.2 := by
  have hli : LinearIndependent R₂ (fun i => (b i).2) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h : ∑ j, ((0 : R₁), g j) • b j = 0 := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum, Prod.fst_zero]
        exact Finset.sum_eq_zero fun j _ => by
          rw [h₁]
          exact zero_smul R₁ _
      · rw [Prod.snd_sum, Prod.snd_zero, ← hg]
        exact Finset.sum_congr rfl fun j _ => h₂ _ _
    have h0 := Fintype.linearIndependent_iff.mp b.linearIndependent (fun j => ((0 : R₁), g j)) h i
    exact congrArg Prod.snd h0
  have hsp : ⊤ ≤ Submodule.span R₂ (Set.range fun i => (b i).2) := by
    intro s _
    have hrep := b.sum_repr ((0 : S₁), s)
    have hs : s = ∑ i, (b.repr ((0 : S₁), s) i).2 • (b i).2 := by
      have := congrArg Prod.snd hrep
      rw [Prod.snd_sum] at this
      refine this.symm.trans ?_
      exact Finset.sum_congr rfl fun i _ => h₂ _ _
    rw [hs]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let c : Module.Basis ι R₂ S₂ := Module.Basis.mk hli hsp
  exact norm_transport b c (RingHom.snd R₁ R₂) (RingHom.snd S₁ S₂) (fun r s => h₂ r s)
    (fun i => by simp [c, Module.Basis.mk_apply]) x

end ProdBase

section Idele

open NumberField.AdelicVolume NumberField.TateGlobal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem adelicNorm_snd_eq_one (x : AdeleRing (𝓞 L) L) (hx : x.2 = 1) :
    ((GenuineDescent.genuineBaseChange K L).adelicNorm x).2 = 1 := by
  letI : Algebra (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L) :=
    (GenuineDescent.genuineBaseChange K L).β.toAlgebra
  letI : Algebra (InfiniteAdeleRing K) (InfiniteAdeleRing L) :=
    (ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).conorm.toAlgebra
  letI : Algebra (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L) :=
    (Bridge.finiteConorm (𝓞 K) K L (𝓞 L)).toAlgebra
  have key := norm_snd_of_prod (adeleBasis K L (GenuineDescent.genuineBaseChange K L))
    (fun r s => by
      rw [Algebra.smul_def, Algebra.smul_def]
      rfl)
    (fun r s => by
      rw [Algebra.smul_def, Algebra.smul_def]
      rfl) x
  exact key.trans (by rw [hx, map_one])

private def normUnit (v : InfinitePlace K) (w : v.Extension L) : (w.1.Completion)ˣ →* (v.Completion)ˣ :=
  Units.map (Algebra.norm v.Completion : w.1.Completion →* v.Completion)

private theorem idelicNorm_archCentralUnit (v : InfinitePlace K) (w : v.Extension L) (x : (w.1.Completion)ˣ) :
    (GenuineDescent.genuineBaseChange K L).idelicNorm (archCentralUnit L w.1 x) =
      archCentralUnit K v (normUnit K L v w x) := by
  classical
  apply Units.ext
  refine Prod.ext (funext fun v' => ?_) ?_
  · show ((GenuineDescent.genuineBaseChange K L).adelicNorm (archCentralUnit L w.1 x : AdeleRing (𝓞 L) L)).1 v' = _
    by_cases hv : v' = v
    · subst hv
      rw [archCentralUnit_fst_self]
      rw [adelicNorm_fst_apply_of_eq_one K L v' w _ (fun w' hw' => archCentralUnit_fst_of_ne w.1 x
        (fun h => hw' (Subtype.ext h)))]
      rw [archCentralUnit_fst_self]
      rfl
    · rw [archCentralUnit_fst_of_ne v _ hv, adelicNorm_fst_apply]
      have hproj : projPiInf K L v' (archCentralUnit L w.1 x : AdeleRing (𝓞 L) L) = 1 := by
        funext w'
        rw [projPiInf_apply]
        refine archCentralUnit_fst_of_ne w.1 x fun h => hv ?_
        rw [← w'.2, h, w.2]
      rw [hproj, map_one]
  · show ((GenuineDescent.genuineBaseChange K L).adelicNorm (archCentralUnit L w.1 x : AdeleRing (𝓞 L) L)).2 = _
    rw [adelicNorm_snd_eq_one K L _ (archCentralUnit_snd w.1 x)]
    rfl

private theorem archLocalChar_comp_idelicNorm (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : InfinitePlace K)
    (w : v.Extension L) (x : (w.1.Completion)ˣ) :
    archLocalChar (η.comp (GenuineDescent.genuineBaseChange K L).idelicNorm) w.1 x =
      archLocalChar η v (normUnit K L v w x) := by
  rw [archLocalChar_apply, archLocalChar_apply, MonoidHom.comp_apply, idelicNorm_archCentralUnit]

end Idele

section LocalNorm

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.ComplexEmbedding

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
private theorem conj_extensionEmbedding_of_isReal {v : InfinitePlace K} (hv : v.IsReal) (c : v.Completion) :
    (starRingEnd ℂ) (extensionEmbedding v c) = extensionEmbedding v c := by
  rw [← extensionEmbeddingOfIsReal_apply hv c, Complex.conj_ofReal]

omit [NumberField K] [NumberField L] in
private theorem extensionEmbedding_norm_of_isReal {v : InfinitePlace K} (hv : v.IsReal) (w : v.Extension L)
    (hw : w.1.IsReal) (y : w.1.Completion) :
    extensionEmbedding v (Algebra.norm v.Completion y) = extensionEmbedding w.1 y := by
  haveI : ComplexEmbedding.LiesOver (extensionEmbedding w.1) (extensionEmbedding v) :=
    LiesOver.extensionEmbedding_liesOver_of_isReal w.1 hv
  have hrank : Module.finrank v.Completion w.1.Completion = 1 :=
    finrank_eq_one_of_isUnramified v (isUnramified_iff.mpr (Or.inl hw))
  haveI : Module.Free v.Completion w.1.Completion := Module.Free.of_divisionRing _ _
  haveI : FiniteDimensional v.Completion w.1.Completion := ArchSemilocal.finiteDimensional_completion v w.1
  obtain ⟨c, rfl⟩ :=
    ((Algebra.finrank_eq_one_iff_bijective_algebraMap (F := v.Completion) (E := w.1.Completion)).mp hrank).2 y
  rw [Algebra.norm_algebraMap, hrank, pow_one,
    ComplexEmbedding.LiesOver.over_apply (extensionEmbedding w.1) (extensionEmbedding v)]

omit [NumberField K] [NumberField L] in
private theorem extensionEmbedding_norm_of_isComplex {v : InfinitePlace K} (hv : v.IsReal) (w : v.Extension L)
    (hw : w.1.IsComplex) (y : w.1.Completion) :
    extensionEmbedding v (Algebra.norm v.Completion y) = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
  classical
  haveI : ComplexEmbedding.LiesOver (extensionEmbedding w.1) (extensionEmbedding v) :=
    LiesOver.extensionEmbedding_liesOver_of_isReal w.1 hv
  haveI : FiniteDimensional v.Completion w.1.Completion := ArchSemilocal.finiteDimensional_completion v w.1
  haveI : CharZero v.Completion := (extensionEmbedding v).charZero
  letI : Algebra v.Completion ℂ := (extensionEmbedding v).toAlgebra
  let φ₁ : w.1.Completion →ₐ[v.Completion] ℂ :=
    { extensionEmbedding w.1 with
      commutes' := fun c => ComplexEmbedding.LiesOver.over_apply (extensionEmbedding w.1) (extensionEmbedding v) }
  let φ₂ : w.1.Completion →ₐ[v.Completion] ℂ :=
    { conjugate (extensionEmbedding w.1) with
      commutes' := fun c => by
        show (starRingEnd ℂ) (extensionEmbedding w.1 (algebraMap v.Completion w.1.Completion c)) = _
        rw [ComplexEmbedding.LiesOver.over_apply (extensionEmbedding w.1) (extensionEmbedding v)]
        exact conj_extensionEmbedding_of_isReal hv c }
  have hne : φ₁ ≠ φ₂ := by
    intro h
    obtain ⟨z, hz⟩ := surjective_extensionEmbedding_of_isComplex hw Complex.I
    have h1 : φ₁ z = Complex.I := hz
    have h2 : φ₂ z = (starRingEnd ℂ) Complex.I := congrArg (starRingEnd ℂ) hz
    rw [h, h2, Complex.conj_I] at h1
    exact Complex.I_ne_zero (by linear_combination (-(1 : ℂ) / 2) * h1)
  have hrank : Module.finrank v.Completion w.1.Completion = 2 := by
    refine finrank_eq_two_of_isRamified v (isRamified_iff.mpr ⟨hw, ?_⟩)
    rw [w.2]
    exact hv
  have hcard : Fintype.card (w.1.Completion →ₐ[v.Completion] ℂ) = 2 := by
    rw [AlgHom.card, hrank]
  have huniv : (Finset.univ : Finset (w.1.Completion →ₐ[v.Completion] ℂ)) = {φ₁, φ₂} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, hcard])).symm
  have key := Algebra.norm_eq_prod_embeddings v.Completion ℂ y
  rw [RingHom.algebraMap_toAlgebra] at key
  rw [key, huniv, Finset.prod_pair hne]
  show extensionEmbedding w.1 y * (starRingEnd ℂ) (extensionEmbedding w.1 y) = _
  rw [Complex.mul_conj', (isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _) y]
  rw [Complex.ofReal_pow]

end LocalNorm

section X2

open NumberField.InfinitePlace.Completion NumberField.TateGlobal IsDedekindDomain

private theorem isArchCompAt_of_local_comp_real
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : InfinitePlace ℚ) (u : ℂ) (a : ℤ)
    (hη : LanglandsTunnell.Converse.IsArchCompAt ℚ η v u a)
    (K : Type) [Field K] [NumberField K] (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K)
    (n : (w.Completion)ˣ → (v.Completion)ˣ)
    (hμ : ∀ x, archLocalChar μ w x = archLocalChar η v (n x))
    (hv : v.mult = 1) (hw : w.mult = 1)
    (hnorm : ∀ x : (w.Completion)ˣ,
      ‖((n x : (v.Completion)ˣ) : v.Completion)‖ = ‖(x : w.Completion)‖)
    (hemb : ∀ x : (w.Completion)ˣ,
      extensionEmbedding v ((n x : (v.Completion)ˣ) : v.Completion) =
        extensionEmbedding w (x : w.Completion)) :
    LanglandsTunnell.Converse.IsArchCompAt K μ w u a := by
  intro x
  rw [hμ x, hη (n x), hnorm x, hemb x, hv, hw]

private theorem isArchCompAt_of_local_comp_complex
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : InfinitePlace ℚ) (u : ℂ) (a : ℤ)
    (hη : LanglandsTunnell.Converse.IsArchCompAt ℚ η v u a)
    (K : Type) [Field K] [NumberField K] (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K)
    (n : (w.Completion)ˣ → (v.Completion)ˣ)
    (hμ : ∀ x, archLocalChar μ w x = archLocalChar η v (n x))
    (hv : v.mult = 1) (hw : w.mult = 2)
    (hnorm : ∀ x : (w.Completion)ˣ,
      ‖((n x : (v.Completion)ˣ) : v.Completion)‖ = ‖(x : w.Completion)‖ ^ 2)
    (hemb : ∀ x : (w.Completion)ˣ,
      extensionEmbedding v ((n x : (v.Completion)ˣ) : v.Completion) =
        ((‖(x : w.Completion)‖ ^ 2 : ℝ) : ℂ)) :
    LanglandsTunnell.Converse.IsArchCompAt K μ w u 0 := by
  intro x
  have hsq : ((‖(x : w.Completion)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have h0 : ‖(x : w.Completion)‖ ≠ 0 := norm_ne_zero_iff.mpr (Units.ne_zero x)
    exact_mod_cast pow_ne_zero 2 h0
  have hpow : (((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ (2 : ℂ)) ^ u =
      ((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ (2 * u) := by
    simpa using (Complex.cpow_mul_ofReal_nonneg (norm_nonneg (x : w.Completion)) 2 u).symm
  rw [hμ x, hη (n x), hnorm x, hemb x, hv, hw, div_self hsq, one_zpow, zpow_zero, mul_one,
    mul_one]
  push_cast
  rw [← hpow, Complex.cpow_two, one_mul]

end X2

section Closers

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.ComplexEmbedding
open NumberField.TateGlobal IsDedekindDomain LanglandsTunnell LanglandsTunnell.Converse

private theorem isReal_of_rat (v : InfinitePlace ℚ) : v.IsReal := by
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext q
  rw [ComplexEmbedding.conjugate_coe_eq, eq_ratCast, map_ratCast]

variable (K : Type) [Field K] [NumberField K]

private def extOfRat (v : InfinitePlace ℚ) (w : InfinitePlace K) : v.Extension K :=
  ⟨w, Subsingleton.elim _ _⟩

private theorem isArchCompAt_archOfParamR (P : RealArchParam) (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : InfinitePlace ℚ) (hq : IsArchCompAt ℚ η v P.centralExponent (P.centralSign.val : ℤ))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hS8 : ω = η.comp (GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
    (w : InfinitePlace K) (hw : w.IsReal) :
    IsArchCompAt K ω w (archOfParamR K P w hw).centralExponent ((archOfParamR K P w hw).centralSign.val : ℤ) := by
  have hv : v.IsReal := isReal_of_rat v
  refine isArchCompAt_of_local_comp_real η v _ _ hq K ω w (normUnit ℚ K v (extOfRat K v w)) ?_
    (mult_isReal ⟨v, hv⟩) (mult_isReal ⟨w, hw⟩) ?_ ?_
  · intro x
    rw [hS8]
    exact archLocalChar_comp_idelicNorm ℚ K η v (extOfRat K v w) x
  · intro x
    rw [← (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _),
      ← (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (x : w.Completion)]
    exact congrArg norm (extensionEmbedding_norm_of_isReal hv (extOfRat K v w) hw (x : w.Completion))
  · intro x
    exact extensionEmbedding_norm_of_isReal hv (extOfRat K v w) hw (x : w.Completion)

private theorem isArchCompAt_archOfParamC (P : RealArchParam) (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : InfinitePlace ℚ) (hq : IsArchCompAt ℚ η v P.centralExponent (P.centralSign.val : ℤ))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hS8 : ω = η.comp (GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
    (w : InfinitePlace K) (hw : w.IsComplex) :
    IsArchCompAt K ω w (archOfParamC K P w hw).centralExponent (archOfParamC K P w hw).centralTwist := by
  have hv : v.IsReal := isReal_of_rat v
  rw [archOfParamC_apply, RealArchParam.centralExponent_baseChange, RealArchParam.centralTwist_baseChange]
  refine isArchCompAt_of_local_comp_complex η v _ _ hq K ω w (normUnit ℚ K v (extOfRat K v w)) ?_
    (mult_isReal ⟨v, hv⟩) (mult_isComplex ⟨w, hw⟩) ?_ ?_
  · intro x
    rw [hS8]
    exact archLocalChar_comp_idelicNorm ℚ K η v (extOfRat K v w) x
  · intro x
    rw [← (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]
    refine (congrArg norm (extensionEmbedding_norm_of_isComplex hv (extOfRat K v w) hw (x : w.Completion))).trans ?_
    rw [Complex.norm_real]
    exact Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 2)
  · intro x
    exact extensionEmbedding_norm_of_isComplex hv (extOfRat K v w) hw (x : w.Completion)

end Closers

section StepOneSupply
open NumberField.StandardAddChar NumberField.InfinitePlace.Completion

private theorem psiQ_real_place (w : InfinitePlace ℚ) (x : InfiniteAdeleRing ℚ)
    (hx : ∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) :
    psiQ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)) := by
  show psiArch x * psiFin 0 = _
  rw [AddChar.map_zero_eq_one, mul_one, psiArch_apply,
    finprod_eq_single (fun v => psiArchPlace v (x v)) w (fun v hv => by
      show psiArchPlace v (x v) = 1
      rw [hx v hv, AddChar.map_zero_eq_one]),
    psiArchPlace_apply, extensionEmbeddingOfIsReal_apply]

end StepOneSupply

section LinkBlock
open NumberField.InfinitePlace.Completion NumberField.AdelicVolume
section Unitarize

private def unitCircleHom : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ‖(z : ℂ)‖) (div_ne_zero z.ne_zero (by exact_mod_cast norm_ne_zero_iff.mpr z.ne_zero))
  map_one' := by
    ext
    simp
  map_mul' z₁ z₂ := by
    ext
    simp only [Units.val_mk0, Units.val_mul, norm_mul, Complex.ofReal_mul]
    have h₁ : ((‖(z₁ : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr z₁.ne_zero
    have h₂ : ((‖(z₂ : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr z₂.ne_zero
    field_simp

private theorem unitCircleHom_apply (z : ℂˣ) : ((unitCircleHom z : ℂˣ) : ℂ) = (z : ℂ) / ‖(z : ℂ)‖ := rfl

variable (F : Type) [Field F] [NumberField F]

private def unitarize (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
  unitCircleHom.comp χ

private theorem norm_unitarize_apply (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ‖((unitarize F χ x : ℂˣ) : ℂ)‖ = 1 := by
  have hx : ‖((χ x : ℂˣ) : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (χ x).ne_zero
  simp [unitarize, unitCircleHom_apply, hx]

private theorem archLocalChar_unitarize (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F)
    (x : (w.Completion)ˣ) :
    ((archLocalChar (unitarize F χ) w x : ℂˣ) : ℂ) =
      ((archLocalChar χ w x : ℂˣ) : ℂ) / ‖((archLocalChar χ w x : ℂˣ) : ℂ)‖ := rfl

omit [NumberField F] in
private theorem norm_archComp_value (w : InfinitePlace F) (x : (w.Completion)ˣ) (u : ℂ) (a : ℤ) :
    ‖((‖(x : w.Completion)‖ : ℂ) ^ ((w.mult : ℂ) * u)) *
        (extensionEmbedding w (x : w.Completion) / (‖(x : w.Completion)‖ : ℂ)) ^ a‖ =
      ‖(x : w.Completion)‖ ^ ((w.mult : ℝ) * u.re) := by
  have hx : 0 < ‖(x : w.Completion)‖ := norm_pos_iff.mpr x.ne_zero
  have hphase : ‖extensionEmbedding w (x : w.Completion) / (‖(x : w.Completion)‖ : ℂ)‖ = 1 := by
    rw [norm_div, (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), Complex.norm_real,
      Real.norm_of_nonneg hx.le, div_self hx.ne']
  rw [norm_mul, norm_zpow, hphase, one_zpow, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hx : (0 : ℝ) < ‖(x : w.Completion)‖)]
  congr 1
  simp [Complex.mul_re]

private theorem isArchCompAt_unitarize (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F) (u : ℂ) (a : ℤ)
    (h : IsArchCompAt F χ w u a) : IsArchCompAt F (unitarize F χ) w (u - (u.re : ℂ)) a := by
  intro x
  have hx : 0 < ‖(x : w.Completion)‖ := norm_pos_iff.mpr x.ne_zero
  have hxC : ((‖(x : w.Completion)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [archLocalChar_unitarize, h x, norm_archComp_value, Complex.ofReal_cpow hx.le, mul_sub,
    Complex.cpow_sub _ _ hxC, div_mul_eq_mul_div]
  congr 2
  push_cast
  ring

private theorem continuous_unitCircleHom : Continuous unitCircleHom := by
  have hn : Continuous fun z : ℂˣ => ((‖(z : ℂ)‖ : ℝ) : ℂ) := Complex.continuous_ofReal.comp Units.continuous_val.norm
  have hne : ∀ z : ℂˣ, ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun z => by exact_mod_cast norm_ne_zero_iff.mpr z.ne_zero
  have hq : Continuous fun z : ℂˣ => ((z : ℂ) / ‖(z : ℂ)‖ : ℂ) := Units.continuous_val.div hn hne
  refine Units.continuous_iff.mpr ⟨hq, ?_⟩
  exact hq.inv₀ fun z => div_ne_zero z.ne_zero (hne z)

private theorem isAdmissibleTwist_unitarize (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hcls : IsIdeleClassChar (𝓞 F) F χ) (hcont : Continuous χ) : IsAdmissibleTwist F (unitarize F χ) := by
  refine ⟨fun q => ?_, continuous_unitCircleHom.comp hcont, norm_unitarize_apply F χ⟩
  show unitCircleHom (χ (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) q)) = 1
  rw [hcls q, map_one]

private theorem ideleNorm_archCentralUnit (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) :
    ideleNorm F (archCentralUnit F v₀ a) = ‖(a : v₀.Completion)‖ ^ v₀.mult := by
  refine (NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F
    (archCentralUnit F v₀ a)).trans ?_
  rw [Finset.prod_eq_single v₀ (fun w _ hw => by rw [archCentralUnit_fst_of_ne v₀ a hw, norm_one, one_pow])
    (fun h => (h (Finset.mem_univ _)).elim), archCentralUnit_fst_self, archCentralUnit_snd]
  rw [show (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(1 : FiniteAdeleRing (𝓞 F) F) v‖) = 1 from
    finprod_eq_one_of_forall_eq_one fun v => by
      show ‖(1 : v.adicCompletion F)‖ = 1
      exact norm_one, mul_one]

private theorem re_eq_one_of_isArchCompAt (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F) (u : ℂ) (a : ℤ)
    (h : IsArchCompAt F χ w u a)
    (hmod : ∀ x : (w.Completion)ˣ, ‖((χ (archCentralUnit F w x) : ℂˣ) : ℂ)‖ = ideleNorm F (archCentralUnit F w x)) :
    u.re = 1 := by
  haveI : CharZero w.Completion := (extensionEmbedding w).charZero
  set x₂ : (w.Completion)ˣ := Units.mk0 (2 : w.Completion) two_ne_zero with hx₂
  have h2 : ‖(x₂ : w.Completion)‖ = 2 := by
    rw [hx₂, Units.val_mk0, ← (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), map_ofNat]
    simp
  have hL : ‖((χ (archCentralUnit F w x₂) : ℂˣ) : ℂ)‖ = (2 : ℝ) ^ ((w.mult : ℝ) * u.re) := by
    have := congrArg norm (h x₂)
    rw [archLocalChar_apply] at this
    rw [this, norm_archComp_value F w x₂ u a, h2]
  have hR : ‖((χ (archCentralUnit F w x₂) : ℂˣ) : ℂ)‖ = (2 : ℝ) ^ ((w.mult : ℝ) * 1) := by
    rw [hmod x₂, ideleNorm_archCentralUnit F w x₂, h2, mul_one, Real.rpow_natCast]
  have hexp : (w.mult : ℝ) * u.re = (w.mult : ℝ) * 1 := by
    have hlog := congrArg Real.log (hL.symm.trans hR)
    rw [Real.log_rpow two_pos, Real.log_rpow two_pos] at hlog
    exact mul_right_cancel₀ (Real.log_pos one_lt_two).ne' hlog
  have hm : (w.mult : ℝ) ≠ 0 := by exact_mod_cast (InfinitePlace.mult_pos (w := w)).ne'
  exact mul_left_cancel₀ hm hexp

private theorem re_eq_zero_of_isArchCompAt_add_one (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F)
    (e : ℂ) (a : ℤ) (h : IsArchCompAt F χ w (e + 1) a)
    (hmod : ∀ x : (w.Completion)ˣ, ‖((χ (archCentralUnit F w x) : ℂˣ) : ℂ)‖ = ideleNorm F (archCentralUnit F w x)) :
    e.re = 0 := by
  have h1 := re_eq_one_of_isArchCompAt F χ w (e + 1) a h hmod
  rw [Complex.add_re, Complex.one_re] at h1
  linarith

private theorem isArchCompAt_unitarize_of_add_one (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F)
    (e : ℂ) (a : ℤ) (h : IsArchCompAt F χ w (e + 1) a)
    (hmod : ∀ x : (w.Completion)ˣ, ‖((χ (archCentralUnit F w x) : ℂˣ) : ℂ)‖ = ideleNorm F (archCentralUnit F w x)) :
    IsArchCompAt F (unitarize F χ) w e a := by
  have h0 := re_eq_zero_of_isArchCompAt_add_one F χ w e a h hmod
  have hb := isArchCompAt_unitarize F χ w (e + 1) a h
  have hshift : (e + 1) - (((e + 1).re : ℝ) : ℂ) = e := by
    rw [Complex.add_re, Complex.one_re, h0, zero_add]
    simp
  rwa [hshift] at hb

end Unitarize

section Beta

open AutomorphicForm NumberField.AdelicLevel

private theorem unitarize_apply_of_eq_inv_mul (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (N : ℕ) (hN : N ≠ 0) (b : ℂ) (hb : ‖b‖ = 1) (hraw : ((χ x : ℂˣ) : ℂ) = ((N : ℂ))⁻¹ * b) :
    ((unitarize ℚ χ x : ℂˣ) : ℂ) = b := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  show ((χ x : ℂˣ) : ℂ) / ‖((χ x : ℂˣ) : ℂ)‖ = b
  rw [hraw, norm_mul, norm_inv, hb, mul_one, Complex.norm_natCast, Complex.ofReal_inv, Complex.ofReal_natCast,
    div_eq_iff (inv_ne_zero hNC)]
  exact mul_comm _ _

private theorem det_heckeGen (p : HeightOneSpectrum (𝓞 ℚ)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 ℚ) ℚ p) = uniformizerIdele ℚ p := by
  apply Units.ext
  simp [heckeGen, heckeGenAt, uniformizerIdele, diagOne]

private theorem unitarize_centralChar_apply_uniformizerIdele
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (B : Set (AdeleRing (𝓞 ℚ) ℚ)) (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ D
        (fun N => NumberField.AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => NumberField.AdelicLevel.heckeGen (𝓞 ℚ) ℚ v) B) Φ.toRawCentral)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∉ R.exceptionalSet) (hb : ‖Φ.b p‖ = 1) :
    ((unitarize ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) (uniformizerIdele ℚ p) : ℂˣ) : ℂ)
      = Φ.b p := by
  refine unitarize_apply_of_eq_inv_mul _ _ (Ideal.absNorm p.asIdeal)
    (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot) (Φ.b p) hb ?_
  have h := R.centralChar_det_gen_eq_b hp (Subgroup.topEquiv.symm (uniformizerIdele ℚ p)) (det_heckeGen p).symm
  rw [HeckeEigensystem.toRawCentral_b] at h
  exact h

private theorem apply_uniformizerIdele_eq_pow_of_forall (K : Type) [Field K] [NumberField K]
    (Φ : HeckeEigensystem ℚ ℂ) (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (Tq T : Finset (HeightOneSpectrum (𝓞 ℚ))) (hTq : Tq ⊆ T)
    (hωT : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tq →
      ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) = (formalBaseChange ℚ K Φ).b 𝔓)
    (hη : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ T → ((η (uniformizerIdele ℚ p) : ℂˣ) : ℂ) = Φ.b p)
    (𝔓 : HeightOneSpectrum (𝓞 K)) (hT : 𝔓.under (𝓞 ℚ) ∉ T) :
    ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
      ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
  rw [hωT 𝔓 (fun h => hT (hTq h)), formalBaseChange_b, hη _ hT]

end Beta
end LinkBlock

section RawCharacter

variable (F : Type) [Field F] [NumberField F]

private theorem centralScalar_principal (u : Fˣ) :
    centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) u)
      = globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) u) :=
  Units.ext <| by
    simp [centralScalar, globalPoints, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map,
      Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]

private theorem continuous_centralScalar : Continuous (centralScalar (𝓞 F) F) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact ((continuous_pi fun _ : Fin 2 => (Units.continuous_val (M := AdeleRing (𝓞 F) F))).matrix_diagonal).congr
      fun z => (Matrix.scalar_apply (z : AdeleRing (𝓞 F) F)).symm
  · exact ((continuous_pi fun _ : Fin 2 =>
        (Units.continuous_val (M := AdeleRing (𝓞 F) F)).comp continuous_inv).matrix_diagonal).congr
      fun z => (Matrix.scalar_apply ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).symm

variable {F}

private theorem centralChar_eq_one_of_principal {pins : CarrierPins F} {Φ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F pins Φ) (z : pins.Z) (u : Fˣ)
    (hz : (z : (AdeleRing (𝓞 F) F)ˣ) = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) u) : R.centralChar z = 1 := by
  letI := pins.mS
  have hfn := ((lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z R.centralChar pins.D R.toFun).mp R.smoothCusp.1.1).1
  obtain ⟨g, hg⟩ := R.exists_ne_zero
  have h1 := hfn.central_transform z g
  rw [hz, centralScalar_principal F u, hfn.left_invariant] at h1
  have h2 : ((R.centralChar z : ℂˣ) : ℂ) * R.toFun g = 1 * R.toFun g := by rw [one_mul]; exact h1.symm
  exact Units.val_eq_one.mp (mul_right_cancel₀ hg h2)

private theorem continuous_centralChar_val {pins : CarrierPins F} {Φ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F pins Φ) (hR : Continuous R.toFun) :
    Continuous fun z : pins.Z => ((R.centralChar z : ℂˣ) : ℂ) := by
  obtain ⟨g, hg⟩ := R.exists_ne_zero
  have hform : (fun z : pins.Z => ((R.centralChar z : ℂˣ) : ℂ))
      = fun z : pins.Z => R.toFun (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) / R.toFun g :=
    funext fun z => R.centralChar_apply_eq z hg
  rw [hform]
  exact (hR.comp (((continuous_centralScalar F).comp continuous_subtype_val).mul continuous_const)).div_const _

end RawCharacter

section RawAtWindow

open NumberField.AdelicLevel

variable (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (B : Set (AdeleRing (𝓞 ℚ) ℚ)) (Φ : HeckeEigensystem ℚ ℂ)
  (R : SmoothCuspRealizationAt ℚ
    (productionPinsOf ℚ D
      (fun N => NumberField.AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
      (fun v => NumberField.AdelicLevel.heckeGen (𝓞 ℚ) ℚ v) B) Φ.toRawCentral)

private theorem raw_isIdeleClassChar :
    IsIdeleClassChar (𝓞 ℚ) ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) :=
  fun u => centralChar_eq_one_of_principal R _ u rfl

private theorem continuous_raw (hR : Continuous R.toFun) :
    Continuous (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) := by
  have hmk : Continuous fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup (AdeleRing (𝓞 ℚ) ℚ)ˣ)) :=
    continuous_id.subtype_mk _
  have hval : Continuous fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      (((R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) x : ℂˣ) : ℂ) :=
    (continuous_centralChar_val R hR).comp hmk
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp_rw [Units.val_inv_eq_inv_val]
  exact hval.inv₀ fun x => Units.ne_zero _

end RawAtWindow

section ExportsIRIC

open LanglandsTunnell

variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
private theorem ir_archOfParamR (P : RealArchParam)
    (hP : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) :
    ∀ (w : InfinitePlace K) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archOfParamR K P w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
        ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2) :=
  fun _ _ u₁ u₂ a₁ a₂ h => hP u₁ u₂ a₁ a₂ h

omit [NumberField K] in
private theorem ic_archOfParamC (P : RealArchParam)
    (hP : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) :
    ∀ (w : InfinitePlace K) (hw : w.IsComplex) (p q : ℕ), 1 ≤ p → 1 ≤ q →
      ¬ ((2 * ((archOfParamC K P w hw).u₁ - (archOfParamC K P w hw).u₂) = ((p + q : ℕ) : ℂ) ∧
            (archOfParamC K P w hw).k₁ - (archOfParamC K P w hw).k₂ = (p : ℤ) - q) ∨
          (2 * ((archOfParamC K P w hw).u₁ - (archOfParamC K P w hw).u₂) = -((p + q : ℕ) : ℂ) ∧
            (archOfParamC K P w hw).k₁ - (archOfParamC K P w hw).k₂ = (q : ℤ) - p)) := by
  intro w hw p q hp hq
  rw [archOfParamC_apply]
  cases P with
  | principal u₁ a₁ u₂ a₂ =>
    have hre := abs_lt.mp (hP u₁ u₂ a₁ a₂ rfl)
    simp only [RealArchParam.baseChange, sub_self, not_or, not_and]
    constructor
    · intro h1
      have h := congrArg Complex.re h1
      simp only [Complex.mul_re, Complex.add_re, Complex.natCast_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
        sub_zero, Nat.cast_add] at h
      intro _
      have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      linarith [hre.2]
    · intro h1
      have h := congrArg Complex.re h1
      simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.re_ofNat,
        Complex.im_ofNat, zero_mul, sub_zero, Nat.cast_add] at h
      intro _
      have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      linarith [hre.1]
  | discrete u k hk =>
    simp only [RealArchParam.baseChange, sub_self, mul_zero, not_or, not_and]
    constructor
    · intro h1
      exfalso
      have h : ((p + q : ℕ) : ℂ) = 0 := h1.symm
      have h' : p + q = 0 := by exact_mod_cast h
      omega
    · intro h1
      exfalso
      have h : ((p + q : ℕ) : ℂ) = 0 := by
        have := h1.symm
        rw [neg_eq_zero] at this
        exact this
      have h' : p + q = 0 := by exact_mod_cast h
      omega

end ExportsIRIC
end RegionB

section RegionC

open NumberField.AdelicLevel M4aHerbrand.GenuineDescent LanglandsTunnell.TateLocal

variable (K : Type) [Field K] [NumberField K]

private def finUnitAt (u : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    (w.adicCompletion K)ˣ :=
  Units.map ((finAdeleEval (𝓞 K) K w).toMonoidHom.comp (adeleFin (𝓞 K) K).toMonoidHom) u

private theorem finUnitAt_coe (u : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    (finUnitAt K u w : w.adicCompletion K) = ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w :=
  rfl

private theorem snd_apply_eq_prod_localUnit (W : Finset (HeightOneSpectrum (𝓞 K)))
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (hsupp : ∀ w, w ∉ W → ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w = 1)
    (v : HeightOneSpectrum (𝓞 K)) :
    ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
      (∏ w ∈ W, ((localUnit (𝓞 K) K w (finUnitAt K u w) : (FiniteAdeleRing (𝓞 K) K)ˣ) :
        FiniteAdeleRing (𝓞 K) K)) v := by
  classical
  rw [← finAdeleEval_apply (𝓞 K) K v (∏ w ∈ W, _), map_prod]
  simp only [finAdeleEval_apply]
  by_cases hv : v ∈ W
  · rw [Finset.prod_eq_single_of_mem v hv]
    · show _ = Function.update (1 : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) v
        (finUnitAt K u v : v.adicCompletion K) v
      rw [Function.update_self]
      rfl
    · intro w _ hwv
      show Function.update (1 : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) w
        (finUnitAt K u w : w.adicCompletion K) v = 1
      rw [Function.update_of_ne (Ne.symm hwv)]
      rfl
  · rw [hsupp v hv, Finset.prod_eq_one]
    intro w hw
    show Function.update (1 : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) w
      (finUnitAt K u w : w.adicCompletion K) v = 1
    rw [Function.update_of_ne (by rintro rfl; exact hv hw)]
    rfl

private theorem eq_prod_localUnit (W : Finset (HeightOneSpectrum (𝓞 K))) (u : (AdeleRing (𝓞 K) K)ˣ)
    (h1 : (u : AdeleRing (𝓞 K) K).1 = 1)
    (hsupp : ∀ w, w ∉ W → ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w = 1) :
    u = ∏ w ∈ W, Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K w (finUnitAt K u w)) := by
  classical

  have key1 : adeleArch (𝓞 K) K (∏ w ∈ W, ((Units.map (finIncl (𝓞 K) K)
      (localUnit (𝓞 K) K w (finUnitAt K u w)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) = 1 := by
    rw [map_prod]
    exact Finset.prod_eq_one fun w _ => rfl
  have key2 : adeleFin (𝓞 K) K (∏ w ∈ W, ((Units.map (finIncl (𝓞 K) K)
      (localUnit (𝓞 K) K w (finUnitAt K u w)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))
      = ∏ w ∈ W, ((localUnit (𝓞 K) K w (finUnitAt K u w) : (FiniteAdeleRing (𝓞 K) K)ˣ) :
          FiniteAdeleRing (𝓞 K) K) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun w _ => rfl
  have key3 : ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K)
      = ∏ w ∈ W, ((localUnit (𝓞 K) K w (finUnitAt K u w) : (FiniteAdeleRing (𝓞 K) K)ˣ) :
          FiniteAdeleRing (𝓞 K) K) :=
    Subtype.ext (funext fun v => snd_apply_eq_prod_localUnit K W u hsupp v)
  refine Units.ext (Prod.ext ?_ ?_)
  · rw [Units.coe_prod]
    exact h1.trans key1.symm
  · rw [Units.coe_prod]
    exact key3.trans key2.symm

private theorem apply_eq_prod_localChar (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (W : Finset (HeightOneSpectrum (𝓞 K))) (u : (AdeleRing (𝓞 K) K)ˣ)
    (h1 : (u : AdeleRing (𝓞 K) K).1 = 1)
    (hsupp : ∀ w, w ∉ W → ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w = 1) :
    μ u = ∏ w ∈ W, localChar μ w (finUnitAt K u w) := by
  conv_lhs => rw [eq_prod_localUnit K W u h1 hsupp]
  rw [map_prod]
  exact Finset.prod_congr rfl fun w _ => rfl

private theorem prod_epsS_eq_one (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (W : Finset (HeightOneSpectrum (𝓞 K))) (u : (AdeleRing (𝓞 K) K)ˣ)
    (h1 : (u : AdeleRing (𝓞 K) K).1 = 1)
    (hsupp : ∀ w, w ∉ W → ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w = 1)
    (hval : ∀ w ∈ W, Valued.v ((finUnitAt K u w : (w.adicCompletion K)ˣ) : w.adicCompletion K) = 1)
    (hcancel : ∀ v ∈ W, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      localChar μ v t * epsS v t = 1)
    (hμ : μ u = 1) :
    ∏ w ∈ W, epsS w (finUnitAt K u w) = 1 := by
  have hprod : (∏ w ∈ W, localChar μ w (finUnitAt K u w)) * ∏ w ∈ W, epsS w (finUnitAt K u w) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun w hw => hcancel w hw _ (hval w hw)
  rwa [← apply_eq_prod_localChar K μ W u h1 hsupp, hμ, one_mul] at hprod

private theorem not_exists_pullback (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (W : Finset (HeightOneSpectrum (𝓞 K))) (u : (AdeleRing (𝓞 K) K)ˣ)
    (h1 : (u : AdeleRing (𝓞 K) K).1 = 1)
    (hsupp : ∀ w, w ∉ W → ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w = 1)
    (hval : ∀ w ∈ W, Valued.v ((finUnitAt K u w : (w.adicCompletion K)ˣ) : w.adicCompletion K) = 1)
    (hN : (genuineBaseChange ℚ K).idelicNorm u = 1)
    (hcancel : ∀ v ∈ W, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      localChar μ v t * epsS v t = 1)
    (hne : ∏ w ∈ W, epsS w (finUnitAt K u w) ≠ 1) :
    ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) := by
  rintro ⟨η, hη, hagree⟩
  have hμη : μ = η.comp (genuineBaseChange ℚ K).idelicNorm :=
    LanglandsTunnell.RankinSelberg.eq_comp_idelicNorm_of_forall_uniformizerIdele_eq_pow_inertiaDeg K μ
      hμ.1 hμ.2.1 η hη.1 hη.2.1 hagree
  have hμu : μ u = 1 := by
    rw [hμη, MonoidHom.comp_apply, hN, map_one]
  exact hne (prod_epsS_eq_one K μ epsS W u h1 hsupp hval hcancel hμu)

section StepOne

open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

private theorem realization_of_window (Φ : HeckeEigensystem ℚ ℂ)
    (hΦ : IsArithGenuineCuspRealizable ℚ (productionPinsGeneral ℚ) Φ) :
    ∃ R : SmoothCuspRealizationAt ℚ
        (productionPinsOf ℚ
          (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1 / 2 : ℝ) 1 (1 / 2) 2)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
          (adelicBox ℚ))
        Φ.toRawCentral,
      Continuous R.toFun :=
  hΦ

private theorem coversModCentre_window :
    CoversModCentre ℚ
      (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1 / 2 : ℝ) 1 (1 / 2) 2) :=
  AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat

private theorem realization_of_window' (Φ : HeckeEigensystem ℚ ℂ)
    (hΦ : IsArithGenuineCuspRealizable ℚ (productionPinsGeneral ℚ) Φ) :
    ∃ R : SmoothCuspRealizationAt ℚ
        (productionPinsOf ℚ
          (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1 / 2 : ℝ) 1 (1 / 2) 2)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
          (adelicBox ℚ))
        Φ.toRawCentral,
      IsGenuineCuspRealizationAt ℚ _ Φ.toRawCentral R :=
  hΦ

end StepOne

end RegionC

end EBCSol
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_isNicePinned_rsDatum_isArchCompAt_of_isArithGenuineCuspRealizable.EBCSol"

open scoped Classical in
open LanglandsTunnell LanglandsTunnell.RankinSelberg in
open EBCSol in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hΦ : AutomorphicForm.IsArithGenuineCuspRealizable ℚ
      (AutomorphicForm.productionPinsGeneral ℚ) Φ)
    (SQ₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (hb : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), p ∉ SQ₀ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (Tq : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωT : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tq →
      IsUnramifiedCharAt ω 𝔓 ∧
        ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) = (formalBaseChange ℚ K Φ).b 𝔓) :
    ∃ (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))), SQ₀ ⊆ SQ ∧
    ∃ (SK : Finset (HeightOneSpectrum (𝓞 K))),
    (∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ SK ↔ 𝔓.under (𝓞 ℚ) ∈ SQ) ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1) ∧
    ∃
      (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
      (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
      (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
      (A Ad : (↥SK → ℤ) → ℂ),
      (∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ Tq → 𝔓 ∈ SK) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex) (p q : ℕ), 1 ≤ p → 1 ≤ q →
        ¬ ((2 * ((archC w hw).u₁ - (archC w hw).u₂) = ((p + q : ℕ) : ℂ) ∧
              (archC w hw).k₁ - (archC w hw).k₂ = (p : ℤ) - q) ∨
            (2 * ((archC w hw).u₁ - (archC w hw).u₂) = -((p + q : ℕ) : ℂ) ∧
              (archC w hw).k₁ - (archC w hw).k₂ = (q : ℤ) - p))) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal),
        IsArchCompAt K ω w (archR w hw).centralExponent ((archR w hw).centralSign.val : ℤ)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex),
        IsArchCompAt K ω w (archC w hw).centralExponent (archC w hw).centralTwist) ∧
      (∀ v ∈ SK, Continuous ⇑(epsS v)) ∧
      (∃ C : ℝ, ∀ n : ↥SK → ℤ, ‖A n‖ ≤ C ∧ ‖Ad n‖ ≤ C) ∧
      (∃ n₀ : ↥SK → ℤ, ∀ n : ↥SK → ℤ, (∃ v, n v < n₀ v) → A n = 0 ∧ Ad n = 0) ∧
      (A ≠ 0) ∧
      (∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsAdmissibleTwist K μ →
        (∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
          localChar μ v u * epsS v u = 1) →
        ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
          (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
          (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
          (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
          (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
          (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
          IsNicePinned
            (rsDatum ℚ SQ Φ.a Φ.b
              (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
              (twistedGammaR K archR uR aR) (twistedGammaC K archR archC uR aR uC kC)
              (twistedGammaR K (fun w hw => (archR w hw).dual) (fun w hw => -uR w hw) aR)
              (twistedGammaC K (fun w hw => (archR w hw).dual) (fun w hw => (archC w hw).dual)
                (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)))
            (sPart K SK A μ) (sPartDual K SK Ad μ)
            (pinnedRootNumber K (formalBaseChange ℚ K Φ) μ SK archR archC uR aR uC kC)
            (finiteConductor K μ SK)) := by

  haveI := subsingleton_algebra_ratRingOfIntegers (𝓞 K)
  obtain rfl : (‹_› : Algebra (𝓞 ℚ) (𝓞 K)) = canonAlg K := Subsingleton.elim _ _

  obtain ⟨R, hR⟩ := realization_of_window Φ hΦ

  obtain ⟨S, archRQ, Cfin, hexc, hC11, hpr, hnd, hcompQ, hpar⟩ :=
    LanglandsTunnell.exists_realArchParam_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_continuous_realization
      Φ R hR
  set vQ : InfinitePlace ℚ := default
  have hvQ : vQ.IsReal := isReal_of_rat vQ
  set P : RealArchParam := archRQ vQ hvQ
  set η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ :=
    unitarize ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom)

  obtain ⟨p₀, ⟨w₀, hw₀p⟩, w₂, _hp₀, hw₀₂, _hf₀, _he₀⟩ :=
    NumberField.exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one
      K (by omega) (SQ₀ ∪ Tq ∪ levelPrimes Φ ∪ ramQ K ∪ S)
  set SQ : Finset (HeightOneSpectrum (𝓞 ℚ)) := SQ₀ ∪ Tq ∪ levelPrimes Φ ∪ ramQ K ∪ S ∪ {p₀} with hSQdef
  have hSQ₀ : SQ₀ ⊆ SQ := fun p hp => by simp [hSQdef, hp]
  have hTq_SQ : Tq ⊆ SQ := fun p hp => by simp [hSQdef, hp]
  have hbSQ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1 :=
    fun p hp => hb p (fun h => hp (by simp [hSQdef, h]))
  have hSQ_C1 : (∀ p : HeightOneSpectrum (𝓞 ℚ), Φ.level ≤ p.asIdeal → p ∈ SQ) ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
        Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1 :=
    ⟨fun p hp => by simp [hSQdef, mem_levelPrimes Φ p hp],
     fun 𝔓 h => ramificationIdx_eq_one_of_under_notMem_ramQ 𝔓 (fun hr => h (by simp [hSQdef, hr]))⟩
  have hS_SQ : S ⊆ SQ := fun x hx => by simp [hSQdef, hx]
  have hp₀ : p₀ ∈ SQ := by simp [hSQdef]
  have hE : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ Tq → 𝔓 ∈ fibreFinset K SQ :=
    fun 𝔓 h => (mem_fibreFinset SQ 𝔓).mpr (by simp [hSQdef, h])
  refine ⟨SQ, hSQ₀, fibreFinset K SQ, mem_fibreFinset SQ, hbSQ, ?_⟩

  obtain ⟨u, huinf, husupp, huunit, hw₀ne', hNu⟩ :=
    LanglandsTunnell.RankinSelberg.exists_unitIdele_over_idelicNorm_eq_one_and_apply_ne_one_of_ne K p₀ ⟨w₀, hw₀p⟩ w₂ hw₀₂
  have hw₀ne : ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w₀ ≠ 1 := hw₀ne'
  have hw₀ : w₀ ∈ fibreFinset K SQ := (mem_fibreFinset SQ w₀).mpr (hw₀p ▸ hp₀)

  obtain ⟨c₀, -, hc₀2, ξ, hξc, -, hξH, hξne⟩ :=
    LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt_apply_ne K w₀ (finUnitAt K u w₀)
      (by rw [finUnitAt_coe]; exact huunit w₀)
      (fun h => hw₀ne (by rw [← finUnitAt_coe, h, Units.val_one])) 1 2

  let c₀fun : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun p => if p = p₀ then c₀ else 0

  obtain ⟨bQ, hbQ⟩ := NormPin.exists_levelExp Φ.level Φ.level_ne_bot

  obtain ⟨χA, kχ, c', epsS, hχA, hχoff, hkχ, hχinf, hkfl, hεcont, hεH, hdc', hεprod', hεoff, hεon⟩ :=
    NormPin.exists_chiA_epsS K _hdeg SQ (fibreFinset K SQ) (fun w hw => (mem_fibreFinset SQ w).mp hw)
      (fun v => max 2 (4 * (FractionalIdeal.count K v
          ((Φ.level.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) +
        LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K v) + 1)).toNat)
      (fun p => 6 * ((bQ p : ℤ) + 3 * (2 * ((∑ᶠ w ∈ primeFibre ℚ K p,
              ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal : ℤ) *
                ((Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal : ℤ) *
                    (2 * ((52 : ℤ) + 3 * (c₀fun p : ℤ)) +
                      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 2) +
                  (c₀fun p : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1)) +
            ((52 : ℤ) + 3 * (c₀fun p : ℤ)))) + 3) + 7)
      w₀ hw₀ ξ hξc c₀ hξH

  have hεprod : ∏ w ∈ fibreFinset K SQ, epsS w (finUnitAt K u w) ≠ 1 := by
    have hχu : ∏ w ∈ fibreFinset K SQ,
        localChar (χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w (finUnitAt K u w) = 1 := by
      rw [← apply_eq_prod_localChar K _ (fibreFinset K SQ) u huinf
        (fun w hw => husupp w fun h => hw ((mem_fibreFinset SQ w).mpr (h ▸ hp₀))),
        MonoidHom.comp_apply, hNu, map_one]
    rw [hεprod' (finUnitAt K u), hχu, inv_one, one_mul]
    exact hξne

  obtain ⟨Ad, n₀Ad, hsupp, hA09⟩ :=
    LanglandsTunnell.Converse.exists_sPartDual_eq_of_forall_cancel_units K (fibreFinset K SQ) ω hω epsS

  have hq : IsArchCompAt ℚ η vQ P.centralExponent (P.centralSign.val : ℤ) :=
    isArchCompAt_unitarize_of_add_one ℚ _ vQ P.centralExponent _ (hcompQ vQ hvQ) fun x =>
      AutomorphicForm.SmoothCuspRealizationAt.norm_centralChar_eq_ideleNorm_of_forall_norm_b_eq_one ℚ _ _ Φ R hR SQ₀ hb
        (Subgroup.topEquiv.symm (NumberField.AdelicVolume.archCentralUnit ℚ vQ x))
  have hηadm : IsAdmissibleTwist ℚ η :=
    isAdmissibleTwist_unitarize ℚ _ (raw_isIdeleClassChar _ _ Φ R) (continuous_raw _ _ Φ R hR)
  have hηval : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      ((η (uniformizerIdele ℚ p) : ℂˣ) : ℂ) = Φ.b p :=
    fun p hp => unitarize_centralChar_apply_uniformizerIdele _ _ Φ R p (fun hx => hp (hS_SQ (hexc hx))) (hbSQ p hp)
  have hS8 : ω = η.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm :=
    LanglandsTunnell.RankinSelberg.eq_comp_idelicNorm_of_forall_under_notMem_uniformizerIdele_eq_pow_inertiaDeg
      K ω hω.1 hω.2.1 η hηadm.1 hηadm.2.1 SQ
      (fun 𝔓 hT _ _ => apply_uniformizerIdele_eq_pow_of_forall K Φ ω η Tq SQ hTq_SQ
        (fun 𝔔 h => (hωT 𝔔 h).2) hηval 𝔓 hT)
  have hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archOfParamR K P w hw).centralExponent ((archOfParamR K P w hw).centralSign.val : ℤ) :=
    fun w hw => isArchCompAt_archOfParamR K P η vQ hq ω hS8 w hw
  have hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archOfParamC K P w hw).centralExponent (archOfParamC K P w hw).centralTwist :=
    fun w hw => isArchCompAt_archOfParamC K P η vQ hq ω hS8 w hw

  refine ⟨archOfParamR K P, archOfParamC K P, epsS, deltaZero K (fibreFinset K SQ), Ad, hE,
    ir_archOfParamR K P (hnd vQ hvQ), ic_archOfParamC K P (hpr vQ hvQ), hωR, hωC,
    fun v _ => hεcont v,
    ⟨max 1 ‖Ad n₀Ad‖, fun n => ⟨(deltaZero_norm_le K (fibreFinset K SQ) n).trans (le_max_left _ _),
      (norm_le_of_single_support Ad n₀Ad hsupp n).trans (le_max_right _ _)⟩⟩,
    ⟨fun v => min 0 (n₀Ad v), fun n ⟨v, hv⟩ =>
      ⟨deltaZero_eq_zero_of_neg K (fibreFinset K SQ) n ⟨v, lt_of_lt_of_le hv (min_le_left _ _)⟩,
       eq_zero_of_lt_of_single_support K (fibreFinset K SQ) Ad n₀Ad hsupp n
         ⟨v, lt_of_lt_of_le hv (min_le_right _ _)⟩⟩⟩,
    deltaZero_ne_zero K (fibreFinset K SQ), ?_⟩
  intro μ hμ hcancel uR aR uC kC hcR hcC
  have hoff := not_exists_pullback K μ hμ epsS (fibreFinset K SQ) u huinf
    (fun w hw => husupp w fun h => hw ((mem_fibreFinset SQ w).mpr (h ▸ hp₀)))
    (fun w _ => by rw [finUnitAt_coe]; exact huunit w) hNu hcancel hεprod
  have hdepth : ∀ w : ↥(fibreFinset K SQ),
      4 * (FractionalIdeal.count K w.1
            ((Φ.level.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w.1) + 1) ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w.1 (localChar μ w.1) := fun w => by
    rw [(hA09 μ hμ hcancel).1 w.1 w.2,
      LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K w.1 (hεH w.1 w.2)]
    have h1 : max 2 (4 * (FractionalIdeal.count K w.1
            ((Φ.level.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w.1) + 1)).toNat ≤
        c' w.1 := hdc' w.1 w.2
    omega
  have harch : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), archRQ w hw = P := fun w hw => by
    obtain rfl : w = vQ := Subsingleton.elim _ _
    rfl

  obtain ⟨ωQ, hωQ⟩ :=
    LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three K _hdeg μ hμ

  have hν : ∀ p ∈ SQ, ∀ w ∈ primeFibre ℚ K p, ∃ c : ℕ, c ≤ c₀fun p ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w
        (NumberField.TateGlobal.localChar
          (μ * (χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)⁻¹) w) c := by
    intro p hp w hw
    have hwp : w.under (𝓞 ℚ) = p := (mem_primeFibre (F := ℚ) p w).mp hw
    have hwSK : w ∈ fibreFinset K SQ := (mem_fibreFinset SQ w).mpr (hwp ▸ hp)
    by_cases hw0 : w = w₀
    · subst hw0
      refine ⟨c₀, ?_, NormPin.hasConductorExponentAt_of_cancel_aux K μ _ _ (epsS _) ξ c₀ hξH hεon (hcancel _ hwSK)⟩
      have hpp : p = p₀ := hwp.symm.trans hw₀p
      simp only [c₀fun, hpp, if_true, le_refl]
    · exact ⟨0, Nat.zero_le _,
        NormPin.hasConductorExponentAt_zero_of_cancel K μ _ w (epsS w) (hεoff w hw0) (hcancel w hwSK)⟩

  have hC1 :=
    LanglandsTunnell.RankinSelberg.isNicePinned_rsDatum_of_centralInduced_of_localWhittaker_of_not_exists_eq_pow_inertiaDeg_of_normPin_archTrivial
      K _hdeg Φ SQ hSQ_C1 hbSQ ha (fibreFinset K SQ) (mem_fibreFinset SQ) P S hS_SQ
      ⟨R, hR, Cfin, hexc, hC11, by simpa only [harch] using hpr, by simpa only [harch] using hnd,
        by simpa only [harch] using hcompQ, fun par => by
          obtain ⟨φ, Wr, k, hiso, hne, hloc, hrest⟩ := hpar par
          exact ⟨φ, Wr, k, hiso, hne, fun p _ => hloc p, by simpa only [harch] using hrest⟩⟩
      Tq ω hω hωT hE hωR hωC μ hμ hoff χA hχA hχoff kχ hkχ hχinf c₀fun hν bQ (fun p _ => hbQ p) hkfl hdepth
      ωQ hωQ uR aR uC kC hcR hcC
  rw [sPart_deltaZero K (fibreFinset K SQ) μ]
  exact (hA09 μ hμ hcancel).2 ▸ hC1

end
end S_LanglandsTunnell_RankinSelberg_exists_isNicePinned_rsDatum_isArchCompAt_of_isArithGenuineCuspRealizable
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_isNicePinned_rsDatum_isArchCompAt_of_isArithGenuineCuspRealizable (solution)
