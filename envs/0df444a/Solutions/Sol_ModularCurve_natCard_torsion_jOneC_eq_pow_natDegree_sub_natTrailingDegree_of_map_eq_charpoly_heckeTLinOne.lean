-- Prove2me | solution 1 for ModularCurve.natCard_torsion_jOneC_eq_pow_natDegree_sub_natTrailingDegree_of_map_eq_charpoly_heckeTLinOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4093013b-1019-5ecb-84c4-642af13a4b27

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Theorems.Thm_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective
import Theorems.Thm_ModularCurve_natCard_torsion_jOneC_eq_natCard_regularDifferentials_x1FunctionFieldC_coeff_mul_eq_pow
import Theorems.Thm_LinearMap_natCard_setOf_apply_eq_frobeniusSemilinear_eq_pow_finrank_iInf_range_pow
import Theorems.Thm_CuspForm_qCoeff_heckeTLinOne
import Theorems.Thm_CuspForm_heckeTLinOne_slashOfMemGamma0
import Theorems.Thm_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_torsion_jOneC_eq_pow_natDegree_sub_natTrailingDegree_of_map_eq_charpoly_heckeTLinOne
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.jqNModC_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D"
p2m_attr_erase "simp" "ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq"
p2m_attr_erase "simp" "CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ"
p2m_attr_erase "simp" "ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

namespace G1PRank

open scoped TensorProduct ModularForm MatrixGroups
p2m_open "CongruenceSubgroup ModularForm ModularFormClass ModularCurve~IsCusp AlgebraicCurve Polynomial"

section Generic

theorem forall_eq_zero_of_forall_baseField_eq_zero {K₀ K : Type*} [Field K₀] [Field K] [Algebra K₀ K]
    {ι S : Type*} [Fintype ι] (v : ι → S → K₀)
    (hv : ∀ d : ι → K₀, (∀ s, ∑ i, d i * v i s = 0) → ∀ i, d i = 0)
    (g : ι → K) (hg : ∀ s, ∑ i, g i * algebraMap K₀ K (v i s) = 0) : ∀ i, g i = 0 := by
  classical
  let B := Module.Basis.ofVectorSpace K₀ K
  have key : ∀ l, ∀ i, B.repr (g i) l = 0 := by
    intro l
    refine hv (fun i => B.repr (g i) l) ?_
    intro s
    have h1 : B.repr (∑ i, g i * algebraMap K₀ K (v i s)) l = 0 := by
      rw [hg s, map_zero, Finsupp.zero_apply]
    rw [map_sum, Finsupp.finsetSum_apply] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (g i), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  intro i
  rw [← B.repr.map_eq_zero_iff]
  ext l
  exact key l i

theorem forall_eq_zero_of_forall_intRel {ι S : Type*} [Fintype ι] (v : ι → S → ℤ)
    (H : ∀ m : ι → ℤ, (∀ s, (∑ i, m i * v i s : ℤ) = 0) → ∀ i, m i = 0)
    (g : ι → ℂ) (hg : ∀ s, ∑ i, g i * (v i s : ℂ) = 0) : ∀ i, g i = 0 := by
  classical
  refine forall_eq_zero_of_forall_baseField_eq_zero (K₀ := ℚ) (fun i s => (v i s : ℚ)) ?_ g ?_
  · intro d hd i
    set D : ℕ := ∏ i, (d i).den with hD
    have hD0 : (D : ℚ) ≠ 0 := by
      rw [hD]
      exact_mod_cast Finset.prod_ne_zero_iff.mpr fun i _ => (d i).den_nz
    have hint : ∀ i, ∃ m : ℤ, (D : ℚ) * d i = m := by
      intro i
      obtain ⟨c, hc⟩ : (d i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      refine ⟨c * (d i).num, ?_⟩
      rw [hc]
      push_cast
      rw [mul_comm ((d i).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
    choose m hm using hint
    have h1 : ∀ s, (∑ i, m i * v i s : ℤ) = 0 := by
      intro s
      have h : ((∑ i, m i * v i s : ℤ) : ℚ) = D * ∑ i, d i * v i s := by
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hm i]
        ring
      rw [hd s, mul_zero] at h
      exact_mod_cast h
    have hmi : m i = 0 := H m h1 i
    have h6 : (D : ℚ) * d i = 0 := by rw [hm i, hmi, Int.cast_zero]
    exact (mul_eq_zero.mp h6).resolve_left hD0
  · intro s
    simp_rw [map_intCast]
    exact hg s

theorem natTrailingDegree_map_of_injective {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : Function.Injective f) (P : R[X]) :
    (P.map f).natTrailingDegree = P.natTrailingDegree := by
  by_cases hP : P = 0
  · subst hP; simp
  have hPf : P.map f ≠ 0 := fun h => hP (Polynomial.map_injective f hf (by rw [h, Polynomial.map_zero]))
  refine le_antisymm ?_ ?_
  · apply natTrailingDegree_le_of_ne_zero
    rw [coeff_map]
    intro h
    exact (trailingCoeff_nonzero_iff_nonzero.mpr hP) (hf (h.trans (map_zero f).symm))
  · apply le_natTrailingDegree hPf
    intro m hm
    rw [coeff_map, coeff_eq_zero_of_lt_natTrailingDegree hm, map_zero]

theorem finrank_iInf_range_pow_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (φ : Module.End K V) :
    Module.finrank K ↥(⨅ n : ℕ, LinearMap.range (φ ^ n)) =
      φ.charpoly.natDegree - φ.charpoly.natTrailingDegree := by
  have h1 := LinearMap.finrank_maxGenEigenspace_zero_eq φ
  have hV : φ.maxGenEigenspace 0 = ⨆ n : ℕ, LinearMap.ker (φ ^ n) := by
    simp [← Module.End.iSup_genEigenspace_eq, Module.End.genEigenspace_nat]
  have hc : IsCompl (⨆ n : ℕ, LinearMap.ker (φ ^ n)) (⨅ n : ℕ, LinearMap.range (φ ^ n)) :=
    LinearMap.isCompl_iSup_ker_pow_iInf_range_pow φ
  have h2 := Submodule.finrank_add_eq_of_isCompl hc
  rw [← hV, h1, ← LinearMap.charpoly_natDegree φ] at h2
  omega

end Generic

section Lattice

variable (M : ℕ) [NeZero M]

abbrev S2 : Type := CuspForm (Gamma1 M) 2

lemma one_mem_strictPeriods :
    (1 : ℝ) ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

lemma hasSum_qCoeff (f : S2 M) (τ : UpperHalfPlane) :
    HasSum (fun m ↦ qCoeff f m * Function.Periodic.qParam 1 τ ^ m) (f τ) := by
  haveI : Fact (IsCusp OnePoint.infty ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
  have := UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods M))
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ
  first | simpa only [smul_eq_mul] using this | simpa only [smul_eq_mul, qCoeff] using this | exact this

lemma eq_zero_of_forall_qCoeff_eq_zero (f : S2 M) (h : ∀ n, qCoeff f n = 0) : f = 0 := by
  refine DFunLike.ext _ _ fun τ => ?_
  have hs := hasSum_qCoeff M f τ
  have hz : (fun m ↦ qCoeff f m * Function.Periodic.qParam 1 τ ^ m) = fun _ => 0 := by
    funext m
    rw [h m, zero_mul]
  rw [hz] at hs
  simpa using hs.unique hasSum_zero

def qCoeffLin (n : ℕ) : S2 M →ₗ[ℂ] ℂ where
  toFun f := qCoeff f n
  map_add' f g := by
    simp only [qCoeff, CuspForm.coe_add]
    rw [ModularForm.qExpansion_add one_pos (one_mem_strictPeriods M) f g, map_add]
  map_smul' c f := by
    simp only [qCoeff, CuspForm.IsGLPos.coe_smul, RingHom.id_apply, smul_eq_mul]
    rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M) c f]
    simp

@[scoped simp] lemma qCoeffLin_apply (n : ℕ) (f : S2 M) : qCoeffLin M n f = qCoeff f n := rfl

theorem sl_slash (f : UpperHalfPlane → ℂ) (k : ℤ) (γ : SL(2, ℤ)) :
    f ∣[k] γ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) := rfl

def dsSet : Set (S2 M) :=
  {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2 |
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ∀ n : ℕ,
      ModularFormClass.qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) n ∈ Set.range ((↑) : ℤ → ℂ)}

abbrev Lat : Submodule ℤ (S2 M) :=
  Submodule.span ℤ
    {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2 |
      ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ∀ n : ℕ,
        ModularFormClass.qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) n ∈ Set.range ((↑) : ℤ → ℂ)}

lemma Lat_eq : Lat M = Submodule.span ℤ (dsSet M) := rfl

variable {M}

def qCoeffSlashLin {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (n : ℕ) : S2 M →ₗ[ℂ] ℂ :=
  qCoeffLin M n ∘ₗ CuspForm.slashLinOfMemGamma0 M 2 hγ

lemma qCoeffSlashLin_apply {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (n : ℕ) (f : S2 M) :
    qCoeffSlashLin hγ n f = qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) n := rfl

theorem exists_int_qCoeff_slash_of_mem {f : S2 M} (hf : f ∈ Lat M) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 M) (n : ℕ) :
    ∃ m : ℤ, qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) n = (m : ℂ) := by
  rw [Lat_eq] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨m, hm⟩ := hx γ hγ n
      exact ⟨m, hm.symm⟩
  | zero => exact ⟨0, by rw [← qCoeffSlashLin_apply hγ, map_zero, Int.cast_zero]⟩
  | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      rw [← qCoeffSlashLin_apply hγ, map_add, qCoeffSlashLin_apply, qCoeffSlashLin_apply, ha, hb,
        Int.cast_add]
  | smul a x _ hx =>
      obtain ⟨b, hb⟩ := hx
      refine ⟨a * b, ?_⟩
      rw [← qCoeffSlashLin_apply hγ, map_zsmul, qCoeffSlashLin_apply, hb, zsmul_eq_mul, Int.cast_mul]

theorem exists_int_qCoeff_of_mem {f : S2 M} (hf : f ∈ Lat M) (n : ℕ) :
    ∃ m : ℤ, qCoeff f n = (m : ℂ) := by
  obtain ⟨m, hm⟩ := exists_int_qCoeff_slash_of_mem hf (Subgroup.one_mem (Gamma0 M)) n
  refine ⟨m, ?_⟩
  rw [← hm, sl_slash, map_one, SlashAction.slash_one]

def coefZ (f : ↥(Lat M)) (n : ℕ) : ℤ := (exists_int_qCoeff_of_mem f.2 n).choose

theorem coefZ_spec (f : ↥(Lat M)) (n : ℕ) : qCoeff (f : S2 M) n = (coefZ f n : ℂ) :=
  (exists_int_qCoeff_of_mem f.2 n).choose_spec

section Hecke

variable {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M)

include hp hpM in

theorem exists_qCoeff_heckeT_eq {f : S2 M} (hf : f ∈ Lat M) (n : ℕ) :
    ∃ m : ℤ, qCoeff (CuspForm.heckeTLinOne 2 hp hpM f) n = qCoeff f (p * n) + p * m := by
  obtain ⟨σ, hσ⟩ := CuspForm.exists_isDiamondLift_of_coprime (M := M)
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
  obtain ⟨m, hm⟩ := exists_int_qCoeff_slash_of_mem hf hσ.1 (n / p)
  refine ⟨if p ∣ n then m else 0, ?_⟩
  rw [CuspForm.qCoeff_heckeTLinOne 2 hp hpM f n, CuspForm.coe_diamondLinOne_apply hσ,
    ← sl_slash]
  have h2 : ((2 : ℤ) - 1) = 1 := by norm_num
  rw [h2, zpow_one]
  split_ifs with h
  · rw [hm]
  · simp

include hp hpM in

theorem heckeT_mem_dsSet {f : S2 M} (hf : f ∈ Lat M) : CuspForm.heckeTLinOne 2 hp hpM f ∈ dsSet M := by
  intro γ hγ n
  obtain ⟨σ, hσ⟩ := CuspForm.exists_isDiamondLift_of_coprime (M := M)
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
  have hγσ : γ * σ ∈ Gamma0 M := Subgroup.mul_mem _ hγ hσ.1
  obtain ⟨m₁, hm₁⟩ := exists_int_qCoeff_slash_of_mem hf hγ (p * n)
  obtain ⟨m₂, hm₂⟩ := exists_int_qCoeff_slash_of_mem hf hγσ (n / p)
  refine ⟨m₁ + p * (if p ∣ n then m₂ else 0), ?_⟩
  change _ = qCoeff (⇑(CuspForm.slashOfMemGamma0 M 2 hγ (CuspForm.heckeTLinOne 2 hp hpM f))) n
  rw [← CuspForm.heckeTLinOne_slashOfMemGamma0 2 hp hpM hγ f,
    CuspForm.qCoeff_heckeTLinOne 2 hp hpM _ n,
    CuspForm.coe_diamondLinOne_apply hσ (CuspForm.slashOfMemGamma0 M 2 hγ f),
    CuspForm.coe_slashOfMemGamma0, ← SlashAction.slash_mul, ← map_mul]
  have h2 : ((2 : ℤ) - 1) = 1 := by norm_num
  rw [h2, zpow_one]
  change (↑(m₁ + ↑p * if p ∣ n then m₂ else 0) : ℂ) =
    qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) (p * n) +
      ↑p * (if p ∣ n then qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] (γ * σ)) (n / p) else 0)
  rw [hm₁, hm₂]
  push_cast
  split_ifs <;> simp

include hp hpM in
theorem heckeT_mem_Lat {f : S2 M} (hf : f ∈ Lat M) : CuspForm.heckeTLinOne 2 hp hpM f ∈ Lat M :=
  Submodule.subset_span (heckeT_mem_dsSet hp hpM hf)

def TLat : Module.End ℤ ↥(Lat M) :=
  ((CuspForm.heckeTLinOne 2 hp hpM).restrictScalars ℤ).restrict fun _ hf => heckeT_mem_Lat hp hpM hf

@[scoped simp] theorem coe_TLat_apply (f : ↥(Lat M)) :
    ((TLat hp hpM f : ↥(Lat M)) : S2 M) = CuspForm.heckeTLinOne 2 hp hpM (f : S2 M) := rfl

end Hecke

variable (M)

theorem exists_finset_qCoeff_eq_zero_imp [FiniteDimensional ℂ (S2 M)] :
    ∃ s : Finset ℕ, ∀ f : S2 M, (∀ n ∈ s, qCoeff f n = 0) → f = 0 := by
  classical
  let Kf : Finset ℕ → Submodule ℂ (S2 M) := fun s => ⨅ n ∈ s, LinearMap.ker (qCoeffLin M n)
  have hanti : ∀ s t : Finset ℕ, s ⊆ t → Kf t ≤ Kf s := by
    intro s t hst
    exact biInf_mono hst
  obtain ⟨W, ⟨s₀, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule ℂ (S2 M))).has_min (Set.range Kf) ⟨Kf ∅, ∅, rfl⟩
  refine ⟨s₀, fun f hf => ?_⟩
  have hfK : f ∈ Kf s₀ := by
    simp only [Kf, Submodule.mem_iInf, LinearMap.mem_ker, qCoeffLin_apply]
    exact hf
  apply eq_zero_of_forall_qCoeff_eq_zero M f
  intro n
  have hle : Kf (insert n s₀) ≤ Kf s₀ := hanti _ _ (Finset.subset_insert n s₀)
  have hnlt : ¬ Kf (insert n s₀) < Kf s₀ := hmin _ ⟨insert n s₀, rfl⟩
  have heq : Kf (insert n s₀) = Kf s₀ := (eq_or_lt_of_le hle).resolve_right hnlt
  have hf' : f ∈ Kf (insert n s₀) := heq ▸ hfK
  simp only [Kf, Submodule.mem_iInf, LinearMap.mem_ker, qCoeffLin_apply] at hf'
  exact hf' n (Finset.mem_insert_self n s₀)

variable {M} in

def coefZHom (n : ℕ) : ↥(Lat M) →ₗ[ℤ] ℤ where
  toFun f := coefZ f n
  map_add' f g := by
    apply Int.cast_injective (α := ℂ)
    rw [Int.cast_add, ← coefZ_spec, ← coefZ_spec, ← coefZ_spec, Submodule.coe_add, ← qCoeffLin_apply,
      map_add, qCoeffLin_apply, qCoeffLin_apply]
  map_smul' a f := by
    apply Int.cast_injective (α := ℂ)
    rw [smul_eq_mul, Int.cast_mul, ← coefZ_spec, ← coefZ_spec, Submodule.coe_smul, ← qCoeffLin_apply,
      LinearMap.map_smul_of_tower, qCoeffLin_apply, zsmul_eq_mul, RingHom.id_apply]

@[scoped simp] lemma coefZHom_apply (n : ℕ) (f : ↥(Lat M)) : coefZHom n f = coefZ f n := rfl

theorem moduleFinite_Lat [FiniteDimensional ℂ (S2 M)] : Module.Finite ℤ ↥(Lat M) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_qCoeff_eq_zero_imp M
  let ev : ↥(Lat M) →ₗ[ℤ] (↥s → ℤ) := LinearMap.pi fun n => coefZHom (M := M) n.1
  refine Module.Finite.of_injective ev ?_
  intro f g hfg
  rw [← sub_eq_zero]
  apply Subtype.ext
  rw [Submodule.coe_sub, Submodule.coe_zero]
  have h : ev (f - g) = 0 := by rw [map_sub, hfg, sub_self]
  apply hs
  intro n hn
  have hn' := congrFun h ⟨n, hn⟩
  simp only [ev, LinearMap.pi_apply, coefZHom_apply, Pi.zero_apply] at hn'
  rw [← Submodule.coe_sub, coefZ_spec, hn', Int.cast_zero]

scoped instance isTorsionFree_Lat : Module.IsTorsionFree ℤ ↥(Lat M) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
  have h' : (r : ℂ) • ((m : ↥(Lat M)) : S2 M) = 0 := by
    rw [Int.cast_smul_eq_zsmul, ← Submodule.coe_smul_of_tower, h, Submodule.coe_zero]
  rcases smul_eq_zero.mp h' with hr | hm
  · exact Or.inl (by exact_mod_cast hr)
  · exact Or.inr (Subtype.ext hm)

theorem moduleFree_Lat [FiniteDimensional ℂ (S2 M)] : Module.Free ℤ ↥(Lat M) := by
  haveI := moduleFinite_Lat M
  exact Module.free_of_finite_type_torsion_free'

theorem linearIndependent_coe_basis {ι : Type*} [Fintype ι] (c : Module.Basis ι ℤ ↥(Lat M)) :
    LinearIndependent ℂ (fun i => ((c i : ↥(Lat M)) : S2 M)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  refine forall_eq_zero_of_forall_intRel (fun i n => coefZ (c i) n) ?_ g ?_
  · intro m hm
    have hx : (∑ i, m i • c i : ↥(Lat M)) = 0 := by
      apply Subtype.ext
      apply eq_zero_of_forall_qCoeff_eq_zero M
      intro n
      rw [← qCoeffLin_apply, Submodule.coe_sum, map_sum]
      have : ∀ i, qCoeffLin M n (((m i • c i : ↥(Lat M)) : S2 M)) = ((m i * coefZ (c i) n : ℤ) : ℂ) := by
        intro i
        rw [Submodule.coe_smul, LinearMap.map_smul_of_tower, qCoeffLin_apply, coefZ_spec, zsmul_eq_mul,
          Int.cast_mul]
      simp_rw [this]
      rw [← Int.cast_sum, hm n, Int.cast_zero]
    exact fun i => (Fintype.linearIndependent_iff.mp c.linearIndependent m hx) i
  · intro n
    have h := congrArg (qCoeffLin M n) hg
    rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, qCoeffLin_apply, coefZ_spec, smul_eq_mul]

theorem card_basis_eq_finrank [FiniteDimensional ℂ (S2 M)] {ι : Type*} [Fintype ι]
    (c : Module.Basis ι ℤ ↥(Lat M)) : Fintype.card ι = Module.finrank ℂ (S2 M) := by
  classical
  haveI := moduleFinite_Lat M
  refine le_antisymm (linearIndependent_coe_basis M c).fintype_card_le_finrank ?_
  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast M 2
  have hmem : ∀ i, b i ∈ Lat M := fun i => Submodule.subset_span (hb i)
  let b' : Fin n → ↥(Lat M) := fun i => ⟨b i, hmem i⟩
  have hbZ : LinearIndependent ℤ (fun i => (b i : S2 M)) := by
    refine b.linearIndependent.restrict_scalars ?_
    intro r s hrs
    have h : (r : ℂ) = (s : ℂ) := by simpa [zsmul_eq_mul] using hrs
    exact_mod_cast h
  have hb' : LinearIndependent ℤ b' := LinearIndependent.of_comp (Lat M).subtype hbZ
  have h1 : Fintype.card (Fin n) ≤ Module.finrank ℤ ↥(Lat M) := hb'.fintype_card_le_finrank
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c] at *
  exact h1

def basisC [FiniteDimensional ℂ (S2 M)] {ι : Type*} [Fintype ι] (c : Module.Basis ι ℤ ↥(Lat M)) :
    Module.Basis ι ℂ (S2 M) :=
  basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_coe_basis M c) (card_basis_eq_finrank M c)

@[scoped simp] theorem basisC_apply [FiniteDimensional ℂ (S2 M)] {ι : Type*} [Fintype ι]
    (c : Module.Basis ι ℤ ↥(Lat M)) (i : ι) : basisC M c i = ((c i : ↥(Lat M)) : S2 M) := by
  rw [basisC, coe_basisOfLinearIndependentOfCardEqFinrank']

theorem charpoly_heckeT_eq_map [FiniteDimensional ℂ (S2 M)] {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    letI := moduleFinite_Lat M
    letI := moduleFree_Lat M
    (CuspForm.heckeTLinOne 2 hp hpM).charpoly = (TLat hp hpM).charpoly.map (Int.castRingHom ℂ) := by
  classical
  haveI := moduleFinite_Lat M
  haveI := moduleFree_Lat M
  let c := Module.Free.chooseBasis ℤ ↥(Lat M)
  let cB := basisC M c
  set A : Matrix _ _ ℤ := LinearMap.toMatrix c c (TLat hp hpM) with hA
  have hmat : LinearMap.toMatrix cB cB (CuspForm.heckeTLinOne 2 hp hpM) = A.map (Int.castRingHom ℂ) := by
    ext i j
    rw [Matrix.map_apply, hA, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    have h1 : CuspForm.heckeTLinOne 2 hp hpM (cB j) = ∑ i', ((c.repr (TLat hp hpM (c j)) i' : ℤ) : ℂ) • cB i' := by
      have h2 := (c.sum_repr (TLat hp hpM (c j))).symm
      have h3 := congrArg (fun x : ↥(Lat M) => (x : S2 M)) h2
      simp only [coe_TLat_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower] at h3
      rw [basisC_apply, h3]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [basisC_apply, Int.cast_smul_eq_zsmul]
    rw [h1, cB.repr_sum_self]
    rfl
  rw [← LinearMap.charpoly_toMatrix (CuspForm.heckeTLinOne 2 hp hpM) cB, hmat, Matrix.charpoly_map, hA,
    LinearMap.charpoly_toMatrix]

end Lattice

section Red

variable (k : Type*) [Field k]

def red (a : ℕ → ℤ) : LaurentSeries k :=
  HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk fun n => (a n : k))

theorem red_coeff_natCast (a : ℕ → ℤ) (n : ℕ) : (red k a).coeff (n : ℤ) = (a n : k) := by
  rw [red, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

theorem red_coeff_of_neg (a : ℕ → ℤ) {m : ℤ} (hm : m < 0) : (red k a).coeff m = 0 := by
  rw [red, HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  intro hmem
  obtain ⟨n, hn⟩ := hmem
  have h' : (n : ℤ) = m := hn
  omega

end Red

section ModP

variable {M : ℕ} [NeZero M] {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M)

include hp hpM in

theorem exists_coefZ_TLat_eq (f : ↥(Lat M)) (n : ℕ) :
    ∃ m : ℤ, coefZ (TLat hp hpM f) n = coefZ f (p * n) + p * m := by
  obtain ⟨m, hm⟩ := exists_qCoeff_heckeT_eq hp hpM f.2 n
  refine ⟨m, ?_⟩
  apply Int.cast_injective (α := ℂ)
  rw [← coefZ_spec, coe_TLat_apply, hm, coefZ_spec]
  push_cast
  ring

end ModP

end G1PRank
p2m_reactivate "P2MW.S_ModularCurve_natCard_torsion_jOneC_eq_pow_natDegree_sub_natTrailingDegree_of_map_eq_charpoly_heckeTLinOne.G1PRank"

end
p2m_reactivate "P2MW.S_ModularCurve_natCard_torsion_jOneC_eq_pow_natDegree_sub_natTrailingDegree_of_map_eq_charpoly_heckeTLinOne.G1PRank"

set_option maxHeartbeats 25600000 in
open scoped TensorProduct in
p2m_open "ModularCurve~IsCusp" in open  AlgebraicCurve G1PRank Polynomial in
theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : ¬ p ∣ M)
    [FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) 2)]
    (k : Type*) [Field k] [IsAlgClosed k] [CharP k p]
    (Q : Polynomial ℤ)
    (hQ : Q.map (algebraMap ℤ ℂ) = (CuspForm.heckeTLinOne 2 (Fact.out : p.Prime) hpM).charpoly) :
    Nat.card {y : ModularCurve.JOneC M k // p • y = 0} =
      p ^ (Q.natDegree - (Q.map (Int.castRingHom (ZMod p))).natTrailingDegree) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Module.Finite ℤ ↥(Lat M) := moduleFinite_Lat M
  haveI : Module.Free ℤ ↥(Lat M) := moduleFree_Lat M
  haveI : Module.Finite k (k ⊗[ℤ] ↥(Lat M)) := inferInstance
  have hMk : (M : k) ≠ 0 := by
    intro h
    exact hpM ((CharP.cast_eq_zero_iff k p M).mp h)

  set TS : Module.End ℤ ↥(Lat M) := TLat hp hpM with hTS
  set T : Module.End k (k ⊗[ℤ] ↥(Lat M)) := TS.baseChange k with hT
  set Qx := qExpansionDiffAlong (x1FunctionFieldC k M).val with hQx

  have hQL : Q = TS.charpoly := by
    apply Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
    rw [hTS, ← charpoly_heckeT_eq_map M hp hpM, ← hQ, algebraMap_int_eq]

  have hexp : Module.finrank k ↥(⨅ n : ℕ, LinearMap.range (T ^ n)) =
      Q.natDegree - (Q.map (Int.castRingHom (ZMod p))).natTrailingDegree := by
    have hTc : T.charpoly = Q.map (algebraMap ℤ k) := by
      rw [hT, LinearMap.charpoly_baseChange, ← hQL]
    have hmon : Q.Monic := hQL ▸ LinearMap.charpoly_monic TS
    have hfac : algebraMap ℤ k = (ZMod.castHom (dvd_refl p) k).comp (Int.castRingHom (ZMod p)) :=
      RingHom.ext_int _ _
    rw [finrank_iInf_range_pow_eq, hTc, hmon.natDegree_map, hfac, ← Polynomial.map_map,
      natTrailingDegree_map_of_injective _ (ZMod.castHom (dvd_refl p) k).injective]

  obtain ⟨⟨e, he⟩, hinjQ⟩ :=
    ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective
      k M hMk
  have he' : ∀ (c : k) (f : ↥(Lat M)),
      Qx (e ((c ⊗ₜ[ℤ] f : k ⊗[ℤ] ↥(Lat M))) : Ω[↥(x1FunctionFieldC k M)⁄k]) =
        c • red k (coefZ f) := fun c f => he c f (coefZ f) (coefZ_spec f)
  set qe : (k ⊗[ℤ] ↥(Lat M)) →ₗ[k] LaurentSeries k :=
    Qx ∘ₗ (regularDifferentials k ↥(x1FunctionFieldC k M)).subtype ∘ₗ e.toLinearMap with hqe_def
  have hqe : ∀ v : k ⊗[ℤ] ↥(Lat M), qe v = Qx (e v : Ω[↥(x1FunctionFieldC k M)⁄k]) := fun v => rfl

  have hshift : ∀ (v : k ⊗[ℤ] ↥(Lat M)) (m : ℤ), (qe (T v)).coeff m = (qe v).coeff (m * p) := by
    intro v m
    induction v using TensorProduct.induction_on generalizing m with
    | zero =>
      rw [map_zero, map_zero, HahnSeries.coeff_zero, HahnSeries.coeff_zero]
    | add x y hx hy =>
      rw [map_add, map_add, HahnSeries.coeff_add, hx, hy, map_add, HahnSeries.coeff_add]
    | tmul c f =>
      rw [hqe, hqe, hT, LinearMap.baseChange_tmul, he', he', HahnSeries.coeff_smul, HahnSeries.coeff_smul]
      congr 1
      rcases lt_or_ge m 0 with hm | hm
      · rw [red_coeff_of_neg k _ hm, red_coeff_of_neg k]
        have : (0 : ℤ) < p := by exact_mod_cast hp.pos
        nlinarith
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
        have hnp : ((n : ℤ) * p) = ((p * n : ℕ) : ℤ) := by push_cast; ring
        obtain ⟨m', hm'⟩ := exists_coefZ_TLat_eq hp hpM f n
        rw [← hTS] at hm'
        rw [hnp, red_coeff_natCast, red_coeff_natCast, hm']
        push_cast
        rw [CharP.cast_eq_zero k p]
        simp

  set φ : k ≃ₗ[ℤ] k := (frobeniusEquiv k p).toAddEquiv.toIntLinearEquiv with hφ
  have hφ_apply : ∀ a : k, φ a = a ^ p := fun a => frobenius_def p a
  set σE : (k ⊗[ℤ] ↥(Lat M)) ≃ₗ[ℤ] (k ⊗[ℤ] ↥(Lat M)) := LinearEquiv.rTensor ↥(Lat M) φ with hσE
  set S : (k ⊗[ℤ] ↥(Lat M)) →+ (k ⊗[ℤ] ↥(Lat M)) := σE.toLinearMap.toAddMonoidHom with hSdef
  have hS_tmul : ∀ (a : k) (f : ↥(Lat M)), S (a ⊗ₜ[ℤ] f) = (a ^ p) ⊗ₜ[ℤ] f := by
    intro a f
    change σE (a ⊗ₜ[ℤ] f) = _
    rw [hσE]
    erw [LinearEquiv.rTensor_tmul]
    rw [hφ_apply]
  have hSbij : Function.Bijective S := σE.bijective
  have hS : ∀ (c : k) (v : k ⊗[ℤ] ↥(Lat M)), S (c • v) = c ^ p • S v := by
    intro c v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
    | tmul a f =>
      rw [TensorProduct.smul_tmul', hS_tmul, hS_tmul, TensorProduct.smul_tmul', smul_eq_mul,
        smul_eq_mul, mul_pow]
  have hcomm : ∀ v : k ⊗[ℤ] ↥(Lat M), T (S v) = S (T v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | tmul a f => rw [hS_tmul, hT, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hS_tmul]
  have hfrob : ∀ (v : k ⊗[ℤ] ↥(Lat M)) (m : ℤ), (qe (S v)).coeff m = (qe v).coeff m ^ p := by
    intro v m
    induction v using TensorProduct.induction_on generalizing m with
    | zero =>
      rw [map_zero, map_zero, HahnSeries.coeff_zero, zero_pow hp.ne_zero]
    | add x y hx hy =>
      rw [map_add, map_add, HahnSeries.coeff_add, hx, hy, map_add, HahnSeries.coeff_add, add_pow_char]
    | tmul a f =>
      rw [hqe, hqe, hS_tmul, he', he', HahnSeries.coeff_smul, HahnSeries.coeff_smul, smul_eq_mul,
        smul_eq_mul, mul_pow]
      congr 1
      rcases lt_or_ge m 0 with hm | hm
      · rw [red_coeff_of_neg k _ hm, zero_pow hp.ne_zero]
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
        rw [red_coeff_natCast, ← frobenius_def, map_intCast]

  have hiff : ∀ v : k ⊗[ℤ] ↥(Lat M), T v = S v ↔
      ∀ m : ℤ, (Qx (e v : Ω[↥(x1FunctionFieldC k M)⁄k])).coeff (m * p) =
        (Qx (e v : Ω[↥(x1FunctionFieldC k M)⁄k])).coeff m ^ p := by
    intro v
    constructor
    · intro hv m
      rw [← hqe, ← hshift, hv, hfrob]
    · intro hv
      apply e.injective
      apply hinjQ
      change qe (T v) = qe (S v)
      ext m
      rw [hshift, hfrob, hqe, hv]
  have hcard : Nat.card {v : k ⊗[ℤ] ↥(Lat M) // T v = S v} =
      Nat.card {ω : ↥(regularDifferentials k ↥(x1FunctionFieldC k M)) //
        ∀ m : ℤ, (Qx (ω : Ω[↥(x1FunctionFieldC k M)⁄k])).coeff (m * p) =
          (Qx (ω : Ω[↥(x1FunctionFieldC k M)⁄k])).coeff m ^ p} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun v => hiff v))

  rw [← hexp, ← LinearMap.natCard_setOf_apply_eq_frobeniusSemilinear_eq_pow_finrank_iInf_range_pow p S hS
      hSbij T hcomm, hcard, hQx,
    ModularCurve.natCard_torsion_jOneC_eq_natCard_regularDifferentials_x1FunctionFieldC_coeff_mul_eq_pow
      k p M hpM]

end S_ModularCurve_natCard_torsion_jOneC_eq_pow_natDegree_sub_natTrailingDegree_of_map_eq_charpoly_heckeTLinOne
end P2MW
export P2MW.S_ModularCurve_natCard_torsion_jOneC_eq_pow_natDegree_sub_natTrailingDegree_of_map_eq_charpoly_heckeTLinOne (solution)
