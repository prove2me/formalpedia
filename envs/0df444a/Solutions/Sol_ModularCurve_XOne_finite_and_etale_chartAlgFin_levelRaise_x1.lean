-- Prove2me | solution 1 for ModularCurve.XOne.finite_and_etale_chartAlgFin_levelRaise_x1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4efb9a2d-52c3-5afa-9674-83e801d41607

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_Algebra_isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one
import Theorems.Thm_Algebra_isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one
import Theorems.Thm_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1FunctionField_of_dvd
import Theorems.Thm_ModularCurve_XOne_smooth_toBase_and_isIntegral_pullback_twoChartIntegralModel_x1
import Theorems.Thm_Algebra_isUnramifiedAt_of_forall_le_height_eq_one_of_flat_of_isIntegrallyClosed
import Theorems.Thm_Algebra_etale_of_moduleFinite_of_flat_of_forall_isUnramifiedAt
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_ModularCurve_XOne_isSeparable_residueField_of_height_eq_one_of_map_maximalIdeal_le_chartAlgFin_levelRaise_x1
import Theorems.Thm_ModularCurve_XOne_isPrime_map_maximalIdeal_chartAlgFin_twoChartIntegralModel_x1
import Theorems.Thm_ModularCurve_XOne_finite_and_flat_chartAlgFin_levelRaise_x1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOne_finite_and_etale_chartAlgFin_levelRaise_x1
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isScalarTower_adjoin CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec"
p2m_attr_erase "simp" "GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix"
p2m_attr_erase "simp" "ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq"
p2m_attr_erase "simp" "CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero"
p2m_attr_erase "simp" "TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace Plumb

universe u

theorem eq_of_isPrime_of_le_of_height_eq_one {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P ≤ Q) (hP : P ≠ ⊥) (hQ : Q.height = 1) : P = Q := by
  haveI hQf : Q.FiniteHeight := ⟨Or.inr (by rw [hQ]; exact ENat.coe_ne_top 1)⟩
  haveI : P.FiniteHeight := Ideal.finiteHeight_of_le hPQ Ideal.IsPrime.ne_top'
  refine Ideal.eq_of_le_of_height_le P hPQ ?_
  rw [hQ]
  by_contra hlt
  rw [not_le, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff] at hlt
  have hbot : minimalPrimes R = {⊥} := Ideal.minimalPrimes_eq_subsingleton_self
  rw [hbot, Set.mem_singleton_iff] at hlt
  exact hP hlt

end Plumb

set_option maxHeartbeats 16000000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMp : ¬ ℓ ∣ M * p)

    (K_M : IntermediateField L (LaurentSeries L))
    (hK_M : K_M = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    [Algebra A ↥K_M] [IsScalarTower A L ↥K_M]
    (j_M : ↥K_M) (hj_M : ((j_M : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_M ≠ 0)]
    (K_N : IntermediateField L (LaurentSeries L))
    (hK_N : K_N = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * ℓ)))
    [Algebra A ↥K_N] [IsScalarTower A L ↥K_N]
    (j_N : ↥K_N) (hj_N : ((j_N : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_N ≠ 0)]
    (hleMN : K_M ≤ K_N)
    (ι_M : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) →ₐ[A] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N))
    (hι_M : ∀ x, (((ι_M x : ↥K_N) : LaurentSeries L)) = ((x : ↥K_M) : LaurentSeries L)) :
    ι_M.toRingHom.Finite ∧ ι_M.toRingHom.Etale := by
  obtain ⟨hfin, hflat⟩ := ModularCurve.XOne.finite_and_flat_chartAlgFin_levelRaise_x1 p M hM hpM L ζ hζ A hAp hζA ℓ hℓ hℓMp K_M hK_M j_M hj_M K_N hK_N j_N hj_N hleMN ι_M hι_M
  refine ⟨hfin, ?_⟩
  letI alg : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) := ι_M.toRingHom.toAlgebra
  have halg : ∀ x, algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) x = ι_M x := fun _ => rfl
  haveI hF : Module.Finite ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) := hfin
  haveI hFl : Module.Flat ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) := hflat

  have hT : ∀ N : ℕ, ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := fun N => by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.coe_T]
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) hℓ.ne_zero⟩
  have hfdM : FiniteDimensional ↥(IntermediateField.adjoin L ({j_M} : Set ↥K_M)) ↥K_M :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CongruenceSubgroup.Gamma1 M) (hT M)
      L K_M hK_M j_M hj_M
  have hfdN : FiniteDimensional ↥(IntermediateField.adjoin L ({j_N} : Set ↥K_N)) ↥K_N :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CongruenceSubgroup.Gamma1 (M * ℓ)) (hT _)
      L K_N hK_N j_N hj_N
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j_M} : Set ↥K_M)) ↥K_M := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j_N} : Set ↥K_N)) ↥K_N := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j_M} : Set ↥K_M)) ↥K_M := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j_N} : Set ↥K_N)) ↥K_N := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have htM : Transcendental A j_M := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K_M A j_M hj_M
  have htN : Transcendental A j_N := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K_N A j_N hj_N

  haveI : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) := by
    obtain ⟨hft, -⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K_M) j_M htM hfdM inferInstance
    exact Algebra.FiniteType.isNoetherianRing A _
  haveI : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) := by
    obtain ⟨hft, -⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K_N) j_N htN hfdN inferInstance
    exact Algebra.FiniteType.isNoetherianRing A _

  haveI : IsIntegrallyClosed ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K_M) {j_M}
  haveI : IsIntegrallyClosed ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K_N) {j_N}
  letI algMN : Algebra ↥K_M ↥K_N := (IntermediateField.inclusion hleMN).toRingHom.toAlgebra

  haveI : IsScalarTower ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) ↥K_N := by
    refine ⟨fun x y c => ?_⟩
    show (((ι_M x * y : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) : ↥K_N)) * c =
      (IntermediateField.inclusion hleMN (x : ↥K_M)) * ((((y : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) : ↥K_N)) * c)
    rw [← mul_assoc]
    congr 1
    apply Subtype.ext
    rw [Subalgebra.coe_mul]
    show ((ι_M x : ↥K_N) : LaurentSeries L) * ((y : ↥K_N) : LaurentSeries L) = ((x : ↥K_M) : LaurentSeries L) * ((y : ↥K_N) : LaurentSeries L)
    rw [hι_M]
  haveI : IsScalarTower ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥K_M ↥K_N := ⟨fun x k c => mul_smul (x : ↥K_M) k c⟩
  haveI : IsFractionRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥K_M := AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L (↥K_M) {j_M}
  haveI : IsFractionRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) ↥K_N := AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L (↥K_N) {j_N}

  haveI : Module.Finite ↥K_M ↥K_N := by
    let Lj : IntermediateField L ↥K_N := IntermediateField.adjoin L ({j_N} : Set ↥K_N)
    have hLj : ∀ x : ↥K_N, x ∈ Lj → ((x : LaurentSeries L)) ∈ K_M := by
      intro x hx
      induction hx using IntermediateField.adjoin_induction with
      | mem x hx =>
          rw [Set.mem_singleton_iff] at hx
          subst hx
          rw [hj_N, ← hj_M]
          exact j_M.2
      | algebraMap c => exact K_M.algebraMap_mem c
      | add x y _ _ hx hy => exact K_M.add_mem hx hy
      | inv x _ hx => exact K_M.inv_mem hx
      | mul x y _ _ hx hy => exact K_M.mul_mem hx hy
    let φ : ↥Lj →+* ↥K_M :=
      { toFun := fun x => ⟨((x : ↥K_N) : LaurentSeries L), hLj x x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    letI : Algebra ↥Lj ↥K_M := φ.toAlgebra
    haveI : IsScalarTower ↥Lj ↥K_M ↥K_N := by
      refine ⟨fun x k v => ?_⟩
      show (IntermediateField.inclusion hleMN (φ x * k)) * v = ((x : ↥Lj) : ↥K_N) * ((IntermediateField.inclusion hleMN k) * v)
      rw [map_mul, mul_assoc]
      congr 1
    haveI : Module.Finite ↥Lj ↥K_N := hfdN
    exact Module.Finite.of_restrictScalars_finite ↥Lj ↥K_M ↥K_N
  haveI : Algebra.IsAlgebraic ↥K_M ↥K_N := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable ↥K_M ↥K_N := Algebra.IsAlgebraic.isSeparable_of_perfectField

  have hU : ∀ (Q : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) [Q.IsPrime], Algebra.IsUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) Q := by
    intro Q _
    refine Algebra.isUnramifiedAt_of_forall_le_height_eq_one_of_flat_of_isIntegrallyClosed ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥K_M ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) ↥K_N Q ?_
    intro Q' _ hle hQ'1
    haveI hMlne : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) hℓ.ne_zero⟩
    by_cases hv : Ideal.map (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) (IsLocalRing.maximalIdeal A) ≤ Q'
    ·
      have hMl : 5 ≤ M * ℓ := le_trans hM (Nat.le_mul_of_pos_right M hℓ.pos)
      have hpMl : ¬ p ∣ M * ℓ := by
        intro h
        rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h1 | h2
        · exact hpM h1
        · have hpl : p = ℓ := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hℓ).1 h2
          exact hℓMp (hpl ▸ dvd_mul_left p M)
      have hP0 : (Ideal.map (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) (IsLocalRing.maximalIdeal A)).IsPrime :=
        ModularCurve.XOne.isPrime_map_maximalIdeal_chartAlgFin_twoChartIntegralModel_x1 p (M * ℓ) hMl hpMl L ζ hζ K_N hK_N A hAp hζA j_N hj_N
      have hP0ne : Ideal.map (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) (IsLocalRing.maximalIdeal A) ≠ ⊥ := by
        have hinj : Function.Injective (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) := by
          rw [injective_iff_map_eq_zero]
          intro a ha
          have h1 := congrArg (fun z : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) => (z : ↥K_N)) ha
          simp only [Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] at h1
          rw [IsScalarTower.algebraMap_apply A L ↥K_N, map_eq_zero] at h1
          exact (IsFractionRing.injective A L) (h1.trans (map_zero _).symm)
        exact fun h => IsDiscreteValuationRing.not_a_field A ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
      have hQ'eq : Ideal.map (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) (IsLocalRing.maximalIdeal A) = Q' :=
        @Plumb.eq_of_isPrime_of_le_of_height_eq_one _ _ _ _ _ Q' hP0 _ hv hP0ne hQ'1

      haveI : NoZeroSMulDivisors ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) := by
        refine ⟨fun {c x} h => ?_⟩
        have h' : ι_M c * x = 0 := h
        rcases mul_eq_zero.mp h' with h1 | h2
        · left
          have hinjι : Function.Injective ι_M := fun a b hab => by
            apply Subtype.ext
            apply Subtype.ext
            rw [← hι_M a, ← hι_M b]
            exact congrArg (fun t : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) => ((t : ↥K_N) : LaurentSeries L)) hab
          exact hinjι (h1.trans (map_zero ι_M).symm)
        · exact Or.inr h2
      letI := Localization.AtPrime.algebraOfLiesOver (Q'.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)) Q'
      have hsep := ModularCurve.XOne.isSeparable_residueField_of_height_eq_one_of_map_maximalIdeal_le_chartAlgFin_levelRaise_x1 p M hM hpM L ζ hζ A hAp hζA ℓ hℓ hℓMp K_M hK_M j_M hj_M K_N hK_N j_N hj_N hleMN ι_M hι_M halg Q' hQ'1 hv
      have key := Algebra.isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one (O := ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)) (C := ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) Q' hQ'1
      refine key.2.2.2.mpr ⟨?_, hsep⟩

      haveI : IsScalarTower A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) := IsScalarTower.of_algebraMap_eq (fun a => (ι_M.commutes a).symm)
      have hleO : Ideal.map (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)) (IsLocalRing.maximalIdeal A) ≤ Q'.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) := by
        rw [Ideal.map_le_iff_le_comap, Ideal.under_def, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N),
          ← Ideal.map_le_iff_le_comap]
        exact hQ'eq.le
      apply le_antisymm
      · rw [IsScalarTower.algebraMap_eq ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) (Localization.AtPrime Q'), ← Ideal.map_map,
          ← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.map_mono Ideal.map_comap_le
      · rw [← Localization.AtPrime.map_eq_maximalIdeal]
        calc Ideal.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) (Localization.AtPrime Q')) Q'
            = Ideal.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) (Localization.AtPrime Q'))
                (Ideal.map (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) (IsLocalRing.maximalIdeal A)) := by rw [hQ'eq]
          _ = Ideal.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) (Localization.AtPrime Q'))
                (Ideal.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) (Ideal.map (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)) (IsLocalRing.maximalIdeal A))) := by
              congr 1
              rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)]
          _ ≤ Ideal.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) (Localization.AtPrime Q'))
                (Ideal.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) (Q'.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M))) := Ideal.map_mono (Ideal.map_mono hleO)
          _ = Ideal.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) (Localization.AtPrime Q')) (Q'.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)) := by
              rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) (Localization.AtPrime Q')]
    ·
      obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A
      have hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
      have hϖQ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) ϖ ∉ Q' := by
        intro h
        apply hv
        rw [hϖ, Ideal.map_span, Set.image_singleton]
        exact Ideal.span_le.2 (Set.singleton_subset_iff.2 h)
      haveI : Algebra.IsAlgebraic ℚ L := by
        haveI := IsCyclotomicExtension.finiteDimensional {p} ℚ L
        exact Algebra.IsAlgebraic.of_finite ℚ L
      haveI : IsScalarTower A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) := IsScalarTower.of_algebraMap_eq (fun a => (ι_M.commutes a).symm)
      have hι : ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M), algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) ↥K_N (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) x) = IntermediateField.inclusion hleMN (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥K_M x) := by
        intro x
        apply Subtype.ext
        exact hι_M x
      have hint : (IntermediateField.inclusion hleMN).toRingHom.IsIntegral := by
        have hfinMN : (IntermediateField.inclusion hleMN).toRingHom.Finite := ‹Module.Finite ↥K_M ↥K_N›
        exact hfinMN.to_isIntegral
      have he : ∀ w : AlgebraicCurve.Place L ↥K_N, 0 ≤ w.ord (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) ↥K_N (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K_N) j_N)) →
          AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hleMN) w = 1 := by
        intro w hw
        have hw' : 0 ≤ w.ord j_N := hw
        exact ModularCurve.ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1FunctionField_of_dvd
          M (M * ℓ) (by omega) (dvd_mul_right M ℓ) L K_N hK_N K_M hK_M hleMN j_N hj_N w hw'
      exact Algebra.isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one
        L A ↥K_N ↥K_M (IntermediateField.inclusion hleMN) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) hι hint
        (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K_N) j_N) he ϖ hϖ Q' hQ'1 hϖQ

  exact Algebra.etale_of_moduleFinite_of_flat_of_forall_isUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) hU

end S_ModularCurve_XOne_finite_and_etale_chartAlgFin_levelRaise_x1
end P2MW
export P2MW.S_ModularCurve_XOne_finite_and_etale_chartAlgFin_levelRaise_x1 (solution)
