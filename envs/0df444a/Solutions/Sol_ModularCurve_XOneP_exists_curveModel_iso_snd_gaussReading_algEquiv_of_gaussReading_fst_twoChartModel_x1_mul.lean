-- Prove2me | solution 1 for ModularCurve.XOneP.exists_curveModel_iso_snd_gaussReading_algEquiv_of_gaussReading_fst_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9a5c1bba-9ad0-5ce8-8b8c-818bdc426cf9

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv
import Theorems.Thm_ValuationSubring_exists_fractionRing_tensorProduct_quotient_algEquiv_apply_tmul_eq_coeffMap_of_residueField_ringEquiv
import Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_algEquiv_fractionRing_tensorProduct_apply_germ_eq_of_curveModel_component_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_curveModel_igusaFunctionFieldX1C_iso_snd_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_pair_x1_mul
import Theorems.Thm_ModularCurve_XOneP_valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation
import Theorems.Thm_ModularCurve_adjoin_image_coeffMap_igusaFunctionFieldX1C_eq
import Theorems.Thm_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_ModularCurve_XOneP_eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_curveModel_iso_snd_gaussReading_algEquiv_of_gaussReading_fst_twoChartModel_x1_mul
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower"
p2m_attr_erase "instance" "CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec"
p2m_attr_erase "simp" "CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄"
p2m_attr_erase "simp" "ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct

namespace CIP

theorem maximalIdeal_le_ker_algebraMap_of_charP
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (k : Type*) [Field k] [CharP k p] [Algebra A k] :
    IsLocalRing.maximalIdeal A ≤ RingHom.ker (algebraMap A k) := by
  have hker : (RingHom.ker (algebraMap A k)).IsPrime := RingHom.ker_isPrime _
  have hpk : (p : A) ∈ RingHom.ker (algebraMap A k) := by
    rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hne : RingHom.ker (algebraMap A k) ≠ ⊥ := fun h => hp0 (by rwa [h, Ideal.mem_bot] at hpk)
  rw [IsLocalRing.eq_maximalIdeal ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime A).mp ‹_› |>.2
    |> fun _ => hker.isMaximal hne)]

noncomputable def residueFieldTo
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (k : Type*) [Field k] [CharP k p] [Algebra A k] : IsLocalRing.ResidueField A →+* k :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (algebraMap A k)
    (fun a ha => maximalIdeal_le_ker_algebraMap_of_charP A p hp0 k ha)

theorem residueFieldTo_residue
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (k : Type*) [Field k] [CharP k p] [Algebra A k] (a : A) :
    residueFieldTo A p hp0 k (IsLocalRing.residue A a) = algebraMap A k a := rfl

theorem coeffMap_ofPowerSeries_map {κ k : Type*} [Field κ] [Field k] (σ : κ →+* k)
    {A : Type*} [CommRing A] (ρ : A →+* κ) (q : PowerSeries A) :
    ModularCurve.coeffMap σ (HahnSeries.ofPowerSeries ℤ κ (q.map ρ)) = HahnSeries.ofPowerSeries ℤ k (q.map (σ.comp ρ)) := by
  ext n
  change σ ((HahnSeries.ofPowerSeries ℤ κ (q.map ρ)).coeff n) = (HahnSeries.ofPowerSeries ℤ k (q.map (σ.comp ρ))).coeff n
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map, RingHom.comp_apply]
  · have hr : n ∉ Set.range (fun m : ℕ => (m : ℤ)) := by
      rintro ⟨m, hm⟩
      simp only at hm
      omega
    rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range hr, HahnSeries.ofPowerSeries_apply,
      HahnSeries.embDomain_notin_range hr, map_zero]

end CIP

namespace CIP

theorem exists_pin_of_component
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    (k : Type) [Field k] [Algebra A k] (M : ℕ) (w : ModularCurve.IntegralWeightOneForm k M)
    (C : Scheme.{0}) (c : C ⟶ Spec (CommRingCat.of k))
    (i : SchemeHomOver c (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    (Mdl : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e : Mdl.C ≅ C) (he : e.hom ≫ c = Mdl.toBase)
    (V : ValuationSubring ↥K) (hCV : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), ((a : ↥K)) ∈ V)
    [Algebra A ↥V]
    (𝔮 : Ideal (k ⊗[A] ↥V))
    (Ψ : ↥(ModularCurve.igusaFunctionFieldX1C k M w) ≃ₐ[k] FractionRing ((k ⊗[A] ↥V) ⧸ 𝔮))
    (hne : Nonempty (Scheme.Opens.toScheme ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))))
    (hpin : haveI := hne
      ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        Ψ (Mdl.ffEquiv.symm
                (Mdl.C.germToFunctionField ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
                  (((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
                    (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))))
          = Localization.mk (Ideal.Quotient.mk 𝔮 ((1 : k) ⊗ₜ[A] (⟨(a : ↥K), hCV a⟩ : ↥V))) 1)
    (Φ : FractionRing ((k ⊗[A] ↥V) ⧸ 𝔮) ≃ₐ[k] ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (Pres : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) → PowerSeries A → PowerSeries A → Prop)
    (R : ↥V → LaurentSeries k)
    (hΦ : ∀ v : ↥V, (((Φ (Localization.mk (Ideal.Quotient.mk 𝔮 ((1 : k) ⊗ₜ[A] v)) 1)) : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) = R v)
    (hR : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      Pres a x y →
      R ⟨(a : ↥K), hCV a⟩ = HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) /
        HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k))) :
    ∃ (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C),
      e₁.hom ≫ c = Mdl₁.toBase ∧
      (∃ hne : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))),
          haveI := hne
          ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
            y.map (algebraMap A k) ≠ 0 →
            Pres a x y →
            ((Mdl₁.ffEquiv.symm
                (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
                  (((e₁.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
                    (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
                : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
              HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) /
                HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k))) := by
  classical
  haveI := hne
  obtain ⟨Mdl₁, f, hf, hsq⟩ :=
    AlgebraicCurve.CurveModel.exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv (Ψ.trans Φ) Mdl

  have hfx : ∀ x0 : ↥Mdl.C, f.hom.base (f.inv.base x0) = x0 := fun x0 => by
    have := congrArg (fun h : Mdl.C ⟶ Mdl.C => h.base x0) f.inv_hom_id
    simpa using this
  have hne1 : Nonempty (Scheme.Opens.toScheme (((f ≪≫ e).hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))) := by
    obtain ⟨⟨x0, hx0⟩⟩ := hne
    refine ⟨⟨f.inv.base x0, ?_⟩⟩
    change (i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base
        (e.hom.base (f.hom.base (f.inv.base x0))) ∈ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)
    rw [hfx]
    exact hx0
  refine ⟨Mdl₁, f ≪≫ e, ?_, hne1, ?_⟩
  · show (f.hom ≫ e.hom) ≫ c = Mdl₁.toBase
    rw [Category.assoc, he, hf]
  · intro a x y hy hxy

    have key : ∀ (g' : Mdl₁.C ⟶ (AlgebraicCurve.TwoChartIntegralModel A (↥K) j)) (hg : ((f ≪≫ e).hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) = g')
        (inst' : Nonempty (Scheme.Opens.toScheme (g' ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))),
        (haveI := hne1
         Mdl₁.ffEquiv.symm (Mdl₁.C.germToFunctionField (((f ≪≫ e).hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
          ((((f ≪≫ e).hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))))
        = (haveI := inst'
           Mdl₁.ffEquiv.symm (Mdl₁.C.germToFunctionField (g' ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            ((g'.app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))) := by
      intro g' hg inst'
      subst hg
      rfl
    have hg' : ((f ≪≫ e).hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) = f.hom ≫ (e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) := by
      simp only [Iso.trans_hom, Category.assoc]
    have inst2 : Nonempty (Scheme.Opens.toScheme ((f.hom ≫ (e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))) := by
      rw [← hg']; exact hne1
    rw [key _ hg' inst2]

    haveI : Nonempty (Scheme.Opens.toScheme (f.hom ⁻¹ᵁ ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))) := inst2
    have hsq' := hsq ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)) (((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))
    refine (congrArg (fun z : ↥(ModularCurve.igusaFunctionFieldX1C k M w) => ((z : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k)) hsq').trans ?_
    show ((((Ψ.trans Φ) (Mdl.ffEquiv.symm
                (Mdl.C.germToFunctionField ((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
                  (((e.hom ≫ i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
                    (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)))))) : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) = _
    rw [AlgEquiv.trans_apply, hpin a, hΦ, hR a x y hy hxy]

end CIP

theorem CIP.isGenericPoint_hom_base {X Y : Scheme} [IrreducibleSpace X] (e : X ≅ Y) :
    IsGenericPoint (e.hom.base (genericPoint X)) (⊤ : Set Y) := by
  have h := (genericPoint_spec X).image (f := e.hom.base) e.hom.base.hom.continuous
  have hsurj : Function.Surjective e.hom.base := (Scheme.homeoOfIso e).surjective
  rw [Set.image_univ, hsurj.range_eq, closure_univ] at h
  exact h

namespace DistinctRings

theorem eq_of_forall_isUnit_germ_iff {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    (x₁ x₂ : X) (h₁ : x₁ ∈ U) (h₂ : x₂ ∈ U)
    (h : ∀ f : Γ(X, U), IsUnit (X.presheaf.germ U x₁ h₁ f) ↔ IsUnit (X.presheaf.germ U x₂ h₂ f)) :
    x₁ = x₂ := by
  have key : hU.primeIdealOf ⟨x₁, h₁⟩ = hU.primeIdealOf ⟨x₂, h₂⟩ := by
    rw [hU.primeIdealOf_eq_map_closedPoint ⟨x₁, h₁⟩, hU.primeIdealOf_eq_map_closedPoint ⟨x₂, h₂⟩]
    ext f
    change f ∈ Ideal.comap _ _ ↔ f ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change (X.presheaf.germ U x₁ h₁).hom f ∈ IsLocalRing.maximalIdeal _ ↔
      (X.presheaf.germ U x₂ h₂).hom f ∈ IsLocalRing.maximalIdeal _
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
    exact h f
  have e₁ := hU.fromSpec_primeIdealOf ⟨x₁, h₁⟩
  have e₂ := hU.fromSpec_primeIdealOf ⟨x₂, h₂⟩
  rw [key] at e₁
  exact e₁.symm.trans e₂

theorem isUnit_iff_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (φ : R ≃+* S) (x : R) :
    IsUnit x ↔ IsUnit (φ x) :=
  ⟨fun h => h.map φ, fun h => by simpa using h.map φ.symm⟩

theorem isUnit_iff_coe_not_mem_nonunits {K : Type*} [Field K] (V : ValuationSubring K) (v : ↥V) :
    IsUnit v ↔ (v : K) ∉ V.nonunits := by
  rw [ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

end DistinctRings

namespace DistinctRings

theorem surjective_fst_of_range_subset {Y C₁ C₂ : Scheme.{0}} (i₁ : C₁ ⟶ Y) (i₂ : C₂ ⟶ Y)
    (h : Set.range i₁.base ⊆ Set.range i₂.base) : Function.Surjective (pullback.fst i₁ i₂).base := by
  intro a
  obtain ⟨b, hb⟩ := h ⟨a, rfl⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback a b hb.symm
  exact ⟨z, hz⟩

theorem infinite_pullback_of_range_eq {Y C₁ C₂ : Scheme.{0}} (i₁ : C₁ ⟶ Y) (i₂ : C₂ ⟶ Y)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] (h : Set.range i₁.base = Set.range i₂.base) [Infinite ↥C₁] :
    Infinite ↥(pullback i₁ i₂) :=
  Infinite.of_surjective _ (surjective_fst_of_range_subset i₁ i₂ h.le)

theorem eq_of_specializes_of_isGenericPoint {Y C₁ C₂ : Scheme.{0}} (i₁ : C₁ ⟶ Y) (i₂ : C₂ ⟶ Y)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IrreducibleSpace ↥C₁] [IrreducibleSpace ↥C₂] [Infinite ↥C₁]
    (hcover : ∀ z : ↥Y, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base) (hfin : Finite ↥(pullback i₁ i₂))
    (ξ₁ : ↥C₁) (hξ₁ : IsGenericPoint ξ₁ ⊤) (y : ↥Y) (hy : y ⤳ i₁.base ξ₁) : y = i₁.base ξ₁ := by
  rcases hcover y with ⟨a, rfl⟩ | ⟨b, rfl⟩
  ·
    have h1 : i₁.base ξ₁ ⤳ i₁.base a := (hξ₁.specializes (Set.mem_univ a)).map i₁.base.hom.continuous
    exact ((hy.antisymm h1).eq)
  ·
    exfalso
    have hcl : IsClosed (Set.range i₂.base) := i₂.isClosedEmbedding.isClosed_range
    have hmem : i₁.base ξ₁ ∈ Set.range i₂.base :=
      hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨b, rfl⟩) (specializes_iff_mem_closure.mp hy)
    have hsub : Set.range i₁.base ⊆ Set.range i₂.base := by
      calc Set.range i₁.base = i₁.base '' Set.univ := Set.image_univ.symm
        _ = i₁.base '' closure {ξ₁} := by rw [hξ₁.def, Set.top_eq_univ]
        _ ⊆ closure (i₁.base '' {ξ₁}) := image_closure_subset_closure_image i₁.base.hom.continuous
        _ = closure {i₁.base ξ₁} := by rw [Set.image_singleton]
        _ ⊆ Set.range i₂.base := hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)
    haveI : Infinite ↥(pullback i₁ i₂) := Infinite.of_surjective _ (surjective_fst_of_range_subset i₁ i₂ hsub)
    exact (not_finite ↥(pullback i₁ i₂)).elim

theorem step2
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)
    (w : ModularCurve.IntegralWeightOneForm k M) :
    ∀ (ξ₁ : ↥C₁) (_ : IsGenericPoint ξ₁ ⊤) (ξ₂ : ↥C₂) (_ : IsGenericPoint ξ₂ ⊤)
      (hz₁ : (i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₁ ∈ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
      (hz₂ : (i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₂ ∈ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
      (V₁ V₂ : ValuationSubring ↥K)

      (_ : ∀ a : A, algebraMap A ↥K a ∈ V₁)
      (_ : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V₁.nonunits)
      (_ : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ V₁ ∧ (Polynomial.aeval j P)⁻¹ ∈ V₁)
      (_ : ∀ a : A, algebraMap A ↥K a ∈ V₂)
      (_ : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V₂.nonunits)
      (_ : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ V₂ ∧ (Polynomial.aeval j P)⁻¹ ∈ V₂)
      (φ₁ : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₁) ≃+* ↥V₁)
      (_ : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        ((φ₁ (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₁) hz₁).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))) : ↥V₁) : ↥K) = (a : ↥K))
      (φ₂ : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₂) ≃+* ↥V₂)
      (_ : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        ((φ₂ (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₂) hz₂).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))) : ↥V₂) : ↥K) = (a : ↥K)),
      (i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₁ =
        (i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₂ → False := by
  classical
  intro ξ₁ hξ₁ ξ₂ hξ₂ hz₁ hz₂ V₁ V₂ hA₁ hm₁ hj₁ hA₂ hm₂ hj₂ φ₁ hφ₁ φ₂ hφ₂ hzeq

  let Xk := pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)
  let y₁ : ↥Xk := i₁.1.base ξ₁
  let y₂ : ↥Xk := i₂.1.base ξ₂
  have hy₁ : (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y₁ =
      (i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₁ := by
    simp [y₁]
  have hy₂ : (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y₂ =
      (i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₂ := by
    simp [y₂]

  have hint : ∀ {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
      [GeometricallyIntegral c], IsIntegral C := by
    intro C c _ _ _
    haveI : IsIntegral (pullback c (Spec.map (CommRingCat.ofHom (algebraMap k k)))) :=
      SmoothProperCurve.isIntegral_pullback_Spec_field k c (Spec.map (CommRingCat.ofHom (algebraMap k k)))
    have hid : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _ := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]; exact Spec.map_id _
    haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by rw [hid]; infer_instance
    exact IsIntegral.of_isIso (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap k k))))
  haveI : IsIntegral C₁ := hint c₁
  haveI : IsIntegral C₂ := hint c₂
  have hinf : ∀ {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C] [SmoothOfRelativeDimension 1 c],
      Infinite ↥C := fun c _ _ =>
    Set.infinite_univ_iff.mp ((AlgebraicCurve.infinite_setOf_isClosed_singleton c).mono (Set.subset_univ _))
  haveI : Infinite ↥C₁ := hinf c₁
  haveI : Infinite ↥C₂ := hinf c₂

  haveI hfin : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by rw [hn]; exact hn0.ne')
  haveI hfin' : Finite ↥(pullback i₂.1 i₁.1) :=
    Finite.of_equiv _ (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (pullbackSymmetry i₁.1 i₂.1))).toEquiv

  have hmin₁ : ∀ t, t ⤳ y₁ → t = y₁ := fun t ht =>
    DistinctRings.eq_of_specializes_of_isGenericPoint i₁.1 i₂.1 hcover hfin ξ₁ hξ₁ t ht
  have hmin₂ : ∀ t, t ⤳ y₂ → t = y₂ := fun t ht =>
    DistinctRings.eq_of_specializes_of_isGenericPoint i₂.1 i₁.1 (fun z => (hcover z).symm) hfin' ξ₂ hξ₂ t ht

  have hyeq : y₁ = y₂ :=
    ModularCurve.XOneP.eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k y₁ y₂ hmin₁ hmin₂ V₁ hA₁ hm₁ hj₁ hz₁ φ₁ hφ₁ hzeq

  have hrange : Set.range i₁.1.base = Set.range i₂.1.base := by
    have hr : ∀ {C : Scheme.{0}} (i : C ⟶ Xk) [IsClosedImmersion i] (ξ : ↥C) (hξ : IsGenericPoint ξ ⊤),
        Set.range i.base = closure {i.base ξ} := by
      intro C i _ ξ hξ
      calc Set.range i.base = i.base '' Set.univ := Set.image_univ.symm
        _ = i.base '' closure {ξ} := by rw [hξ.def, Set.top_eq_univ]
        _ = closure (i.base '' {ξ}) := (i.isClosedEmbedding.closure_image_eq _).symm
        _ = closure {i.base ξ} := by rw [Set.image_singleton]
    have h1 : Set.range i₁.1.base = closure {y₁} := hr i₁.1 ξ₁ hξ₁
    have h2 : Set.range i₂.1.base = closure {y₂} := hr i₂.1 ξ₂ hξ₂
    rw [h1, h2, hyeq]
  haveI := DistinctRings.infinite_pullback_of_range_eq i₁.1 i₂.1 hrange
  exact not_finite (↥(pullback i₁.1 i₂.1))

end DistinctRings

namespace T0

theorem mk_one_tmul_eq_zero_iff
    {A : Type*} [CommRing A] {k : Type*} [Field k] [Algebra A k] {K : Type*} [Field K] [Algebra A K]
    (V : ValuationSubring K) [Algebra A ↥V]
    (halgV : ∀ a : A, ((algebraMap A ↥V a : ↥V) : K) = algebraMap A K a)
    (ϖ : A) (hkϖ : algebraMap A k ϖ = 0)
    (hunif : ∀ f : K, f ∈ V.nonunits → ∃ g : K, g ∈ V ∧ f = algebraMap A K ϖ * g)
    (𝔮 : Ideal (k ⊗[A] ↥V)) (h𝔮 : 𝔮.IsPrime) (v : ↥V) :
    Ideal.Quotient.mk 𝔮 ((1 : k) ⊗ₜ[A] v) = 0 ↔ (v : K) ∈ V.nonunits := by
  constructor
  · intro h
    by_contra hv
    have hu : IsUnit v := (DistinctRings.isUnit_iff_coe_not_mem_nonunits V v).mpr hv
    have hu' : IsUnit ((1 : k) ⊗ₜ[A] v) := by
      have := hu.map (Algebra.TensorProduct.includeRight : ↥V →ₐ[A] k ⊗[A] ↥V)
      simpa [Algebra.TensorProduct.includeRight_apply] using this
    rw [Ideal.Quotient.eq_zero_iff_mem] at h
    exact h𝔮.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu')
  · intro hv
    obtain ⟨g, hg, hfg⟩ := hunif (v : K) hv
    have hv' : v = algebraMap A ↥V ϖ * ⟨g, hg⟩ := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, halgV]
      exact hfg
    rw [Ideal.Quotient.eq_zero_iff_mem, hv', ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_one, hkϖ, TensorProduct.zero_tmul]
    exact 𝔮.zero_mem

theorem map_eq_zero_iff_of_comp {A κ k : Type*} [CommRing A] [Field κ] [Field k]
    (ρ : A →+* κ) (τ : κ →+* k) (g : A →+* k) (hg : τ.comp ρ = g) (y : PowerSeries A) :
    y.map g = 0 ↔ y.map ρ = 0 := by
  constructor
  · intro h
    ext n
    have := congrArg (PowerSeries.coeff n) h
    rw [PowerSeries.coeff_map, map_zero, ← hg, RingHom.comp_apply, map_eq_zero_iff _ τ.injective] at this
    rw [PowerSeries.coeff_map, map_zero]
    exact this
  · intro h
    rw [← hg, PowerSeries.map_comp, RingHom.comp_apply, h, map_zero]

end T0

set_option maxHeartbeats 12800000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)
        (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)

    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
        HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))

    [NeZero p]
    (σ : ↥K ≃ₐ[L] ↥K)
    (hσj : ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))
    (hσfin : ∀ b : ↥K, b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ↔
        σ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
    (hσW : ∀ W₀ : ValuationSubring ↥K,
        (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) →
        W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ≠ W₀ ∧
        (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
          Polynomial.aeval j P ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ∧
          (Polynomial.aeval j P)⁻¹ ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom))

    (w₂ : ModularCurve.IntegralWeightOneForm k M) :
    ∃ (Mdl₂ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w₂)) (e₂ : Mdl₂.C ≅ C₂)
      (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

      (hne₂ : Nonempty (Scheme.Opens.toScheme ((e₂.hom ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))),
      haveI := hne₂
      ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
        y.map (algebraMap A k) ≠ 0 →
        ((σ (a : ↥K) : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
          HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        ((Mdl₂.ffEquiv.symm
          (Mdl₂.C.germToFunctionField ((e₂.hom ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₂.hom ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C k M w₂)) : LaurentSeries k) =
          HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)) := by
  classical
  haveI hp : Fact p.Prime := inferInstance

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq
  have hp0 : (p : A) ≠ 0 := fun h =>
    (Nat.cast_ne_zero.mpr hp.out.ne_zero : (p : L) ≠ 0) (by rw [← map_natCast (algebraMap A L), h, map_zero])
  have hk : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A k a = 0 := fun a ha =>
    CIP.maximalIdeal_le_ker_algebraMap_of_charP A p hp0 k ha
  have hkϖ : algebraMap A k ϖ = 0 := hk ϖ (by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
  letI algκk : Algebra (IsLocalRing.ResidueField A) k := (CIP.residueFieldTo A p hp0 k).toAlgebra
  have hκk : ∀ a : A, algebraMap (IsLocalRing.ResidueField A) k (IsLocalRing.residue A a) = algebraMap A k a := fun a => rfl
  have hσres : (algebraMap (IsLocalRing.ResidueField A) k).comp (IsLocalRing.residue A) = algebraMap A k := RingHom.ext hκk
  have hLD : ∀ (n : ℕ) (f : Fin n → LaurentSeries (IsLocalRing.ResidueField A)),
      LinearIndependent (IsLocalRing.ResidueField A) f →
      LinearIndependent k (⇑(ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)) ∘ f) :=
    fun n f hf => ModularCurve.linearIndependent_coeffMap_comp_of_linearIndependent (IsLocalRing.ResidueField A) k f hf

  obtain ⟨w₀⟩ := ModularCurve.nonempty_integralWeightOneForm (IsLocalRing.ResidueField A) M (by omega)
  obtain ⟨W₀, W₁, h1, h2, -, h4, -, h6, h7⟩ :=
    ModularCurve.XOneP.exists_valuationSubring_pair_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj w₀

  obtain ⟨hσne, hσj'⟩ := hσW W₀ h4
  obtain ⟨hcount, hram, -, -⟩ :=
    ModularCurve.XOneP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj w₀ ϖ hϖ W₀ h4 σ hσj hσne hσj'

  obtain ⟨MdlB, eB, heB⟩ :=
    ModularCurve.XOneP.exists_curveModel_igusaFunctionFieldX1C_iso_snd_twoChartModel_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj
      k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 ε ε₁ ε₂ hε₁ w₂

  set ξ₁ : ↥C₁ := e₁.hom.base (genericPoint Mdl₁.C) with hξ₁def
  have hξ₁ : IsGenericPoint ξ₁ ⊤ := CIP.isGenericPoint_hom_base e₁
  set ξ₂ : ↥C₂ := eB.hom.base (genericPoint MdlB.C) with hξ₂def
  have hξ₂ : IsGenericPoint ξ₂ ⊤ := CIP.isGenericPoint_hom_base eB
  obtain ⟨V₁, hVA1, hVm1, hVj1, algV1, halgV1, hCV1, hz1, φ1, hφ1, 𝔮1, h𝔮1, Ψ1, hne1, hpin1⟩ :=
    ModularCurve.XOneP.exists_valuationSubring_algEquiv_fractionRing_tensorProduct_apply_germ_eq_of_curveModel_component_twoChartModel_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj
      k C₁ c₁ i₁ ξ₁ hξ₁ ↥(ModularCurve.igusaFunctionFieldX1C k M w) Mdl₁ e₁ he₁
  obtain ⟨V₂, hVA2, hVm2, hVj2, algV2, halgV2, hCV2, hz2, φ2, hφ2, 𝔮2, h𝔮2, Ψ2, hne2, hpin2⟩ :=
    ModularCurve.XOneP.exists_valuationSubring_algEquiv_fractionRing_tensorProduct_apply_germ_eq_of_curveModel_component_twoChartModel_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj
      k C₂ c₂ i₂ ξ₂ hξ₂ ↥(ModularCurve.igusaFunctionFieldX1C k M w₂) MdlB eB heB
  have hunif1 : ∀ f : ↥K, f ∈ V₁.nonunits → ∃ g : ↥K, g ∈ V₁ ∧ f = algebraMap A ↥K ϖ * g := hram V₁ hVA1 hVm1 hVj1
  have hunif2 : ∀ f : ↥K, f ∈ V₂.nonunits → ∃ g : ↥K, g ∈ V₂ ∧ f = algebraMap A ↥K ϖ * g := hram V₂ hVA2 hVm2 hVj2

  have hV2ne : V₂ ≠ W₀ := by
    intro hV

    have hcentre : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), ((a : ↥K)) ∈ V₁.nonunits ↔ ((a : ↥K)) ∈ V₂.nonunits := by
      intro a
      obtain ⟨x, y, hy, hxy⟩ := (h4 (a : ↥K)).1 (hV ▸ hCV2 a)
      have hyk : y.map (algebraMap A k) ≠ 0 := fun h0 =>
        hy ((T0.map_eq_zero_iff_of_comp (IsLocalRing.residue A) (algebraMap (IsLocalRing.ResidueField A) k) (algebraMap A k) hσres y).1 h0)

      have hG := hgauss₁ a x y hyk hxy

      have hW : ((a : ↥K)) ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0 := (h6 (a : ↥K) x y hy hxy).2

      have hV1 : ((a : ↥K)) ∈ V₁.nonunits ↔ (Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))) = 0 := by
        letI := algV1
        rw [← T0.mk_one_tmul_eq_zero_iff V₁ halgV1 ϖ hkϖ hunif1 𝔮1 h𝔮1.1.1 ⟨(a : ↥K), hCV1 a⟩,
          ← EmbeddingLike.map_eq_zero_iff (f := Ψ1)]
        have hΨ : Ψ1 (Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))) = Localization.mk (Ideal.Quotient.mk 𝔮1 ((1 : k) ⊗ₜ[A] (⟨(a : ↥K), hCV1 a⟩ : ↥V₁))) 1 := hpin1 a
        rw [hΨ, Localization.mk_one_eq_algebraMap, IsFractionRing.to_map_eq_zero_iff]

      have hGx : (Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))) = 0 ↔ x.map (IsLocalRing.residue A) = 0 := by
        rw [← ZeroMemClass.coe_eq_zero, hG, div_eq_zero_iff,
          or_iff_left ((map_ne_zero_iff _ (HahnSeries.ofPowerSeries_injective)).mpr hyk),
          map_eq_zero_iff _ (HahnSeries.ofPowerSeries_injective),
          T0.map_eq_zero_iff_of_comp (IsLocalRing.residue A) (algebraMap (IsLocalRing.ResidueField A) k) (algebraMap A k) hσres x]
      rw [hV1, hGx, ← hW, hV]

    have hU : IsAffineOpen ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) :=
      (Scheme.Hom.image_top_eq_opensRange (ModularCurve.TwoChart.ιFin A (↥K) j)).symm ▸ isAffineOpen_opensRange (ModularCurve.TwoChart.ιFin A (↥K) j)
    have hzeq : (i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₁ = (i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₂ := by
      refine DistinctRings.eq_of_forall_isUnit_germ_iff hU _ _ hz1 hz2 fun f => ?_
      set a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) :=
        (Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).hom f) with ha
      have hf : f = ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a) := by
        simp [ha]
      rw [hf]
      have h1 : IsUnit (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)
      ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₁) hz1).hom
        (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))) ↔ ((a : ↥K)) ∉ V₁.nonunits := by
        refine (DistinctRings.isUnit_iff_of_ringEquiv φ1 _).trans ?_
        rw [DistinctRings.isUnit_iff_coe_not_mem_nonunits, hφ1 a]
      have h2 : IsUnit (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)
      ((i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₂) hz2).hom
        (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))) ↔ ((a : ↥K)) ∉ V₂.nonunits := by
        refine (DistinctRings.isUnit_iff_of_ringEquiv φ2 _).trans ?_
        rw [DistinctRings.isUnit_iff_coe_not_mem_nonunits, hφ2 a]
      exact h1.trans ((not_congr (hcentre a)).trans h2.symm)

    exact DistinctRings.step2 p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 ε ε₁ ε₂ hε₁ w
      ξ₁ hξ₁ ξ₂ hξ₂ hz1 hz2 V₁ V₂ hVA1 hVm1 hVj1 hVA2 hVm2 hVj2 φ1 hφ1 φ2 hφ2 hzeq

  have hV2 : V₂ = W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom := (hcount V₂ hVA2 hVm2 hVj2).resolve_left hV2ne

  have hσA : ∀ a : A, σ (algebraMap A ↥K a) = algebraMap A ↥K a := fun a => by
    rw [IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]
  have hA₁ : ∀ a : A, algebraMap A ↥K a ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom := fun a => by
    rw [ValuationSubring.mem_comap]
    change σ (algebraMap A ↥K a) ∈ W₀
    rw [hσA]
    exact (h1 0).1 a
  obtain ⟨θ, hθread, hθA⟩ :=
    ModularCurve.XOneP.exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation L K A W₀ h4
      (fun f x y hy hxy => (h6 f x y hy hxy).2) (h1 0).1 M w₀ (fun f x y hy hxy => (h6 f x y hy hxy).1) h7 σ hσA hA₁
  subst hV2
  letI := algV2
  obtain ⟨Φ, hΦ⟩ := ValuationSubring.exists_fractionRing_tensorProduct_quotient_algEquiv_apply_tmul_eq_coeffMap_of_residueField_ringEquiv
    A k hk hκk (W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) hVA2 halgV2 ϖ hϖ hunif2
    (ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w₀) θ hθA hLD
    (ModularCurve.igusaFunctionFieldX1C k M w₂) (ModularCurve.adjoin_image_coeffMap_igusaFunctionFieldX1C_eq (IsLocalRing.ResidueField A) k M w₀ w₂) 𝔮2 h𝔮2
  obtain ⟨Mdl₂, e₂, he₂, hne, hpin'⟩ := CIP.exists_pin_of_component L K A j k M w₂ C₂ c₂ i₂ MdlB eB heB _ hCV2 𝔮2 Ψ2 hne2 hpin2 Φ
    (fun a x y => ((σ (a : ↥K) : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
      HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (fun v => ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)
      ((θ (IsLocalRing.residue _ v) : ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w₀)) :
        LaurentSeries (IsLocalRing.ResidueField A)))
    hΦ
    (by
      intro a x y hy hxy
      have hy' : y.map (IsLocalRing.residue A) ≠ 0 := by
        intro h0; apply hy
        rw [← hσres, PowerSeries.map_comp, RingHom.comp_apply, h0, map_zero]
      show ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)
          ((θ (IsLocalRing.residue _ ⟨(a : ↥K), hCV2 a⟩) : ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w₀)) :
            LaurentSeries (IsLocalRing.ResidueField A)) = _
      rw [hθread ⟨(a : ↥K), hCV2 a⟩ x y hy' hxy, map_div₀, CIP.coeffMap_ofPowerSeries_map, CIP.coeffMap_ofPowerSeries_map, hσres])
  exact ⟨Mdl₂, e₂, he₂, hne, hpin'⟩

end S_ModularCurve_XOneP_exists_curveModel_iso_snd_gaussReading_algEquiv_of_gaussReading_fst_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_curveModel_iso_snd_gaussReading_algEquiv_of_gaussReading_fst_twoChartModel_x1_mul (solution)
