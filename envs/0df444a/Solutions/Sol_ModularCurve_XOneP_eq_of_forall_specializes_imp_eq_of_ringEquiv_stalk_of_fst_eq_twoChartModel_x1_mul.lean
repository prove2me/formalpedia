-- Prove2me | solution 1 for ModularCurve.XOneP.eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3da04f29-1e62-58f5-9830-70ff3fdbe1a0

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_pair_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_x1_mul
import Theorems.Thm_ModularCurve_XOneP_valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_ringEquiv_residueField_igusaFunctionFieldX1C_of_gaussPresentation
import Theorems.Thm_ModularCurve_XOneP_exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation
import Theorems.Thm_ModularCurve_adjoin_image_coeffMap_igusaFunctionFieldX1C_eq
import Theorems.Thm_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg"
p2m_attr_erase "simp" "WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

open scoped TensorProduct

namespace CIP2
theorem isDomain_tensorProduct_of_residueField_ringEquiv
    (A : Type) [CommRing A] [IsLocalRing A]
    (k : Type) [Field k] [Algebra A k] (hk : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A k a = 0)
    [Algebra (IsLocalRing.ResidueField A) k]
    (hκk : ∀ a : A, algebraMap (IsLocalRing.ResidueField A) k (IsLocalRing.residue A a) = algebraMap A k a)
    {K : Type} [Field K] [Algebra A K]
    (V : ValuationSubring K) (hVA : ∀ a : A, algebraMap A K a ∈ V)
    [Algebra A ↥V] (halgV : ∀ a : A, ((algebraMap A ↥V a : ↥V) : K) = algebraMap A K a)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (hunif : ∀ f : K, f ∈ V.nonunits → ∃ g : K, g ∈ V ∧ f = algebraMap A K ϖ * g)
    (E : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)))
    (θ : IsLocalRing.ResidueField ↥V ≃+* ↥E)
    (hθ : ∀ a : A, θ (IsLocalRing.residue ↥V ⟨algebraMap A K a, hVA a⟩) =
      algebraMap (IsLocalRing.ResidueField A) ↥E (IsLocalRing.residue A a))
    (hLD : ∀ (n : ℕ) (f : Fin n → LaurentSeries (IsLocalRing.ResidueField A)),
      LinearIndependent (IsLocalRing.ResidueField A) f →
      LinearIndependent k (⇑(ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)) ∘ f)) :
    IsDomain (k ⊗[A] ↥V) := by
  classical

  set S : Set (LaurentSeries k) :=
    ⇑(ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)) '' ((E : Set (LaurentSeries (IsLocalRing.ResidueField A)))) with hSdef
  set E' : IntermediateField k (LaurentSeries k) := IntermediateField.adjoin k S with hE'def

  have hϖ0 : algebraMap A k ϖ = 0 := hk ϖ (hϖ ▸ Ideal.mem_span_singleton_self ϖ)
  have htmul_nonunit : ∀ v : ↥V, (v : K) ∈ V.nonunits → (1 : k) ⊗ₜ[A] v = 0 := by
    intro v hv
    obtain ⟨g, hg, hvg⟩ := hunif v hv
    have hv' : v = algebraMap A ↥V ϖ * ⟨g, hg⟩ := Subtype.ext (by rw [Subring.coe_mul, halgV]; exact hvg)
    rw [hv', Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← TensorProduct.smul_tmul, Algebra.smul_def,
      hϖ0, zero_mul, TensorProduct.zero_tmul]
  have htmul_maximal : ∀ v : ↥V, v ∈ IsLocalRing.maximalIdeal ↥V → (1 : k) ⊗ₜ[A] v = 0 := fun v hv =>
    htmul_nonunit v (ValuationSubring.coe_mem_nonunits_iff.mpr hv)

  let ψL : ↥V →+* LaurentSeries k :=
    (ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)).comp ((algebraMap ↥E (LaurentSeries (IsLocalRing.ResidueField A))).comp
      ((θ : IsLocalRing.ResidueField ↥V →+* ↥E).comp (IsLocalRing.residue ↥V)))
  have hψL_mem : ∀ v : ↥V, ψL v ∈ E' := fun v =>
    IntermediateField.subset_adjoin k S ⟨_, (θ (IsLocalRing.residue ↥V v)).2, rfl⟩
  let ψ₀ : ↥V →+* ↥E' := ψL.codRestrict E' hψL_mem
  letI algAF : Algebra A ↥E' := ((algebraMap k ↥E').comp (algebraMap A k)).toAlgebra
  haveI : IsScalarTower A k ↥E' := IsScalarTower.of_algebraMap_eq (fun a => rfl)

  have hC : ∀ (F : Type) [Field F] (x : F), algebraMap F (LaurentSeries F) x = HahnSeries.C x := fun F _ x => by
    simp [HahnSeries.algebraMap_apply']
  have hmapC : ∀ x : IsLocalRing.ResidueField A, ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k) (HahnSeries.C x)
      = HahnSeries.C (algebraMap (IsLocalRing.ResidueField A) k x) := fun x => by
    ext n
    by_cases hn : n = 0
    · subst hn; simp [ModularCurve.coeffMap]
    · simp [ModularCurve.coeffMap, hn]
  have hψ₀A : ∀ a : A, ψ₀ (algebraMap A ↥V a) = algebraMap A ↥E' a := by
    intro a
    apply Subtype.ext
    have h1 : algebraMap A ↥V a = ⟨algebraMap A K a, hVA a⟩ := Subtype.ext (halgV a)
    show ψL (algebraMap A ↥V a) = ((algebraMap k ↥E' (algebraMap A k a) : ↥E') : LaurentSeries k)
    rw [h1]
    show ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)
        (((θ (IsLocalRing.residue ↥V ⟨algebraMap A K a, hVA a⟩)) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A))
      = algebraMap k (LaurentSeries k) (algebraMap A k a)
    rw [hθ a, show (((algebraMap (IsLocalRing.ResidueField A) ↥E) (IsLocalRing.residue A a) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A))
        = algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a) from rfl,
      hC, hmapC, hκk, hC]
  let ψ : ↥V →ₐ[A] ↥E' := { ψ₀ with commutes' := hψ₀A }
  let Φ : TensorProduct A k ↥V →ₐ[k] ↥E' :=
    Algebra.TensorProduct.lift (Algebra.ofId k ↥E') ψ (fun _ _ => Commute.all _ _)

  have hΦtmul : ∀ (a : k) (v : ↥V), Φ (a ⊗ₜ[A] v) = a • ψ₀ v := fun a v => by
    show Algebra.TensorProduct.lift _ _ _ (a ⊗ₜ[A] v) = _
    rw [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]
    rfl
  have hΦinj : Function.Injective Φ := by
    by_cases hunitϖ : IsUnit (algebraMap A ↥V ϖ)
    ·
      have h10 : (1 : TensorProduct A k ↥V) = 0 := by
        obtain ⟨u, hu⟩ := hunitϖ
        have h : (1 : k) ⊗ₜ[A] (1 : ↥V) = 0 := by
          have h1 : (1 : ↥V) = algebraMap A ↥V ϖ * ↑u⁻¹ := by rw [← hu, Units.mul_inv]
          rw [h1, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← TensorProduct.smul_tmul,
            Algebra.smul_def, hϖ0, zero_mul, TensorProduct.zero_tmul]
        exact h
      haveI : Subsingleton (TensorProduct A k ↥V) := subsingleton_of_zero_eq_one h10.symm
      exact fun x y _ => Subsingleton.elim x y

    have hloc : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥V a ∈ IsLocalRing.maximalIdeal ↥V := by
      intro a ha
      rw [hϖ, Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [map_mul]
      exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hunitϖ)
    let fκ : (IsLocalRing.ResidueField A) →+* IsLocalRing.ResidueField ↥V :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) ((IsLocalRing.residue ↥V).comp (algebraMap A ↥V))
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hloc a ha))
    letI algκV : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥V) := fκ.toAlgebra
    have halgκV : ∀ a : A, algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥V) (IsLocalRing.residue A a)
        = IsLocalRing.residue ↥V (algebraMap A ↥V a) := fun a => rfl

    letI algκF : Algebra (IsLocalRing.ResidueField A) ↥E' := ((algebraMap k ↥E').comp (algebraMap (IsLocalRing.ResidueField A) k)).toAlgebra
    haveI : IsScalarTower (IsLocalRing.ResidueField A) k ↥E' := IsScalarTower.of_algebraMap_eq (fun a => rfl)

    let ψκL : IsLocalRing.ResidueField ↥V →+* LaurentSeries k :=
      (ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)).comp ((algebraMap ↥E (LaurentSeries (IsLocalRing.ResidueField A))).comp
        (θ : IsLocalRing.ResidueField ↥V →+* ↥E))
    have hψκL_mem : ∀ r, ψκL r ∈ E' := fun r => IntermediateField.subset_adjoin k S ⟨_, (θ r).2, rfl⟩
    let ψκ₀ : IsLocalRing.ResidueField ↥V →+* ↥E' := ψκL.codRestrict E' hψκL_mem
    have hψκ₀ψ₀ : ∀ v : ↥V, ψκ₀ (IsLocalRing.residue ↥V v) = ψ₀ v := fun v => rfl
    have hψκ₀κ : ∀ r : IsLocalRing.ResidueField A, ψκ₀ (algebraMap (IsLocalRing.ResidueField A) _ r) = algebraMap (IsLocalRing.ResidueField A) ↥E' r := by
      intro r
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) r
      rw [halgκV, hψκ₀ψ₀, hψ₀A]
      apply Subtype.ext
      show ((algebraMap k ↥E' (algebraMap A k a) : ↥E') : LaurentSeries k)
        = ((algebraMap k ↥E' (algebraMap (IsLocalRing.ResidueField A) k (IsLocalRing.residue A a)) : ↥E') : LaurentSeries k)
      rw [hκk]
    let ψκ : IsLocalRing.ResidueField ↥V →ₐ[IsLocalRing.ResidueField A] ↥E' := { ψκ₀ with commutes' := hψκ₀κ }
    let Φκ : TensorProduct (IsLocalRing.ResidueField A) k (IsLocalRing.ResidueField ↥V) →ₐ[k] ↥E' :=
      Algebra.TensorProduct.lift (Algebra.ofId k ↥E') ψκ (fun _ _ => Commute.all _ _)

    let ρ₀ : ↥V →+* TensorProduct (IsLocalRing.ResidueField A) k (IsLocalRing.ResidueField ↥V) :=
      (Algebra.TensorProduct.includeRight.toRingHom : IsLocalRing.ResidueField ↥V →+* _).comp (IsLocalRing.residue ↥V)
    have hρ₀A : ∀ a : A, ρ₀ (algebraMap A ↥V a) = algebraMap A _ a := by
      intro a
      rw [IsScalarTower.algebraMap_apply A k (TensorProduct (IsLocalRing.ResidueField A) k (IsLocalRing.ResidueField ↥V))]
      show (1 : k) ⊗ₜ[IsLocalRing.ResidueField A] (IsLocalRing.residue ↥V (algebraMap A ↥V a))
        = algebraMap k (TensorProduct (IsLocalRing.ResidueField A) k (IsLocalRing.ResidueField ↥V)) (algebraMap A k a)
      rw [← halgκV, ← hκk, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    let ρ : ↥V →ₐ[A] TensorProduct (IsLocalRing.ResidueField A) k (IsLocalRing.ResidueField ↥V) := { ρ₀ with commutes' := hρ₀A }
    let π : TensorProduct A k ↥V →ₐ[k] TensorProduct (IsLocalRing.ResidueField A) k (IsLocalRing.ResidueField ↥V) :=
      Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft ρ (fun _ _ => Commute.all _ _)
    have hπtmul : ∀ (a : k) (v : ↥V), π (a ⊗ₜ[A] v) = a ⊗ₜ[IsLocalRing.ResidueField A] IsLocalRing.residue ↥V v := fun a v => by
      show Algebra.TensorProduct.lift _ _ _ (a ⊗ₜ[A] v) = _
      rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply]
      show (a ⊗ₜ[IsLocalRing.ResidueField A] (1 : IsLocalRing.ResidueField ↥V)) * ((1 : k) ⊗ₜ[IsLocalRing.ResidueField A] IsLocalRing.residue ↥V v) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

    have hfac : ∀ x, Φ x = Φκ (π x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a v =>
        rw [hΦtmul, hπtmul]
        show _ = Algebra.TensorProduct.lift _ _ _ (a ⊗ₜ[IsLocalRing.ResidueField A] _)
        rw [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]
        rfl
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

    let σV : IsLocalRing.ResidueField ↥V →+* TensorProduct A k ↥V :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥V)
        (Algebra.TensorProduct.includeRight.toRingHom : ↥V →+* TensorProduct A k ↥V)
        (fun v hv => htmul_maximal v hv)
    have hσV : ∀ v : ↥V, σV (IsLocalRing.residue ↥V v) = (1 : k) ⊗ₜ[A] v := fun v => rfl
    have hπinj : Function.Injective π := by

      have hσVκ : ∀ r : IsLocalRing.ResidueField A, σV (algebraMap (IsLocalRing.ResidueField A) _ r) = algebraMap (IsLocalRing.ResidueField A) (TensorProduct A k ↥V) r := by
        intro r
        obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := A) r
        rw [halgκV, hσV, IsScalarTower.algebraMap_apply (IsLocalRing.ResidueField A) k (TensorProduct A k ↥V), hκk,
          Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      let σVa : IsLocalRing.ResidueField ↥V →ₐ[IsLocalRing.ResidueField A] TensorProduct A k ↥V := { σV with commutes' := hσVκ }
      let σ : TensorProduct (IsLocalRing.ResidueField A) k (IsLocalRing.ResidueField ↥V) →ₐ[k] TensorProduct A k ↥V :=
        Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft σVa (fun _ _ => Commute.all _ _)
      have hσπ : ∀ x, σ (π x) = x := by
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a v =>
          rw [hπtmul]
          show Algebra.TensorProduct.lift _ _ _ (a ⊗ₜ[IsLocalRing.ResidueField A] _) = _
          rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply]
          show (a ⊗ₜ[A] (1 : ↥V)) * σV (IsLocalRing.residue ↥V v) = _
          rw [hσV, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        | add x y hx hy => rw [map_add, map_add, hx, hy]
      exact fun x y hxy => by rw [← hσπ x, ← hσπ y, hxy]

    have hΦκinj : Function.Injective Φκ := by
      let B := Module.Free.chooseBasis (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥V)
      let BT := Algebra.TensorProduct.basis k B
      have hBT : ∀ i, Φκ (BT i) = ψκ₀ (B i) := fun i => by
        rw [Algebra.TensorProduct.basis_apply]
        show Algebra.TensorProduct.lift _ _ _ _ = _
        rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rfl

      have hθκ : ∀ (c : IsLocalRing.ResidueField A) (r : IsLocalRing.ResidueField ↥V),
          ((θ (c • r) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A)) = c • ((θ r : ↥E) : LaurentSeries (IsLocalRing.ResidueField A)) := by
        intro c r
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) c
        have h1 : algebraMap A ↥V a = ⟨algebraMap A K a, hVA a⟩ := Subtype.ext (halgV a)
        rw [Algebra.smul_def, map_mul, halgκV, h1, hθ a, ← HahnSeries.C_mul_eq_smul, ← hC]
        rfl

      let θL : IsLocalRing.ResidueField ↥V →ₗ[IsLocalRing.ResidueField A] LaurentSeries (IsLocalRing.ResidueField A) :=
        { toFun := fun r => ((θ r : ↥E) : LaurentSeries (IsLocalRing.ResidueField A))
          map_add' := fun x y => by simp only [map_add]; rfl
          map_smul' := fun c r => hθκ c r }
      have hθLinj : LinearMap.ker θL = ⊥ := LinearMap.ker_eq_bot.mpr (fun x y hxy =>
        θ.injective (Subtype.ext hxy))
      have hBθ : LinearIndependent (IsLocalRing.ResidueField A) (fun i => ((θ (B i) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A))) :=
        B.linearIndependent.map' θL hθLinj
      have hli : LinearIndependent k (fun i => Φκ (BT i)) := by
        rw [linearIndependent_iff']
        intro s g hsum i hi

        have hval : ∀ j, ((Φκ (BT j) : ↥E') : LaurentSeries k)
            = ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k) ((θ (B j) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A)) := fun j => by
          rw [hBT]; rfl
        have hsum' : ∑ j ∈ s, g j • ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)
            ((θ (B j) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A)) = 0 := by
          have h := congrArg (fun y : ↥E' => (y : LaurentSeries k)) hsum
          try simp only at h
          rw [AddSubmonoidClass.coe_finset_sum, ZeroMemClass.coe_zero] at h
          rw [← h]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [IntermediateField.coe_smul, Algebra.smul_def, hC, HahnSeries.C_mul_eq_smul, hval]

        let e : Fin s.card ≃ ↥s := s.equivFin.symm
        have hf : LinearIndependent (IsLocalRing.ResidueField A) (fun j : Fin s.card => ((θ (B (e j)) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A))) :=
          hBθ.comp (fun j => ((e j) : _)) (fun j₁ j₂ h => e.injective (Subtype.ext h))
        have hk' := hLD s.card _ hf
        rw [Fintype.linearIndependent_iff] at hk'
        have hz := hk' (fun j => g (e j)) (by
          rw [← hsum']
          rw [← Finset.sum_coe_sort s]
          exact (Equiv.sum_comp e (fun x : ↥s => g x • ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)
            ((θ (B x) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A)))))
          (e.symm ⟨i, hi⟩)
        simpa using hz

      intro x y hxy
      have hrepr : ∀ z, Φκ z = Finsupp.linearCombination k (fun i => Φκ (BT i)) (BT.repr z) := by
        intro z
        conv_lhs => rw [← BT.linearCombination_repr z]
        rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
        simp only [map_smul]
      rw [hrepr, hrepr] at hxy
      exact BT.repr.injective (hli hxy)
    intro x y hxy
    apply hπinj
    apply hΦκinj
    rw [← hfac, ← hfac, hxy]

  exact hΦinj.isDomain Φ.toRingHom

end CIP2

namespace S2B
open ModularCurve.TwoChart

variable (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem exists_stalk_iso_localization_chartAlgFin
    (x : ↥(ModularCurve.TwoChartModel R F j)) (y : ↥(XFin R F j)) (hxy : (ιFin R F j).base y = x) :
    ∃ (e : (ModularCurve.TwoChartModel R F j).presheaf.stalk x ≅ CommRingCat.of (Localization.AtPrime y.asIdeal)),
      (∀ r : R, e.hom (((ModularCurve.TwoChartModel R F j).presheaf.germ ⊤ x trivial).hom
          (((modelTo R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))
        = algebraMap ↥(chartAlgFin R F j) (Localization.AtPrime y.asIdeal) (algebraMap R ↥(chartAlgFin R F j) r)) ∧
      (∀ (hx : x ∈ (ιFin R F j) ''ᵁ ⊤) (a : ↥(chartAlgFin R F j)),
        e.hom (((ModularCurve.TwoChartModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) x hx).hom
          (((ιFin R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv a)))
        = algebraMap ↥(chartAlgFin R F j) (Localization.AtPrime y.asIdeal) a) := by
  subst hxy
  haveI : IsIso ((ιFin R F j).stalkMap y) := inferInstance
  let e : (ModularCurve.TwoChartModel R F j).presheaf.stalk ((ιFin R F j).base y) ≅
      CommRingCat.of (Localization.AtPrime y.asIdeal) :=
    asIso ((ιFin R F j).stalkMap y) ≪≫ Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F j)) y
  have hstalk : ∀ c : ↥(chartAlgFin R F j),
      (Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F j)) y).hom.hom
        (((XFin R F j).presheaf.germ ⊤ y trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom c)) =
      algebraMap ↥(chartAlgFin R F j) (Localization.AtPrime y.asIdeal) c := by
    intro c
    have h3 := congrArg (fun φ : CommRingCat.of ↥(chartAlgFin R F j) ⟶ _ => φ.hom c)
      (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of ↥(chartAlgFin R F j)) y)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
    first
      | rw [← h3]
      | erw [← h3]
    change ((Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F j)) y).inv ≫ (Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F j)) y).hom).hom _ = _
    rw [Iso.inv_hom_id]
    rfl
  refine ⟨e, fun r => ?_, fun hx a => ?_⟩
  · change (Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F j)) y).hom.hom
        (((ιFin R F j).stalkMap y).hom (((ModularCurve.TwoChartModel R F j).presheaf.germ ⊤ ((ιFin R F j).base y) trivial).hom
          (((modelTo R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) = _
    rw [Scheme.Hom.germ_stalkMap_apply (ιFin R F j) ⊤ y trivial]
    have h1 : ((ιFin R F j).app ⊤).hom (((modelTo R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
        ((Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F j)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
      change (((modelTo R F j).appTop ≫ (ιFin R F j).appTop)).hom _ = _
      rw [← Scheme.Hom.comp_appTop, ιFin_modelTo]
    have h2 : ((Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F j)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
        (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom (algebraMap R ↥(chartAlgFin R F j) r) := by
      have hn := congrArg (fun φ : CommRingCat.of R ⟶ _ => φ.hom r)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F j))))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
      exact hn.symm
    rw [h1, h2]
    exact hstalk _
  · change (Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F j)) y).hom.hom
        (((ιFin R F j).stalkMap y).hom (((ModularCurve.TwoChartModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base y) hx).hom
          (((ιFin R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv a)))) = _
    rw [Scheme.Hom.germ_stalkMap_apply (ιFin R F j) ((ιFin R F j) ''ᵁ ⊤) y hx]
    have h4 : ((ιFin R F j).app ((ιFin R F j) ''ᵁ ⊤)).hom
          (((ιFin R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv a)) =
        ((XFin R F j).presheaf.map (eqToHom ((ιFin R F j).preimage_image_eq ⊤)).op).hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv a) := by
      change (((ιFin R F j).appIso ⊤).inv ≫ (ιFin R F j).app ((ιFin R F j) ''ᵁ ⊤)).hom _ = _
      rw [Scheme.Hom.appIso_inv_app]
    rw [h4]
    erw [(XFin R F j).presheaf.germ_res_apply]
    exact hstalk a

end S2B

open ModularCurve.TwoChart in
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

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k] :
    ∀ (y y' : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
      (_ : ∀ t, t ⤳ y → t = y) (_ : ∀ t, t ⤳ y' → t = y')
      (V : ValuationSubring ↥K)
      (_ : ∀ a : A, algebraMap A ↥K a ∈ V)
      (_ : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits)
      (_ : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 → Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)
      (hz : (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y ∈ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
      (φ : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y) ≃+* ↥V)
      (_ : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        ((φ (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y) hz).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))) : ↥V) : ↥K) = (a : ↥K)),
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y =
        (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y' → y = y' := by
  intro y y' hymin hy'min V hVA hVm hVj hz φ hφ heq
  classical
  haveI hp : Fact p.Prime := inferInstance

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq
  have hp0 : (p : A) ≠ 0 := fun h =>
    (Nat.cast_ne_zero.mpr hp.out.ne_zero : (p : L) ≠ 0) (by rw [← map_natCast (algebraMap A L), h, map_zero])
  have hker : IsLocalRing.maximalIdeal A ≤ RingHom.ker (algebraMap A k) := by
    have hkp : (RingHom.ker (algebraMap A k)).IsPrime := RingHom.ker_isPrime _
    have hpk : (p : A) ∈ RingHom.ker (algebraMap A k) := by
      rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    have hne : RingHom.ker (algebraMap A k) ≠ ⊥ := fun h => hp0 (by rwa [h, Ideal.mem_bot] at hpk)
    rw [IsLocalRing.eq_maximalIdeal ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime A).mp ‹_› |>.2
      |> fun _ => hkp.isMaximal hne)]
  have hk : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A k a = 0 := fun a ha => hker ha
  letI algκk : Algebra (IsLocalRing.ResidueField A) k :=
    (Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (algebraMap A k) hk).toAlgebra
  have hκk : ∀ a : A, algebraMap (IsLocalRing.ResidueField A) k (IsLocalRing.residue A a) = algebraMap A k a := fun a => rfl
  have hLD : ∀ (n : ℕ) (g : Fin n → LaurentSeries (IsLocalRing.ResidueField A)),
      LinearIndependent (IsLocalRing.ResidueField A) g →
      LinearIndependent k (⇑(ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)) ∘ g) :=
    fun n g hg => ModularCurve.linearIndependent_coeffMap_comp_of_linearIndependent (IsLocalRing.ResidueField A) k g hg
  obtain ⟨w₀⟩ := ModularCurve.nonempty_integralWeightOneForm (IsLocalRing.ResidueField A) M (by omega)
  obtain ⟨w'⟩ := ModularCurve.nonempty_integralWeightOneForm k M (by omega)
  obtain ⟨W₀, W₁, h1, -, -, h4, -, h6, h7⟩ :=
    ModularCurve.XOneP.exists_valuationSubring_pair_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj w₀
  obtain ⟨σ, hσj, -, hσ3⟩ :=
    ModularCurve.XOneP.exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj
  obtain ⟨hσW, hσj'⟩ := hσ3 W₀ h4
  obtain ⟨hcomp, hram, -, -⟩ :=
    ModularCurve.XOneP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj w₀ ϖ hϖ W₀ h4 σ hσj hσW hσj'
  have hunif := hram V hVA hVm hVj
  have hA₀ : ∀ a : A, algebraMap A ↥K a ∈ W₀ := (h1 0).1
  have hnu : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0) := fun f x y hy hxy => (h6 f x y hy hxy).2
  have hmem := fun f x y hy hxy => (h6 f x y hy hxy).1
  have hσA : ∀ a : A, σ (algebraMap A ↥K a) = algebraMap A ↥K a := fun a => by
    rw [IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]
  have hθex : ∃ θ : IsLocalRing.ResidueField ↥V ≃+* ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w₀),
      ∀ a : A, θ (IsLocalRing.residue ↥V ⟨algebraMap A ↥K a, hVA a⟩) =
        algebraMap (IsLocalRing.ResidueField A) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w₀)
          (IsLocalRing.residue A a) := by
    rcases hcomp V hVA hVm hVj with rfl | rfl
    · obtain ⟨θ, -, hθc⟩ := ModularCurve.XOneP.exists_ringEquiv_residueField_igusaFunctionFieldX1C_of_gaussPresentation
        L K A _ h4 hnu hVA M w₀ hmem h7
      exact ⟨θ, hθc⟩
    · obtain ⟨θ, -, hθc⟩ := ModularCurve.XOneP.exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation
        L K A _ h4 hnu hA₀ M w₀ hmem h7 σ hσA hVA
      exact ⟨θ, hθc⟩
  obtain ⟨θ, hθA⟩ := hθex

  letI algV : Algebra A ↥V := ((algebraMap A ↥K).codRestrict V.toSubring hVA).toAlgebra
  have halgV : ∀ a : A, ((algebraMap A ↥V a : ↥V) : ↥K) = algebraMap A ↥K a := fun a => rfl
  haveI hdom : IsDomain (k ⊗[A] ↥V) :=
    CIP2.isDomain_tensorProduct_of_residueField_ringEquiv A k hk hκk V hVA halgV ϖ hϖ hunif
      (ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w₀) θ hθA hLD

  have hzimg : ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y) ∈ (((ModularCurve.TwoChart.ιFin A (↥K) j)).base '' (Set.univ : Set ↥(XFin A (↥K) j))) := by
    simpa using hz
  obtain ⟨yF, -, hyF⟩ := hzimg
  obtain ⟨e, heconst, hechart⟩ := S2B.exists_stalk_iso_localization_chartAlgFin A (↥K) j ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y) yF hyF
  have heinj : Function.Injective e.hom := e.commRingCatIsoToRingEquiv.injective
  have hconst : ∀ r : A,
      ((ModularCurve.TwoChartModel A (↥K) j).presheaf.germ ⊤ ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y) trivial).hom (((ModularCurve.TwoChart.modelTo A (↥K) j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r))
        = ((ModularCurve.TwoChartModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y) hz).hom
            (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin A (↥K) j))).inv
              (algebraMap A ↥(chartAlgFin A (↥K) j) r))) := by
    intro r
    apply heinj
    rw [heconst r, hechart hz (algebraMap A _ r)]

  have hU : IsAffineOpen ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) := (isAffineOpen_top (XFin A (↥K) j)).image_of_isOpenImmersion (ModularCurve.TwoChart.ιFin A (↥K) j)
  let ρ : A →+* Γ((ModularCurve.TwoChartModel A (↥K) j), ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)) := (((ModularCurve.TwoChart.modelTo A (↥K) j).appLE ⊤ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) le_top).hom).comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  letI algSt : Algebra A ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y)) := (((ModularCurve.TwoChartModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y) hz).hom.comp ρ).toAlgebra
  have hφA : ∀ a : A, φ (algebraMap A ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y)) a) = algebraMap A ↥V a := by
    intro a
    apply Subtype.ext
    rw [halgV]
    show ((φ (((ModularCurve.TwoChartModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y) hz).hom (((ModularCurve.TwoChart.modelTo A (↥K) j).appLE ⊤ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) : ↥V) : ↥K) = algebraMap A ↥K a
    have hres : ((ModularCurve.TwoChartModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y) hz).hom (((ModularCurve.TwoChart.modelTo A (↥K) j).appLE ⊤ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
        = ((ModularCurve.TwoChartModel A (↥K) j).presheaf.germ ⊤ ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y) trivial).hom (((ModularCurve.TwoChart.modelTo A (↥K) j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) := by
      rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
      exact TopCat.Presheaf.germ_res_apply (ModularCurve.TwoChartModel A (↥K) j).presheaf (homOfLE le_top) ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y) hz _
    rw [hres, hconst a]
    exact hφ (algebraMap A _ a)
  let φA : ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y)) ≃ₐ[A] ↥V := AlgEquiv.ofRingEquiv (f := φ) hφA
  haveI hdomSt : IsDomain (((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y)) ⊗[A] k) :=
    MulEquiv.isDomain (k ⊗[A] ↥V)
      (((Algebra.TensorProduct.congr φA (AlgEquiv.refl : k ≃ₐ[A] k)).trans (Algebra.TensorProduct.comm A ↥V k)).toMulEquiv)

  have hρ : CommRingCat.ofHom ρ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ModularCurve.TwoChart.modelTo A (↥K) j).appLE ⊤ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) le_top := rfl
  have hfromSpec : hU.fromSpec ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = Spec.map (CommRingCat.ofHom ρ) := by
    rw [hρ, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
      IsAffineOpen.SpecMap_appLE_fromSpec (ModularCurve.TwoChart.modelTo A (↥K) j) (isAffineOpen_top (Spec (CommRingCat.of A))) hU (le_top : ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ≤ (ModularCurve.TwoChart.modelTo A (↥K) j) ⁻¹ᵁ ⊤)]
  have hSpec : (ModularCurve.TwoChartModel A (↥K) j).fromSpecStalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y) ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = Spec.map (CommRingCat.ofHom (algebraMap A ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y)))) := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hz, IsAffineOpen.fromSpecStalk, Category.assoc, hfromSpec, ← Spec.map_comp]
    rfl
  let G := pullback (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ((ModularCurve.TwoChartModel A (↥K) j).fromSpecStalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y))
  let eG : G ≅ Spec (CommRingCat.of (((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y)) ⊗[A] k)) :=
    pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ((ModularCurve.TwoChartModel A (↥K) j).fromSpecStalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y))
      ≪≫ pullback.congrHom hSpec rfl ≪≫ pullbackSpecIso A ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y)) k
  haveI : IrreducibleSpace ↥(Spec (CommRingCat.of (((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y)) ⊗[A] k))) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y)) ⊗[A] k)))
  haveI hGirr : IrreducibleSpace ↥G :=
    Function.Surjective.irreducibleSpace (f := eG.inv.base) eG.inv.base.hom.continuous (Scheme.homeoOfIso eG.symm).surjective

  obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))) (g := (ModularCurve.TwoChartModel A (↥K) j).fromSpecStalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y)) y
    (IsLocalRing.closedPoint ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y))) (by rw [Scheme.fromSpecStalk_closedPoint])
  obtain ⟨t', ht', -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))) (g := (ModularCurve.TwoChartModel A (↥K) j).fromSpecStalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y)) y'
    (IsLocalRing.closedPoint ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y))) (by rw [Scheme.fromSpecStalk_closedPoint]; exact heq.symm)
  have hg : ∀ s : ↥G, (pullback.fst (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ((ModularCurve.TwoChartModel A (↥K) j).fromSpecStalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y))).base (genericPoint ↥G) ⤳ (pullback.fst (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ((ModularCurve.TwoChartModel A (↥K) j).fromSpecStalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y))).base s :=
    fun s => ((genericPoint_spec ↥G).specializes (Set.mem_univ s)).map (pullback.fst (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ((ModularCurve.TwoChartModel A (↥K) j).fromSpecStalk ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base y))).base.hom.continuous
  have e1 := hymin _ (ht ▸ hg t)
  have e2 := hy'min _ (ht' ▸ hg t')
  exact e1.symm.trans e2

end S_ModularCurve_XOneP_eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul (solution)
