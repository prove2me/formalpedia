-- Prove2me | solution 1 for ModularCurve.XOneP.comp_fibreAut_eq_of_galoisModelAut_of_gaussPin_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b752796a-f4c0-564a-a11b-a45e5f159b68

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_CurveModel_pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq
import Theorems.Thm_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul
import Theorems.Thm_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_comp_fibreAut_eq_of_galoisModelAut_of_gaussPin_twoChartModel_x1_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module"
p2m_attr_erase "instance" "TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobTwist

universe u

section liftThrough

variable {C Y : Scheme.{u}} (i : C ⟶ Y) [IsClosedImmersion i] (i' : C ⟶ Y) [IsReduced C]
  (hrange : Set.range i'.base ⊆ Set.range i.base)

omit [IsClosedImmersion i] [IsReduced C] in
include hrange in
theorem surjective_snd_base : Function.Surjective (pullback.snd i i').base := by
  intro c
  obtain ⟨b, hb⟩ := hrange ⟨c, rfl⟩
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback b c hb
  exact ⟨z, hz⟩

include hrange in
theorem isIso_snd : IsIso (pullback.snd i i') := by
  haveI : Surjective (pullback.snd i i') := ⟨surjective_snd_base i i' hrange⟩
  exact isIso_of_isClosedImmersion_of_surjective _

noncomputable def liftThrough : C ⟶ C :=
  haveI := isIso_snd i i' hrange
  inv (pullback.snd i i') ≫ pullback.fst i i'

@[reassoc (attr := simp)]
theorem liftThrough_comp : liftThrough i i' hrange ≫ i = i' := by
  haveI := isIso_snd i i' hrange
  rw [liftThrough, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

end liftThrough

section liftAut

variable {C Y : Scheme.{u}} (i : C ⟶ Y) [IsClosedImmersion i] [IsReduced C] (τ : Y ≅ Y)
  (hτ : τ.hom.base '' Set.range i.base ⊆ Set.range i.base)
  (hτ' : τ.inv.base '' Set.range i.base ⊆ Set.range i.base)

omit [IsClosedImmersion i] [IsReduced C] in
include hτ in
theorem range_comp_hom_subset : Set.range (i ≫ τ.hom).base ⊆ Set.range i.base := by
  rintro _ ⟨c, rfl⟩
  exact hτ ⟨i.base c, ⟨c, rfl⟩, by simp⟩

omit [IsClosedImmersion i] [IsReduced C] in
include hτ' in
theorem range_comp_inv_subset : Set.range (i ≫ τ.inv).base ⊆ Set.range i.base := by
  rintro _ ⟨c, rfl⟩
  exact hτ' ⟨i.base c, ⟨c, rfl⟩, by simp⟩

noncomputable def liftAut : C ≅ C where
  hom := liftThrough i (i ≫ τ.hom) (range_comp_hom_subset i τ hτ)
  inv := liftThrough i (i ≫ τ.inv) (range_comp_inv_subset i τ hτ')
  hom_inv_id := by
    rw [← cancel_mono i, Category.assoc, liftThrough_comp, liftThrough_comp_assoc, Category.assoc,
      τ.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono i, Category.assoc, liftThrough_comp, liftThrough_comp_assoc, Category.assoc,
      τ.inv_hom_id, Category.comp_id, Category.id_comp]

@[reassoc (attr := simp)]
theorem liftAut_hom_comp : (liftAut i τ hτ hτ').hom ≫ i = i ≫ τ.hom :=
  liftThrough_comp i (i ≫ τ.hom) (range_comp_hom_subset i τ hτ)

end liftAut

theorem image_range_subset_of_fix {C₁ Y : Scheme.{u}} (i₁ : C₁ ⟶ Y) [IsClosedImmersion i₁] [IrreducibleSpace ↥C₁]
    (Z₂ : Set ↥Y) (hZ₂ : IsClosed Z₂) (hcover : ∀ z : ↥Y, z ∈ Set.range i₁.base ∨ z ∈ Z₂)
    (f : ↥Y → ↥Y) (hf : Continuous f) (P : ↥Y) (hP : f P = P) (hP₁ : P ∈ Set.range i₁.base) (hP₂ : P ∉ Z₂) :
    f '' Set.range i₁.base ⊆ Set.range i₁.base := by
  have hirr : IsPreirreducible (f '' Set.range i₁.base) := by
    rw [← Set.image_univ, ← Set.image_comp]
    exact (IrreducibleSpace.isIrreducible_univ _).isPreirreducible.image _ (hf.comp i₁.continuous).continuousOn
  have hcl : IsClosed (Set.range i₁.base) := i₁.isClosedEmbedding.isClosed_range
  have hsub : f '' Set.range i₁.base ⊆ Set.range i₁.base ∪ Z₂ := fun z _ => hcover z
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hirr) _ _ hcl hZ₂ hsub with h | h
  · exact h
  · exact absurd (h ⟨P, hP₁, hP⟩) hP₂

end FrobTwist

namespace GalPlacesTools

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

theorem appIso_hom_res_app_appIso_inv_apply
    {X Y : Scheme} (f : Y ⟶ X) {A B : CommRingCat} (ι : Spec A ⟶ X) [IsOpenImmersion ι]
    (g : Spec B ⟶ Y) [IsOpenImmersion g] (θ : A ⟶ B) (hfac : g ≫ f = Spec.map θ ≫ ι) (a : A)
    (V' : (Spec B).Opens) (hV' : g ''ᵁ V' ≤ f ⁻¹ᵁ (ι ''ᵁ ⊤)) :
    (g.appIso V').hom (Y.presheaf.map (homOfLE hV').op
      ((f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a)))) =
    (Spec B).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso B).inv (θ a)) := by
  let V : X.Opens := ι ''ᵁ ⊤
  let r := (Scheme.ΓSpecIso A).inv a
  show (g.appIso V').hom (Y.presheaf.map (homOfLE hV').op ((f.app V) ((ι.appIso ⊤).inv r))) = _
  have e1 := CategoryTheory.ConcreteCategory.congr_hom (g.appIso_hom V')
    (Y.presheaf.map (homOfLE hV').op ((f.app V) ((ι.appIso ⊤).inv r)))
  rw [CategoryTheory.comp_apply] at e1
  rw [e1]
  have e2 := CategoryTheory.ConcreteCategory.congr_hom (g.naturality (homOfLE hV').op) ((f.app V) ((ι.appIso ⊤).inv r))
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e2
  rw [e2]
  have e3 := CategoryTheory.ConcreteCategory.congr_hom
    ((Scheme.Hom.comp_app g f V).symm.trans ((Scheme.Hom.congr_app hfac V).trans
      (congrArg (· ≫ (Spec B).presheaf.map _) (Scheme.Hom.comp_app (Spec.map θ) ι V))))
    ((ι.appIso ⊤).inv r)
  erw [e3]
  erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply]
  have e4 := CategoryTheory.ConcreteCategory.congr_hom (ι.appIso_inv_app ⊤) r
  rw [CategoryTheory.comp_apply] at e4
  erw [e4]
  have e5 := CategoryTheory.ConcreteCategory.congr_hom
    ((Spec.map θ).naturality (eqToHom (ι.preimage_image_eq ⊤)).op) r
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e5
  erw [e5]
  have e6 := CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality θ) a
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e6
  erw [← e6]
  simp only [← CategoryTheory.comp_apply]
  rfl

end GalPlacesTools

namespace FrobPTTools

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

section FFMap

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (θ : X ⟶ Y) [IsIso θ]

theorem genericPoint_specializes : θ.base (genericPoint X) ⤳ genericPoint Y := by
  rw [genericPoint_eq_of_isOpenImmersion θ]

noncomputable def ffMap : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (genericPoint_specializes θ) ≫ θ.stalkMap (genericPoint X)

@[reassoc]
theorem SpecMap_ffMap_fromSpecStalk :
    Spec.map (ffMap θ) ≫ Y.fromSpecStalk (genericPoint Y) = X.fromSpecStalk (genericPoint X) ≫ θ := by
  rw [ffMap, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem ffMap_germ_apply (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    ffMap θ (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (θ ⁻¹ᵁ U) (genericPoint X)
        (show θ.base (genericPoint X) ∈ U by rwa [genericPoint_eq_of_isOpenImmersion θ]) (θ.app U s) := by
  rw [← CommRingCat.comp_apply, ffMap, TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
  rfl

theorem ffMap_germ_of_eq {Z : Scheme.{u}} (g₂ : Y ⟶ Z) (g₁ : X ⟶ Z) (e : g₁ = θ ≫ g₂)
    (U : Z.Opens) (h₂ : genericPoint Y ∈ g₂ ⁻¹ᵁ U) (h₁ : genericPoint X ∈ g₁ ⁻¹ᵁ U) (s : Γ(Z, U)) :
    ffMap θ (Y.presheaf.germ (g₂ ⁻¹ᵁ U) (genericPoint Y) h₂ (g₂.app U s)) =
      X.presheaf.germ (g₁ ⁻¹ᵁ U) (genericPoint X) h₁ (g₁.app U s) := by
  subst e
  rw [ffMap_germ_apply]
  rfl

end FFMap

section Laurent

open HahnSeries

variable {A B : Type*} [CommRing A] [CommRing B]

theorem coeffMap_ofPowerSeries (f : A →+* B) (g : PowerSeries A) :
    ModularCurve.coeffMap f (HahnSeries.ofPowerSeries ℤ A g) =
      HahnSeries.ofPowerSeries ℤ B (PowerSeries.map f g) := by
  ext n
  rw [ModularCurve.coeffMap_coeff]
  change f ((g : LaurentSeries A).coeff n) = ((PowerSeries.map f g : PowerSeries B) : LaurentSeries B).coeff n
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · rw [map_zero]
  · rw [PowerSeries.coeff_map]

end Laurent

end FrobPTTools

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open FrobPTTools

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

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

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

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

    (s : L ≃ₐ[ℚ] L) (hsk : ∀ a : A, algebraMap A k (s • a) = algebraMap A k a)

    (ws : ModularCurve.TwoChartModel A (↥K) j ≅ ModularCurve.TwoChartModel A (↥K) j)
    (hws : ws.hom ≫ ModularCurve.TwoChart.modelTo A (↥K) j =
      ModularCurve.TwoChart.modelTo A (↥K) j ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))
    (ρs : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hρs : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      (((ρs b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
        ModularCurve.coeffMap (s : L →+* L) ((b : ↥K) : LaurentSeries L))
    (hwρ : ModularCurve.TwoChart.ιFin A (↥K) j ≫ ws.hom = Spec.map (CommRingCat.ofHom ρs.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)

    (hεs : ε.1 ≫ ws.hom = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) ≫ ε.1)

    (hεC₂ : ∀ t, ((sectionBaseChange k ε).1).base t ∉ Set.range i₂.1.base)

    (wk : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≅ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (hwk₁ : wk.hom ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ ws.hom)
    (hwk₂ : wk.hom ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) :

    i₁.1 ≫ wk.hom = i₁.1 := by
  classical

  have hsA : (algebraMap A k).comp (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s) = algebraMap A k :=
    RingHom.ext fun a => by rw [RingHom.comp_apply, MulSemiringAction.toRingHom_apply]; exact hsk a
  have hspec : specMap A k ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) = specMap A k := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hsA]

  have hsbc : (sectionBaseChange k ε).1 ≫ wk.hom = (sectionBaseChange k ε).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, hwk₁, ← Category.assoc, sectionBaseChange_coe_fst, Category.assoc, hεs, ← Category.assoc, hspec]
    · rw [Category.assoc, hwk₂]
  have hsbc' : (sectionBaseChange k ε).1 ≫ wk.inv = (sectionBaseChange k ε).1 := by
    rw [← cancel_mono wk.hom, Category.assoc, wk.inv_hom_id, Category.comp_id, hsbc]
  let P : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) :=
    ((sectionBaseChange k ε).1).base (IsLocalRing.closedPoint k)
  have hP₁ : P ∈ Set.range i₁.1.base := ⟨ε₁.1.base (IsLocalRing.closedPoint k), by
    show (ε₁.1 ≫ i₁.1).base _ = _; rw [hε₁]⟩
  have hP₂ : P ∉ Set.range i₂.1.base := hεC₂ _
  have hPfix : wk.hom.base P = P := by
    show ((sectionBaseChange k ε).1 ≫ wk.hom).base _ = _; rw [hsbc]
  have hPfix' : wk.inv.base P = P := by
    show ((sectionBaseChange k ε).1 ≫ wk.inv).base _ = _; rw [hsbc']

  haveI : IsIntegral C₁ := by
    haveI : IsIntegral (pullback c₁ (Spec.map (CommRingCat.ofHom (algebraMap k k)))) :=
      SmoothProperCurve.isIntegral_pullback_Spec_field k c₁ (Spec.map (CommRingCat.ofHom (algebraMap k k)))
    have hid : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _ := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]; exact Spec.map_id _
    haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by rw [hid]; infer_instance
    exact IsIntegral.of_isIso (pullback.fst c₁ (Spec.map (CommRingCat.ofHom (algebraMap k k))))
  have hcl₂ : IsClosed (Set.range i₂.1.base) := i₂.1.isClosedEmbedding.isClosed_range
  have himg : wk.hom.base '' Set.range i₁.1.base ⊆ Set.range i₁.1.base :=
    FrobTwist.image_range_subset_of_fix i₁.1 _ hcl₂ hcover _ wk.hom.continuous P hPfix hP₁ hP₂
  have himg' : wk.inv.base '' Set.range i₁.1.base ⊆ Set.range i₁.1.base :=
    FrobTwist.image_range_subset_of_fix i₁.1 _ hcl₂ hcover _ wk.inv.continuous P hPfix' hP₁ hP₂
  have hrange_e : Set.range (e₁.hom ≫ i₁.1).base = Set.range i₁.1.base := by
    ext z
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨e₁.hom.base m, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨e₁.inv.base y, ?_⟩
      change (e₁.inv ≫ e₁.hom ≫ i₁.1).base y = _
      rw [e₁.inv_hom_id_assoc]
  let θ : Mdl₁.C ≅ Mdl₁.C := FrobTwist.liftAut (e₁.hom ≫ i₁.1) wk (by rw [hrange_e]; exact himg)
    (by rw [hrange_e]; exact himg')
  let Wt : Mdl₁.C ⟶ Mdl₁.C := θ.hom
  haveI hWtiso : IsIso Wt := inferInstance
  have hWt : Wt ≫ e₁.hom ≫ i₁.1 = (e₁.hom ≫ i₁.1) ≫ wk.hom :=
    FrobTwist.liftAut_hom_comp (e₁.hom ≫ i₁.1) wk _ _

  let g₂ : Mdl₁.C ⟶ ModularCurve.TwoChartModel A (↥K) j :=
    e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)
  have hWt_g₂ : Wt ≫ g₂ = g₂ ≫ ws.hom := by
    change Wt ≫ e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      (e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ≫ ws.hom
    rw [reassoc_of% hWt, hwk₁]
    simp only [Category.assoc]
  have htb : Mdl₁.toBase = e₁.hom ≫ i₁.1 ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) := by
    rw [← he₁]
    exact congrArg (e₁.hom ≫ ·) i₁.2.symm
  have hWt_base : Wt ≫ Mdl₁.toBase = Mdl₁.toBase := by
    rw [htb, reassoc_of% hWt, hwk₂]

  let Ig := ↥(ModularCurve.igusaFunctionFieldX1C k M w)
  have hff : (FrobPTTools.ffMap Wt).hom.comp Mdl₁.ffEquiv.toRingHom = Mdl₁.ffEquiv.toRingHom := by
    let V : (ModularCurve.TwoChartModel A (↥K) j).Opens := (ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤
    let U : Mdl₁.C.Opens := g₂ ⁻¹ᵁ V
    let sec : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) → Γ(ModularCurve.TwoChartModel A (↥K) j, V) := fun a =>
      ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)
    haveI : Nonempty ↥U := hne₁
    have hηU : genericPoint Mdl₁.C ∈ U :=
      ((genericPoint_spec Mdl₁.C).mem_open_set_iff U.2).mpr (by
        obtain ⟨⟨y, hy⟩⟩ := hne₁
        exact ⟨y, Set.mem_univ _, hy⟩)
    let rd : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) → Ig := fun a =>
      Mdl₁.ffEquiv.symm (Mdl₁.C.germToFunctionField U (g₂.app V (sec a)))
    have hrd : ∀ a, Mdl₁.ffEquiv (rd a) = Mdl₁.C.presheaf.germ U (genericPoint Mdl₁.C) hηU (g₂.app V (sec a)) := by
      intro a
      change Mdl₁.ffEquiv (Mdl₁.ffEquiv.symm _) = _
      rw [RingEquiv.apply_symm_apply]

    have hread : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
        y.map (algebraMap A k) ≠ 0 →
        ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
          HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        ((rd a : Ig) : LaurentSeries k) =
          HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)) :=
      fun a x y hy hxy => hgauss₁ a x y hy hxy

    have hcompS : (s : L →+* L).comp (algebraMap A L) = (algebraMap A L).comp (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s) := by
      ext a
      change s (algebraMap A L a) = algebraMap A L (s • a)
      exact (hΓA s a).symm
    have hsx : ∀ x : PowerSeries A, ModularCurve.coeffMap (s : L →+* L) (HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) =
        HahnSeries.ofPowerSeries ℤ L ((x.map (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)).map (algebraMap A L)) := by
      intro x
      rw [FrobPTTools.coeffMap_ofPowerSeries, ← RingHom.comp_apply (PowerSeries.map (s : L →+* L)) (PowerSeries.map _) x,
        ← PowerSeries.map_comp, ← RingHom.comp_apply (PowerSeries.map (algebraMap A L)) (PowerSeries.map _) x,
        ← PowerSeries.map_comp, hcompS]
    have hsk' : ∀ x : PowerSeries A, (x.map (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)).map (algebraMap A k) =
        x.map (algebraMap A k) := by
      intro x
      rw [← RingHom.comp_apply (PowerSeries.map (algebraMap A k)) (PowerSeries.map _) x, ← PowerSeries.map_comp, hsA]

    have hfix : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
        y.map (algebraMap A k) ≠ 0 →
        ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
          HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        rd (ρs a) = rd a := by
      intro a x y hy hxy
      have hxy' : (((ρs a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) *
          HahnSeries.ofPowerSeries ℤ L ((y.map (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)).map (algebraMap A L)) =
          HahnSeries.ofPowerSeries ℤ L ((x.map (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)).map (algebraMap A L)) := by
        rw [hρs, ← hsx, ← hsx, ← map_mul, hxy]
      have hy' : (y.map (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)).map (algebraMap A k) ≠ 0 := by rwa [hsk']
      apply Subtype.ext
      rw [hread (ρs a) _ _ hy' hxy', hread a x y hy hxy, hsk', hsk']

    let T : Set Ig := {z | ∃ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 ∧
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧ z = rd a}
    let S : Set Ig := Set.range (algebraMap k Ig) ∪ T
    have hyres : ∀ y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 → y.map (algebraMap A k) ≠ 0 := by
      intro y hy h0
      apply hy
      ext m
      have hm := congrArg (PowerSeries.coeff m) h0
      rw [PowerSeries.coeff_map, map_zero] at hm
      rw [PowerSeries.coeff_map, map_zero, IsLocalRing.residue_eq_zero_iff]
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (algebraMap A k)) (RingHom.mem_ker.2 hm)
    have hgen : Subfield.closure S = ⊤ := by
      let val : Ig →+* LaurentSeries k := (ModularCurve.igusaFunctionFieldX1C k M w).toSubfield.subtype
      have hval : ∀ z : Ig, val z = (z : LaurentSeries k) := fun _ => rfl
      have hle : (IntermediateField.adjoin k {r : LaurentSeries k |
          ∃ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
            y.map (IsLocalRing.residue A) ≠ 0 ∧
            (((b : ↥K) : LaurentSeries L)) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
              = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
            r = HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) /
                  HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k))}).toSubfield ≤ (Subfield.closure S).map val := by
        rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
        rintro r (⟨d, rfl⟩ | ⟨b, x, y, hy, hxy, rfl⟩)
        · exact ⟨algebraMap k Ig d, Subfield.subset_closure (Or.inl ⟨d, rfl⟩), rfl⟩
        · let a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) := ⟨(b : ↥K), b.2⟩
          have hy' : y.map (algebraMap A k) ≠ 0 := hyres y hy
          refine ⟨rd a, Subfield.subset_closure (Or.inr ⟨a, x, y, hy', hxy, rfl⟩), ?_⟩
          rw [hval, hread a x y hy' hxy]
      rw [eq_top_iff]
      intro z _
      obtain ⟨hz, -⟩ := ModularCurve.XOneP.coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul
        p M hM hpM L ζ hζ K hK A hAp hζA j hj k w
      obtain ⟨z', hz'S, hzz⟩ := hle (hz z)
      have : z' = z := Subtype.ext hzz
      exact this ▸ hz'S

    have hconst : ∀ d : k, FrobPTTools.ffMap Wt (Mdl₁.ffEquiv (algebraMap k Ig d)) = Mdl₁.ffEquiv (algebraMap k Ig d) := by
      intro d
      rw [Mdl₁.ffEquiv_algebraMap]
      exact FrobPTTools.ffMap_germ_of_eq Wt Mdl₁.toBase Mdl₁.toBase hWt_base.symm ⊤
        (show genericPoint Mdl₁.C ∈ Mdl₁.toBase ⁻¹ᵁ ⊤ from trivial)
        (show genericPoint Mdl₁.C ∈ Mdl₁.toBase ⁻¹ᵁ ⊤ from trivial)
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv d)

    have hpull : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        FrobPTTools.ffMap Wt (Mdl₁.ffEquiv (rd a)) = Mdl₁.ffEquiv (rd (ρs a)) := by
      intro b
      rw [hrd, hrd]
      have hle : V ≤ ws.hom ⁻¹ᵁ V := by
        rintro v ⟨z, -, rfl⟩
        refine ⟨(Spec.map (CommRingCat.ofHom ρs.toRingHom)).base z, trivial, ?_⟩
        have := congrArg (fun f => f.base z) hwρ
        simpa using this.symm
      have key := FrobPTTools.ffMap_germ_of_eq Wt g₂ (g₂ ≫ ws.hom) hWt_g₂.symm V hηU
        (show genericPoint Mdl₁.C ∈ (g₂ ≫ ws.hom) ⁻¹ᵁ V from hle hηU) (sec b)
      rw [key]
      have hres : (ModularCurve.TwoChartModel A (↥K) j).presheaf.map (homOfLE hle).op (ws.hom.app V (sec b)) = sec (ρs b) := by
        apply ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).commRingCatIsoToRingEquiv.injective
        change ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).hom _ = ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).hom _
        rw [GalPlacesTools.appIso_hom_res_app_appIso_inv_apply ws.hom (ModularCurve.TwoChart.ιFin A (↥K) j)
          (ModularCurve.TwoChart.ιFin A (↥K) j) (CommRingCat.ofHom ρs.toRingHom) hwρ b ⊤ hle]
        change _ = (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ≫ ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).hom) _
        rw [Iso.inv_hom_id]
        simp
      rw [Scheme.Hom.comp_app]
      change Mdl₁.C.presheaf.germ ((g₂ ≫ ws.hom) ⁻¹ᵁ V) (genericPoint Mdl₁.C) _ (g₂.app (ws.hom ⁻¹ᵁ V) (ws.hom.app V (sec b))) = _
      have hnat := CategoryTheory.ConcreteCategory.congr_hom (g₂.naturality (homOfLE hle).op) (ws.hom.app V (sec b))
      rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, hres] at hnat
      rw [hnat]
      exact (TopCat.Presheaf.germ_res_apply Mdl₁.C.presheaf _ (genericPoint Mdl₁.C) hηU _).symm
    have hchart : ∀ z ∈ T, FrobPTTools.ffMap Wt (Mdl₁.ffEquiv z) = Mdl₁.ffEquiv z := by
      rintro z ⟨a, x, y, hy, hxy, rfl⟩
      rw [hpull a, hfix a x y hy hxy]
    have h1 : (FrobPTTools.ffMap Wt).hom.comp Mdl₁.ffEquiv.toRingHom = (RingHom.id _).comp Mdl₁.ffEquiv.toRingHom := by
      apply RingHom.eq_of_eqOn_of_field_closure_eq_top hgen
      rintro z (⟨d, rfl⟩ | hz)
      · exact hconst d
      · exact hchart z hz
    rw [h1, RingHom.id_comp]
  have hffMap : FrobPTTools.ffMap Wt = CommRingCat.ofHom
      (Mdl₁.ffEquiv.toRingHom.comp ((SemilinearAut.toRingAut (1 : SemilinearAut k Ig)).symm.toRingHom.comp
        Mdl₁.ffEquiv.symm.toRingHom)) := by
    ext v
    have := RingHom.congr_fun hff (Mdl₁.ffEquiv.symm v)
    simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Function.comp_apply,
      RingEquiv.apply_symm_apply] at this
    show (FrobPTTools.ffMap Wt).hom v =
      Mdl₁.ffEquiv ((SemilinearAut.toRingAut (1 : SemilinearAut k Ig)).symm (Mdl₁.ffEquiv.symm v))
    rw [this, SemilinearAut.toRingAut_one]
    change v = Mdl₁.ffEquiv (Mdl₁.ffEquiv.symm v)
    rw [RingEquiv.apply_symm_apply]
  have hθgen : Mdl₁.C.fromSpecStalk (genericPoint Mdl₁.C) ≫ Wt =
      Spec.map (CommRingCat.ofHom (Mdl₁.ffEquiv.toRingHom.comp
        ((SemilinearAut.toRingAut (1 : SemilinearAut k Ig)).symm.toRingHom.comp Mdl₁.ffEquiv.symm.toRingHom))) ≫
        Mdl₁.C.fromSpecStalk (genericPoint Mdl₁.C) := by
    rw [← FrobPTTools.SpecMap_ffMap_fromSpecStalk Wt, hffMap]

  have hpt : ∀ q : Spec (CommRingCat.of k) ⟶ Mdl₁.C, q ≫ Mdl₁.toBase = 𝟙 _ → q ≫ Wt = q := by
    intro q hq
    let x : {q : Spec (CommRingCat.of k) ⟶ Mdl₁.C // q ≫ Mdl₁.toBase = 𝟙 _} := ⟨q, hq⟩
    let x' : {q : Spec (CommRingCat.of k) ⟶ Mdl₁.C // q ≫ Mdl₁.toBase = 𝟙 _} :=
      ⟨q ≫ Wt, by rw [Category.assoc, hWt_base, hq]⟩
    have hxx' : x'.1.base (IsLocalRing.closedPoint k) = Wt.base (x.1.base (IsLocalRing.closedPoint k)) := rfl
    have key := AlgebraicCurve.CurveModel.pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq
      Mdl₁ (1 : SemilinearAut k Ig) Wt hθgen x x' hxx'
    rw [one_smul] at key
    exact congrArg Subtype.val (Mdl₁.pointEquivPlace.injective key)
  have hWt1 : Wt = 𝟙 _ := by
    refine AlgebraicGeometry.ext_of_forall_comp_eq_of_isAlgClosed Mdl₁.toBase Mdl₁.toBase hWt_base (Category.id_comp _) ?_
    intro q hq
    rw [hpt q hq, Category.comp_id]

  have hfin : e₁.hom ≫ i₁.1 = e₁.hom ≫ i₁.1 ≫ wk.hom := by
    have h := hWt
    rw [hWt1, Category.id_comp, Category.assoc] at h
    exact h
  exact ((cancel_epi e₁.hom).mp hfin).symm

end S_ModularCurve_XOneP_comp_fibreAut_eq_of_galoisModelAut_of_gaussPin_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_comp_fibreAut_eq_of_galoisModelAut_of_gaussPin_twoChartModel_x1_mul (solution)
