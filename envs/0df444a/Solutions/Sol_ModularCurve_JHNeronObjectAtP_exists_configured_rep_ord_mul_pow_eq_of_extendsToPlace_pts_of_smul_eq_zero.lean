-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_configured_rep_ord_mul_pow_eq_of_extendsToPlace_pts_of_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/8cf3ee06-7742-576a-9a54-4cf9b3cb6461

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Theorems.Thm_ModularCurve_XHDRModelAtP_ord_placeOfPoint_eq_sum_ite_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
import Theorems.Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Theorems.Thm_ModularCurve_XHDRModelAtP_ord_placeOfPoint_eq_zero_of_isUnit_of_ffEquiv_symm_germToFunctionField_eq
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_ord_mul_pow_eq_of_extendsToPlace_pts_of_smul_eq_zero
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false
open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

namespace MoveReadAux

open ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

theorem placeOfPoint_ne_placeOn_of_smooth
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (i : Fin 2)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (husm : Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) :
    (𝔛.Mfib A hA ρ hρ).placeOfPoint P ≠ (if i = 0 then 𝔛.placeOn0 A hA ρ hρ n else 𝔛.placeOn1 A hA ρ hρ n) := by

  have hsm : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) ⁻¹ᵁ 𝔛.smoothLocus) := by
    show (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
      (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))
    rw [← Scheme.Hom.comp_apply, huκ₁, Scheme.Hom.comp_apply]
    exact husm ⟨_, rfl⟩
  have hnot := (ModularCurve.XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter p M H hpM hpM2 hj 𝔛 A hA ρ hρ _).1 hsm
  rw [← hP] at hnot
  obtain ⟨⟨hb, hbpl⟩, ⟨ha, hapl⟩⟩ := 𝔛.node_pin A hA ρ hρ n
  have hinvE : ∀ z, (𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hcond : (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) =
      (𝔛.comp A hA ρ hρ 1).base ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) := by
    have := congrArg (fun f => f.base n) (pullback.condition (f := 𝔛.comp A hA ρ hρ 0) (g := 𝔛.comp A hA ρ hρ 1))
    simpa only [Scheme.Hom.comp_apply] using this
  intro heq
  apply hnot
  fin_cases i
  ·
    simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte] at heq ⊢
    have hPeq : P = ⟨_, ha⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.1 (heq.trans hapl.symm)
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [hPeq, Scheme.Hom.comp_apply]
    show (𝔛.comp A hA ρ hρ 0).base ((𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base _)) ∈ _
    rw [hinvE, hcond]
    exact ⟨_, rfl⟩
  ·
    simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at heq ⊢
    have hPeq : P = ⟨_, hb⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.1 (heq.trans hbpl.symm)
    refine ⟨?_, ⟨_, rfl⟩⟩
    rw [hPeq, Scheme.Hom.comp_apply]
    show (𝔛.comp A hA ρ hρ 1).base ((𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base _)) ∈ _
    rw [hinvE, ← hcond]
    exact ⟨_, rfl⟩

theorem pairsum_sum_eq_sum_filter_add {G : Type*} [AddCommMonoid G] {k : ℕ} (c : Fin k → Fin 2) (f : Fin k → G) :
    ∑ i, f i = ∑ i ∈ Finset.univ.filter (fun i => c i = 0), f i + ∑ i ∈ Finset.univ.filter (fun i => c i = 1), f i := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => c i = 0)]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
  constructor
  · intro h
    have h' : (c i).val ≠ 0 := fun h' => h (Fin.ext h')
    exact Fin.ext (by have := (c i).isLt; simp only [Fin.val_one]; omega)
  · intro h h0
    rw [h] at h0
    exact absurd h0 (by decide)

end MoveReadAux

set_option maxHeartbeats 3200000 in
open Classical in
open ModularCurve in
theorem solution
    (p : ℕ)
    [Fact p.Prime]
    (M : ℕ)
    [NeZero M]
    (hpM : p ∣ M)
    (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))
    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (z : ModularCurve.JH M H)
    (hz : ExtendsToPlace Pl Λ.σA (O.pts z))
    (hpz : p • z = 0)
    (D' : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (hD' : AlgebraicCurve.Pic0.mk D' = z)
    (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (hdiv : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      (p : ℤ) * (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v = v.ord f)
    (y : LaurentSeries ↥Pl)
    (hfy : (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y)
    (hy : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0)
    (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
    (hg : (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y) :
    ∃ (h : ↥(ModularCurve.xHFunctionFieldBar M H)) (xh yh : LaurentSeries ↥Pl) (hbar : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
        (k : ℕ) (c : Fin k → Fin 2)
        (yv : Fin k → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : Fin k → NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (uκ : Fin k → (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ)))
        (P : Fin k → closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
        (n : Fin k → ℤ)
        (Dv : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))),

        h ≠ 0 ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xh ≠ 0 ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) yh ≠ 0 ∧
        (h : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype yh = ModularCurve.coeffMap Pl.subtype xh ∧
        (hbar : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) yh =
          ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xh ∧

        (∀ i, ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ (u i).1 = (yv i).1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ∧
        (∀ i, Set.range (u i).1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) ∧
        (∀ i, uκ i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ (u i).1) ∧
        (∀ i, uκ i ≫ pullback.snd _ _ = 𝟙 _) ∧
        (∀ i, (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ (c i)).base (P i).1 = (uκ i).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥Pl))) ∧
        (∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i = 0) ∧
        (∑ i ∈ Finset.univ.filter (fun i => c i = 1), n i = 0) ∧
        ((Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) =
          ∑ i, n i • Finsupp.single (𝔛.Meta.pointEquivPlace (yv i)) 1) ∧

        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v =
            (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v + v.ord h) ∧

        ∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
          v.ord (g * hbar ^ p) =
            (p : ℤ) * (∑ i ∈ Finset.univ.filter (fun i => c i = 0),
              n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) 1) v := by

  let bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) :=
    XHDRLevel.bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥Pl) rfl
  have hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _ := XHDRLevel.bcMap_fst (ΓM M H) hj ρ (IsLocalRing.residue ↥Pl) rfl
  have hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) :=
    XHDRLevel.bcMap_snd (ΓM M H) hj ρ (IsLocalRing.residue ↥Pl) rfl
  have plumb_gA : ∃ gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))),
      gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _ ∧ gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl := by
    have hsp : Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) =
        barPt Pl ≫ Spec.map (CommRingCat.ofHom ρ) := by
      dsimp only [barPt]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
    have hw : (𝔛.eeta ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj = (𝔛.Meta.toBase ≫ barPt Pl) ≫ Spec.map (CommRingCat.ofHom ρ) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, 𝔛.heeta, Category.assoc, hsp]
    exact ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨gA, hgA₁, hgA₂⟩ := plumb_gA

  obtain ⟨h, xh, yh, hbar, k, c, yv, u, uκ, P, n, Dv, hh0, hxh, hyh, hhw, hhbar, hu, husm, huκ₁, huκ₂, hP, hDv, hDvD, hunitF⟩ :=
    ModularCurve.JHNeronObjectAtP.exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero p M hpM hpM2 H hHp Pl hPl hj 𝔛 Λ O hD hDQ hsep ajQ kQ ajbar εbar hpoinc hajQε hajQ hkQ₁ hkQ₂ hajbar hajbar_over
      hεbar hεbar_aj hpts_law hAJ ρ hρ hσA gA hgA₁ hgA₂ bc hbc₁ hbc₂ z hz hpz D' hD' f hf hdiv y hfy hy

  have hxF : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) (y * xh ^ p) ≠ 0 := by
    rw [map_mul, map_pow]
    exact mul_ne_zero hy (pow_ne_zero _ hxh)
  have hyF : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) (yh ^ p) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hyh
  have hFw : ((f * h ^ p : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype (yh ^ p) =
      ModularCurve.coeffMap Pl.subtype (y * xh ^ p) := by
    have hc : ((f * h ^ p : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (f : LaurentSeries (AlgebraicClosure ℚ)) * (h : LaurentSeries (AlgebraicClosure ℚ)) ^ p := by
      push_cast
      rfl
    rw [hc, map_mul, map_pow, map_pow, hfy, mul_assoc, ← mul_pow, hhw]
  have hgFw : ((g * hbar ^ p : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) *
      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) (yh ^ p) = ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) (y * xh ^ p) := by
    have hc : ((g * hbar ^ p : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
        (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * (hbar : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) ^ p := by
      push_cast
      rfl
    rw [hc, map_mul, map_pow, map_pow, hg, mul_assoc, ← mul_pow, hhbar]

  have plumb_divF : ∀ w : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      w.ord (f * h ^ p) = (∑ j, Finsupp.single (𝔛.Meta.pointEquivPlace (yv j)) ((p : ℤ) * n j)) w := by
    intro w
    rw [AlgebraicCurve.Place.ord_mul _ hf (pow_ne_zero _ hh0), ← zpow_natCast, AlgebraicCurve.Place.ord_zpow, ← hdiv w]
    have hDvw := hDvD w
    rw [hDv] at hDvw
    rw [Finsupp.finsetSum_apply] at hDvw ⊢
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] at hDvw ⊢
    rw [← mul_add, ← hDvw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring

  have hident : ∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
      v.ord (g * hbar ^ p) =
        (p : ℤ) * (∑ i ∈ Finset.univ.filter (fun i => c i = 0),
          n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) 1) v := by
    intro v

    obtain ⟨Pbar, rfl⟩ := (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint_bijective.2 v
    by_cases hss : (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∈
        ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p
    ·
      have h0 := ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_zero_of_isUnit_of_ffEquiv_symm_germToFunctionField_eq p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ (f * h ^ p) (y * xh ^ p) (yh ^ p) hxF hyF hFw
        (g * hbar ^ p) hgFw gA hgA₁ hgA₂ bc hbc₁ hbc₂ Pbar (hunitF Pbar hss)
      have plumb_rhs_zero_of_ss :
          (p : ℤ) * (∑ i ∈ Finset.univ.filter (fun i => c i = 0),
            n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) 1) ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar) = 0 := by

        haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos).ne'⟩

        obtain ⟨y₀, hy₀, hfr⟩ : ∃ y₀ ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p,
            qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p y₀ = (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar := by
          rw [← ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq (IsLocalRing.ResidueField ↥Pl) p (ΓN p M H hpM)] at hss
          exact hss
        have hne : ∀ i, c i = 0 → (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i) ≠ (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar := by
          intro i hc
          have hoff := MoveReadAux.placeOfPoint_ne_placeOn_of_smooth p M H hpM hpM2 hj 𝔛 Pl hPl ρ hρ (c i) (u i) (husm i) (uκ i) (huκ₁ i)
            (P i) (hP i) ((𝔛.nodeEquiv Pl hPl ρ hρ).symm ⟨y₀, hy₀⟩)
          rw [hc] at hoff
          simpa only [Fin.isValue, ↓reduceIte, XHDRModelAtP.placeOn0, Equiv.apply_symm_apply, hfr] using hoff
        rw [Finsupp.finsetSum_apply]
        simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        rw [Finset.sum_eq_zero, mul_zero]
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [if_neg (hne i hi.2), mul_zero]
      rw [h0, plumb_rhs_zero_of_ss]
    ·
      have h1 := ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_sum_ite_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap
        p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ (f * h ^ p) (y * xh ^ p) (yh ^ p) hxF hyF hFw (g * hbar ^ p) hgFw
        yv u hu uκ huκ₁ huκ₂ (fun j => (p : ℤ) * n j) plumb_divF Pbar hss
      have plumb_dict :
          (∑ j, if (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1 =
                (uκ j).base (IsLocalRing.closedPoint (ResidueField ↥Pl))
             then (fun j => (p : ℤ) * n j) j else 0) =
          (p : ℤ) * (∑ i ∈ Finset.univ.filter (fun i => c i = 0),
            n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) 1) ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar) := by

        have hinjE : Function.Injective (𝔛.efib Pl hPl ρ hρ).base := fun a b hab => by
          have h := congrArg (fun t => (inv (𝔛.efib Pl hPl ρ hρ)).base t) hab
          simp only [← Scheme.Hom.comp_apply, IsIso.hom_inv_id] at h
          simpa using h
        have hinj0 : Function.Injective (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base := by
          intro a b hab
          rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hab
          haveI := 𝔛.comp_isClosedImmersion Pl hPl ρ hρ 0
          exact hinjE ((𝔛.comp Pl hPl ρ hρ 0).isClosedEmbedding.injective hab)
        have hiff : ∀ j, ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1 =
              (uκ j).base (IsLocalRing.closedPoint (ResidueField ↥Pl))) ↔ (c j = 0 ∧ P j = Pbar) := by
          intro j
          constructor
          · intro hj0
            obtain ⟨cj, hcj⟩ : ∃ cj, c j = cj := ⟨_, rfl⟩
            fin_cases cj
            · refine ⟨hcj, ?_⟩
              have hPj := hP j
              rw [hcj] at hPj
              exact Subtype.ext (hinj0 (hPj.trans hj0.symm))
            · exfalso

              have hsm : (uκ j).base (IsLocalRing.closedPoint (ResidueField ↥Pl)) ∈
                  (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ))) ⁻¹ᵁ 𝔛.smoothLocus) := by
                show (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ)))).base
                  ((uκ j).base (IsLocalRing.closedPoint (ResidueField ↥Pl))) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))
                rw [← Scheme.Hom.comp_apply, huκ₁ j, Scheme.Hom.comp_apply]
                exact husm j ⟨_, rfl⟩
              have hnot := (ModularCurve.XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter p M H hpM hpM2 hj 𝔛 Pl hPl ρ hρ _).1 hsm
              apply hnot
              have hPj := hP j
              rw [hcj] at hPj
              refine ⟨⟨(𝔛.efib Pl hPl ρ hρ).base Pbar.1, ?_⟩, ⟨(𝔛.efib Pl hPl ρ hρ).base (P j).1, ?_⟩⟩
              · rw [← Scheme.Hom.comp_apply, hj0]
              · rw [← Scheme.Hom.comp_apply]
                exact hPj
          · rintro ⟨hcj, rfl⟩
            have hPj := hP j
            rw [hcj] at hPj
            exact hPj
        have hplinj : ∀ j, (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P j) = (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ↔ P j = Pbar :=
          fun j => (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint_bijective.1.eq_iff
        rw [Finsupp.finsetSum_apply]
        simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hiff j, hplinj j]
        by_cases hcj : c j = 0 <;> by_cases hPj : P j = Pbar <;> simp [hcj, hPj]
      rw [h1, plumb_dict]

  haveI hCO : AlgebraicCurve.IsCurveOver (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      (𝔛.Mfib Pl hPl ρ hρ).toBase (𝔛.Mfib Pl hPl ρ hρ).ffEquiv (𝔛.Mfib Pl hPl ρ hρ).ffEquiv_algebraMap
  have hdegF : ∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)), v.deg = 1 := fun v => by
    haveI := AlgebraicCurve.IsCurveOver.finiteResidue (K := IsLocalRing.ResidueField ↥Pl) (F := ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) v
    exact (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField v).mpr
      IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  haveI hCOgen : AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      𝔛.Meta.toBase 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap
  have hdeg1 : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H), v.deg = 1 := fun v => by
    haveI := AlgebraicCurve.IsCurveOver.finiteResidue (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)) v
    exact (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField v).mpr
      IsAlgClosed.algebraMap_bijective_of_isIntegral.2

  have hgF0 : g * hbar ^ p ≠ 0 := by
    intro h0
    apply hxF
    rw [← hgFw, h0]
    push_cast
    rw [zero_mul]
  have hn₀ : ∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i = 0 := by
    obtain ⟨Dg, hDg, hdegDg⟩ :=
      (ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar p M H hpM hpM2
        (IsLocalRing.ResidueField ↥Pl)).1.exists_divisor (g * hbar ^ p) hgF0
    have hDgE : Dg = (p : ℤ) • ∑ i ∈ Finset.univ.filter (fun i => c i = 0),
        n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) 1 := by
      ext v
      rw [hDg v, hident v, Finsupp.smul_apply, smul_eq_mul]
    rw [hDgE, map_zsmul, map_sum] at hdegDg
    simp only [map_zsmul, AlgebraicCurve.Divisor.degree_single, hdegF, Nat.cast_one, mul_one, smul_eq_mul] at hdegDg
    have h' : p = 0 ∨ ∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i = 0 := by simpa using hdegDg
    exact h'.resolve_left (Fact.out : p.Prime).ne_zero
  have hn₁ : ∑ i ∈ Finset.univ.filter (fun i => c i = 1), n i = 0 := by
    have hdeg0 : AlgebraicCurve.Divisor.degree (Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) = 0 :=
      AlgebraicCurve.Divisor.mem_degZero.mp Dv.2
    rw [hDv, map_sum] at hdeg0
    simp only [map_zsmul, AlgebraicCurve.Divisor.degree_single, hdeg1, Nat.cast_one, mul_one, smul_eq_mul] at hdeg0
    rw [MoveReadAux.pairsum_sum_eq_sum_filter_add c, hn₀, zero_add] at hdeg0
    exact hdeg0
  exact ⟨h, xh, yh, hbar, k, c, yv, u, uκ, P, n, Dv, hh0, hxh, hyh, hhw, hhbar, hu, husm, huκ₁, huκ₂, hP, hn₀, hn₁, hDv, hDvD, hident⟩

end S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_ord_mul_pow_eq_of_extendsToPlace_pts_of_smul_eq_zero
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_ord_mul_pow_eq_of_extendsToPlace_pts_of_smul_eq_zero (solution)
