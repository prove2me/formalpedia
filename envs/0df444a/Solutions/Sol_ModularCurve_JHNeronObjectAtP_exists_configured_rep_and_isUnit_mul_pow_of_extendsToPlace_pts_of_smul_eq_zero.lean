-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e0926bdb-2c0c-5004-b359-d872be3241ad

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
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Theorems.Thm_ModularCurve_XHDRModelAtP_crossingPt_mem_preimage_iotaFin
import Theorems.Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_schemeHomOver_barPt_comp_eq_pts_and_iterate_mul_eq_one_of_extendsToPlace_of_nsmul_eq_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation
import Theorems.Thm_ModularCurve_nonempty_ssPlacesQExp
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_eq_mul_of_presentations
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_schemeHomOver_barPt_comp_eq_of_isProper
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
import Theorems.Thm_ModularCurve_XHDRModelAtP_not_mem_range_comp_one_and_mem_smoothLocus_of_placeOfPoint_not_mem_ssPlacesQExp
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_ModularCurve_XHDRModelAtP_isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
import Theorems.Thm_ModularCurve_finite_ssPlacesQExp
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
import Theorems.Thm_ModularCurve_exists_qExpFunctionFieldC_infSubgroup_coe_eq_of_charP
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_exists_isFrameOn_isUnit_germToFunctionField_eq_mul_pow_of_tensorPow_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_of_finite_subset_affineOpen
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false
open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero.AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero.AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard P2MW.S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero.AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

universe u

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.germToFunctionField isAffineOpen_opensRange Scheme.Hom Spec IsIntegral Scheme.Opens.toScheme Spec.map Scheme IsOpenImmersion Scheme.Hom.comp_base pointEquivClosedPoint IsClosedImmersion.spec_of_surjective IsClosedImmersion IsSeparated IsAffineOpen Scheme.Modules Scheme.Opens IsAffineHom Scheme.Hom.comp_apply isClosedImmersion_of_comp_eq_id Scheme.Modules.IsInvertible RelPicard.RepresentsRelSubPic RelEffCartierDiv RelEffCartierDiv.ofPoint RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso Scheme.Modules.IsInvertible.exists_functionField_presentation Scheme.Modules.IsInvertible.exists_isFrameOn Scheme.Modules.tensorPow_succ Scheme.Modules.IsFrameOn Scheme.Modules.IsInvertible.exists_forall_exists_isFrameOn_isUnit_germToFunctionField_eq_mul_pow_of_tensorPow_iso Scheme.Modules.IsInvertible.exists_isFrameOn_of_finite_subset_affineOpen" namespace RelPicard p2m_export "AlgebraicGeometry.RelPicard" "RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic algEquivZeroCut algEquivZeroGroupCut SubPicGroupCondition RepresentsRelSubPic.relativeGroupLaw BaseChange.ofR RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso" namespace RepresentsRelSubPic p2m_export "AlgebraicGeometry.RelPicard.RepresentsRelSubPic" "poincare zero mk grpObj relativeGroupLaw homEquiv_mul relativeGroupLaw_one nonempty_poincare_pullbackAlong_mul_iso nonempty_poincare_pullbackAlong_one_iso" end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.RelPicard.RepresentsRelSubPic" in
open scoped CategoryTheory.MonObj in
theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_iterate_tensor_pullbackAlong_unit_iso_unit_of_iterate_mul_one_eq_one
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (σ : SchemeHomOver t D.toBase) (n : ℕ)
    (hσ : (fun τ : SchemeHomOver t D.toBase => h.relativeGroupLaw.mul t τ σ)^[n] (h.relativeGroupLaw.one t) =
      h.relativeGroupLaw.one t) :
    Nonempty ((((fun N : RigidifiedLineBundle c ε t => N.tensor (h.poincare.pullbackAlong σ))^[n])
        (RigidifiedLineBundle.unit (c := c) (ε := ε) t)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L) := by
  letI := h.grpObj
  have key : ∀ m : ℕ,
      Nonempty ((h.poincare.pullbackAlong
          ((fun τ : SchemeHomOver t D.toBase => h.relativeGroupLaw.mul t τ σ)^[m] (h.relativeGroupLaw.one t))).L ≅
        (((fun N : RigidifiedLineBundle c ε t => N.tensor (h.poincare.pullbackAlong σ))^[m])
          (RigidifiedLineBundle.unit (c := c) (ε := ε) t)).L) := by
    intro m
    induction m with
    | zero =>
      exact AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso h (Over.mk t)
    | succ m ih =>
      obtain ⟨e⟩ := ih
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      obtain ⟨em⟩ := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso h
        (T := Over.mk t)
        (schemeHomOverToOverHom ((fun τ : SchemeHomOver t D.toBase => h.relativeGroupLaw.mul t τ σ)^[m] (h.relativeGroupLaw.one t)))
        (schemeHomOverToOverHom σ)
      exact ⟨em ≪≫ whiskerRightIso e _⟩
  obtain ⟨e⟩ := key n
  rw [hσ] at e
  obtain ⟨e1⟩ := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso h (Over.mk t)
  exact ⟨e.symm ≪≫ e1⟩

namespace ModularCurve p2m_export "ModularCurve" "ssPlacesQExp translation_mem_GammaH Gamma1_le_GammaH xHFunctionFieldBar JH qExpFunctionFieldC qExpFunctionFieldC_mono coeffMap coeffMap_coeff coeffEmb coeffEmb_mem_laurentBaseChange qExpFrobeniusPlaceModL jqModC map_jqModC JHNeronObjectAtP.Fbar JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP.barPt JZeroNeronObjectAtP XHDRLevel.R XHDRModelAtP XHDRModelAtP.crossingPt XHDRModelAtP.crossingPt_mem_preimage_iotaFin image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq JHNeronObjectAtP.exists_schemeHomOver_barPt_comp_eq_pts_and_iterate_mul_eq_one_of_extendsToPlace_of_nsmul_eq_zero nonempty_ssPlacesQExp JZeroNeronObjectAtP.exists_schemeHomOver_barPt_comp_eq_of_isProper XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter XHDRModelAtP.not_mem_range_comp_one_and_mem_smoothLocus_of_placeOfPoint_not_mem_ssPlacesQExp transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC XHDRModelAtP.isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion finite_ssPlacesQExp exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq exists_qExpFunctionFieldC_infSubgroup_coe_eq_of_charP XHDRModelAtP.exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens JHNeronObjectAtP.exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts" namespace XHDRModelAtP p2m_export "ModularCurve.XHDRModelAtP" "eeta comp_jointly_surjective w smoothLocus Meta efib node_pin nodeEquiv comp_isClosedImmersion heeta Mfib isProper mk εinf comp crossingPt crossingPt_mem_preimage_iotaFin mem_preimage_smoothLocus_iff_not_mem_range_comp_inter not_mem_range_comp_one_and_mem_smoothLocus_of_placeOfPoint_not_mem_ssPlacesQExp isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens" end ModularCurve.XHDRModelAtP
p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
open _root_.ModularCurve in
theorem ModularCurve.XHDRModelAtP.exists_isAffineOpen_forall_mem_of_placeOfPoint_mem_ssPlacesQExp
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))) :
    ∃ Uaff : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, IsAffineOpen Uaff ∧
      ∀ Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
        (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p →
        bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1) ∈ Uaff := by
  haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos).ne'⟩
  refine ⟨(pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ (ιFin p (ΓM M H) hj).opensRange, ?_, ?_⟩
  · haveI hg : IsAffineHom (Spec.map (CommRingCat.ofHom ρ) : Spec (CommRingCat.of ↥Pl) ⟶ Spec (CommRingCat.of (R p))) := inferInstance
    haveI : IsAffineHom (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) :=
      MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ hg
    exact (isAffineOpen_opensRange (ιFin p (ΓM M H) hj)).preimage _
  · intro Pbar hss
    have hbc : bc = bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥Pl) rfl :=
      pullback.hom_ext (hbc₁.trans (bcMap_fst (ΓM M H) hj ρ (IsLocalRing.residue ↥Pl) rfl).symm)
        (hbc₂.trans (bcMap_snd (ΓM M H) hj ρ (IsLocalRing.residue ↥Pl) rfl).symm)

    obtain ⟨y₀, hy₀, hfr⟩ : ∃ y₀ ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p,
        qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p y₀ = (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar := by
      rw [← ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq (IsLocalRing.ResidueField ↥Pl) p (ΓN p M H hpM)] at hss
      exact hss
    obtain ⟨-, ⟨ha, hapl⟩⟩ := 𝔛.node_pin Pl hPl ρ hρ ((𝔛.nodeEquiv Pl hPl ρ hρ).symm ⟨y₀, hy₀⟩)
    rw [Equiv.apply_symm_apply] at hapl
    have hPeq : Pbar = ⟨_, ha⟩ := (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint_bijective.1 (hfr.symm.trans hapl.symm)
    have hinvE : ∀ z, (𝔛.efib Pl hPl ρ hρ).base ((inv (𝔛.efib Pl hPl ρ hρ)).base z) = z := fun z => by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
    have key : bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1) =
        𝔛.crossingPt Pl hPl ρ hρ ρ (IsLocalRing.residue ↥Pl) rfl ((𝔛.nodeEquiv Pl hPl ρ hρ).symm ⟨y₀, hy₀⟩) := by
      rw [hPeq, hbc]
      simp only [XHDRModelAtP.crossingPt, Scheme.Hom.comp_apply, hinvE]
    show (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base
        (bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1)) ∈ Set.range (ιFin p (ΓM M H) hj).base
    rw [key]
    exact ModularCurve.XHDRModelAtP.crossingPt_mem_preimage_iotaFin p M H hpM hpM2 hHp hj 𝔛 Pl hPl ρ hρ ↥Pl ρ
      (IsLocalRing.residue ↥Pl) rfl _

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place Place.ord_mul Place.ord_inv Place.ord_zpow Divisor Divisor.degZero Divisor.mem_degZero HasPrincipalDivisors Pic0 Pic0.mk HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.hasPrincipalDivisors CurveModel CurveModel.pointEquivPlace_apply H1 Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed RegularProlongation RegularProlongation.residue_ne_zero_of_isUnit CurveModel.ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one" namespace Divisor p2m_export "AlgebraicCurve.Divisor" "degree degZero mem_degZero pullbackAlong pullback" end AlgebraicCurve.Divisor
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Divisor" in

theorem AlgebraicCurve.Divisor.apply_eq_zero_of_ord_eq_neg {K F : Type*} [Field K] [Field F] [Algebra K F]
    (Dv D' Dφ : AlgebraicCurve.Divisor K F) (r : K) (hr : r ≠ 0) (g₁ t : F) (hg₁ : g₁ ≠ 0) (ht : t ≠ 0)
    (hDvD : ∀ w : AlgebraicCurve.Place K F, Dv w = D' w + w.ord (algebraMap K F r * g₁ * t))
    (hDφ : ∀ w : AlgebraicCurve.Place K F, Dφ w = D' w + w.ord g₁)
    (v : AlgebraicCurve.Place K F) (hord : v.ord t = -Dφ v) : Dv v = 0 := by
  have hr' : algebraMap K F r ≠ 0 := (map_ne_zero _).mpr hr
  rw [hDvD v, v.ord_mul (mul_ne_zero hr' hg₁) ht, v.ord_mul hr' hg₁, v.ord_algebraMap r, hord, hDφ v]
  ring

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero.ModularCurve in

theorem ModularCurve.XHDRModelAtP.exists_configured_family_of_support_avoids
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))
    (V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (hTV : ∀ Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
      (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p →
      bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1) ∈ V)
    (Dv : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (hV : ∀ q : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _},
      gA.base (q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ∈ V →
      (Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) (𝔛.Meta.pointEquivPlace q) = 0) :
    ∃ (k : ℕ) (c : Fin k → Fin 2)
      (yv : Fin k → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : Fin k → NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (uκ : Fin k → (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ)))
      (P : Fin k → closedPoints (𝔛.Mfib Pl hPl ρ hρ).C) (n : Fin k → ℤ),
      (∀ i, ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ (u i).1 = (yv i).1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ∧
      (∀ i, Set.range (u i).1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) ∧
      (∀ i, uκ i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ (u i).1) ∧
      (∀ i, uκ i ≫ pullback.snd _ _ = 𝟙 _) ∧
      (∀ i, (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ (c i)).base (P i).1 = (uκ i).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥Pl))) ∧
      ((Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) = ∑ i, n i • Finsupp.single (𝔛.Meta.pointEquivPlace (yv i)) 1) := by
  classical

  let D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) := Dv
  let S := D.support
  let k : ℕ := Fintype.card ↥S
  let σ : Fin k ≃ ↥S := (Fintype.equivFin ↥S).symm
  let v : Fin k → AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) := fun i => (σ i).1
  have hvS : ∀ i, v i ∈ S := fun i => (σ i).2
  let yv : Fin k → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} :=
    fun i => 𝔛.Meta.pointEquivPlace.symm (v i)
  let n : Fin k → ℤ := fun i => D (v i)
  have hDv : D = ∑ i, n i • Finsupp.single (𝔛.Meta.pointEquivPlace (yv i)) 1 := by
    simp only [yv, n, Equiv.apply_symm_apply, Finsupp.smul_single_one]
    rw [show (∑ i : Fin k, Finsupp.single (v i) (D (v i))) = ∑ x : ↥S, Finsupp.single x.1 (D x.1) from
      Fintype.sum_equiv σ _ (fun x : ↥S => Finsupp.single x.1 (D x.1)) (fun i => rfl)]
    rw [Finset.sum_coe_sort S (fun x => Finsupp.single x (D x))]
    exact (Finsupp.sum_single D).symm

  haveI := 𝔛.isProper
  have hsec : ∀ i, ∃ uu : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj),
      barPt Pl ≫ uu.1 = (yv i).1 ≫ 𝔛.eeta ≫ pullback.fst _ _ := by
    intro i
    have hx : ((yv i).1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj = genPt p := by
      simp only [Category.assoc]
      rw [pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, (yv i).2, Category.id_comp]
    exact ModularCurve.JZeroNeronObjectAtP.exists_schemeHomOver_barPt_comp_eq_of_isProper p Pl ρ hρ
      (toBase p (ΓM M H) hj) ⟨_, hx⟩
  choose u hu using hsec

  have hcond : ∀ i, (Spec.map (CommRingCat.ofHom (residue ↥Pl)) ≫ (u i).1) ≫ toBase p (ΓM M H) hj =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom ((residue ↥Pl).comp ρ)) := by
    intro i
    rw [Category.assoc, (u i).2, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let uκ : Fin k → (Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((residue ↥Pl).comp ρ)) :=
    fun i => pullback.lift _ _ (hcond i)
  have huκ₁ : ∀ i, uκ i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (residue ↥Pl)) ≫ (u i).1 :=
    fun i => pullback.lift_fst _ _ _
  have huκ₂ : ∀ i, uκ i ≫ pullback.snd _ _ = 𝟙 _ := fun i => pullback.lift_snd _ _ _

  let y : Fin k → ↥(fibre (Γ := ΓM M H) (hj := hj) ((residue ↥Pl).comp ρ)) :=
    fun i => (uκ i).base (closedPoint (ResidueField ↥Pl))
  have hrange_uκ : ∀ i, Set.range (uκ i).base = {y i} := by
    intro i
    ext z
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, rfl⟩
      rw [Subsingleton.elim t (closedPoint (ResidueField ↥Pl))]
    · rintro rfl
      exact ⟨_, rfl⟩
  have hy_closed : ∀ i, IsClosed ({y i} : Set ↥(fibre (Γ := ΓM M H) (hj := hj) ((residue ↥Pl).comp ρ))) := by
    intro i
    haveI : IsClosedImmersion (uκ i) := isClosedImmersion_of_comp_eq_id _ _ (huκ₂ i)
    rw [← hrange_uκ i]
    exact (uκ i).isClosedEmbedding.isClosed_range

  have hback : ∀ (i : Fin k) (j : Fin 2) (y0 : ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((residue ↥Pl).comp ρ))),
      (𝔛.comp Pl hPl ρ hρ j).base y0 = y i →
      ∃ P : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C, (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ j).base P.1 = y i := by
    intro i j y0 hy0
    haveI := 𝔛.comp_isClosedImmersion Pl hPl ρ hρ j
    let x0 := (inv (𝔛.efib Pl hPl ρ hρ)).base y0
    have hx0 : (𝔛.efib Pl hPl ρ hρ).base x0 = y0 := by
      show (𝔛.efib Pl hPl ρ hρ) ((inv (𝔛.efib Pl hPl ρ hρ)) y0) = y0
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      simp
    have hy0cl : IsClosed ({y0} : Set ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((residue ↥Pl).comp ρ))) := by
      rw [(𝔛.comp Pl hPl ρ hρ j).isClosedEmbedding.isClosed_iff_image_isClosed, Set.image_singleton, hy0]
      exact hy_closed i
    have hx0cl : IsClosed ({x0} : Set ↥(𝔛.Mfib Pl hPl ρ hρ).C) := by
      rw [(𝔛.efib Pl hPl ρ hρ).isClosedEmbedding.isClosed_iff_image_isClosed, Set.image_singleton, hx0]
      exact hy0cl
    refine ⟨⟨x0, hx0cl⟩, ?_⟩
    show (𝔛.comp Pl hPl ρ hρ j).base ((𝔛.efib Pl hPl ρ hρ).base x0) = y i
    rw [hx0, hy0]

  let ut : Fin k → (Spec (CommRingCat.of ↥Pl) ⟶ pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) :=
    fun i => pullback.lift (u i).1 (𝟙 _) (by rw [(u i).2, Category.id_comp])
  have hut_gen : ∀ i, barPt Pl ≫ ut i = (yv i).1 ≫ gA := by
    intro i
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hu, Category.assoc, hgA₁]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.assoc, hgA₂, ← Category.assoc, (yv i).2,
        Category.id_comp]
  have hut_sp : ∀ i, Spec.map (CommRingCat.ofHom (residue ↥Pl)) ≫ ut i = uκ i ≫ bc := by
    intro i
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, hbc₁, huκ₁]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.assoc, hbc₂, ← Category.assoc, huκ₂,
        Category.id_comp]
  have hres_pt : (Spec.map (CommRingCat.ofHom (residue ↥Pl))).base (closedPoint (ResidueField ↥Pl)) = closedPoint ↥Pl :=
    IsLocalRing.comap_closedPoint (residue ↥Pl)

  have hgenV : ∀ i, bc.base (y i) ∈ V → gA.base ((yv i).1.base (closedPoint (AlgebraicClosure ℚ))) ∈ V := by
    intro i hyV
    have h1 : gA.base ((yv i).1.base (closedPoint (AlgebraicClosure ℚ))) =
        (ut i).base ((barPt Pl).base (closedPoint (AlgebraicClosure ℚ))) := by
      have := congrArg (fun f => f.base (closedPoint (AlgebraicClosure ℚ))) (hut_gen i)
      simpa using this.symm
    have h2 : bc.base (y i) = (ut i).base (closedPoint ↥Pl) := by
      have := congrArg (fun f => f.base (closedPoint (ResidueField ↥Pl))) (hut_sp i)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
      rw [hres_pt] at this
      exact this.symm
    have hspec : (ut i).base ((barPt Pl).base (closedPoint (AlgebraicClosure ℚ))) ⤳ (ut i).base (closedPoint ↥Pl) :=
      (IsLocalRing.specializes_closedPoint _).map (ut i).base.hom.continuous
    rw [h1]
    exact hspec.mem_open V.isOpen (h2 ▸ hyV)

  have hcrossV : ∀ i, y i ∈ Set.range (𝔛.comp Pl hPl ρ hρ 0).base → y i ∈ Set.range (𝔛.comp Pl hPl ρ hρ 1).base →
      bc.base (y i) ∈ V := by
    intro i h0 h1
    obtain ⟨y0, hy0⟩ := h0
    obtain ⟨P, hP⟩ := hback i 0 y0 hy0
    have hss : (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P ∈ ModularCurve.ssPlacesQExp (ResidueField ↥Pl) (ΓN p M H hpM) p := by
      by_contra hns
      have h := (ModularCurve.XHDRModelAtP.not_mem_range_comp_one_and_mem_smoothLocus_of_placeOfPoint_not_mem_ssPlacesQExp
        p M H hpM hpM2 hj 𝔛 Pl hPl ρ hρ P.1 P.2 hns).1
      rw [hP] at h
      exact h h1
    have := hTV P hss
    rwa [hP] at this

  have hy_fst : ∀ i, (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((residue ↥Pl).comp ρ)))).base (y i) =
      (u i).1.base (closedPoint ↥Pl) := by
    intro i
    have := congrArg (fun f => f.base (closedPoint (ResidueField ↥Pl))) (huκ₁ i)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    rw [hres_pt] at this
    exact this
  have husm_closed : ∀ i, (u i).1.base (closedPoint ↥Pl) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) := by
    intro i
    rw [← hy_fst i]
    have key := (ModularCurve.XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
      p M H hpM hpM2 hj 𝔛 Pl hPl ρ hρ (y i)).mpr ?_
    · exact key
    · rintro ⟨h0, h1⟩
      have hzero := hV (yv i) (hgenV i (hcrossV i h0 h1))
      simp only [yv, Equiv.apply_symm_apply] at hzero
      exact (Finsupp.mem_support_iff.mp (hvS i)) hzero
  have husm : ∀ i, Set.range (u i).1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) := by
    rintro i _ ⟨t, rfl⟩
    have hspec : (u i).1.base t ⤳ (u i).1.base (closedPoint ↥Pl) :=
      (IsLocalRing.specializes_closedPoint t).map (u i).1.base.hom.continuous
    exact hspec.mem_open 𝔛.smoothLocus.isOpen (husm_closed i)

  let c : Fin k → Fin 2 := fun i => if y i ∈ Set.range (𝔛.comp Pl hPl ρ hρ 0).base then 0 else 1
  have hyc : ∀ i, y i ∈ Set.range (𝔛.comp Pl hPl ρ hρ (c i)).base := by
    intro i
    by_cases h0 : y i ∈ Set.range (𝔛.comp Pl hPl ρ hρ 0).base
    · simp only [c, if_pos h0]; exact h0
    · simp only [c, if_neg h0]
      exact (𝔛.comp_jointly_surjective Pl hPl ρ hρ (y i)).resolve_left h0
  have hP : ∀ i, ∃ P : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
      (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ (c i)).base P.1 = y i :=
    fun i => hback i (c i) (hyc i).choose (hyc i).choose_spec
  choose P hP using hP
  exact ⟨k, c, yv, u, uκ, P, n, hu, husm, huκ₁, huκ₂, fun i => hP i, hDv⟩

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero.ModularCurve in

theorem ModularCurve.XHDRModelAtP.ssPlacesQExp_nonempty_levelN
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)
    (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] :
    (ModularCurve.ssPlacesQExp K (ΓN p M H hpM) p).Nonempty := by
  haveI : NeZero (M / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) (Fact.out : p.Prime).pos).ne'⟩
  have hpN : ¬ p ∣ M / p := by
    intro h; apply hpM2; obtain ⟨k, hk⟩ := h; refine ⟨k, ?_⟩
    have := Nat.div_mul_cancel hpM; rw [hk] at this; rw [pow_two]; linarith [this]
  exact ModularCurve.nonempty_ssPlacesQExp (M / p) (ΓN p M H hpM) (Gamma1_le_GammaH (M / p) _) (CohCarrier.GammaH_le_Gamma0 _)
    p hpN K

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in

theorem ModularCurve.XHDRModelAtP.finite_and_isClosed_bc_comp_zero_of_ssPlacesQExp
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))) :
    Set.Finite {x : ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) | ∃ Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
      (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p ∧
      x = bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1)} ∧
    ∀ t ∈ {x : ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) | ∃ Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
      (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p ∧
      x = bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1)},
      IsClosed ({t} : Set ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))) := by
  classical
  haveI : NeZero (M / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) (Fact.out : p.Prime).pos).ne'⟩
  haveI : (ΓN p M H hpM).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH (M / p) _)

  have hSS : (ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p).Finite :=
    ModularCurve.finite_ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) p (ΓN p M H hpM) (translation_mem_GammaH _ _)
  have hPfin : {Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C |
      (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p}.Finite :=
    hSS.preimage (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint_bijective.1.injOn
  refine ⟨?_, ?_⟩
  · refine (hPfin.image fun Pbar => bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1)).subset ?_
    rintro _ ⟨Pbar, hss, rfl⟩
    exact ⟨Pbar, hss, rfl⟩

  · haveI := 𝔛.comp_isClosedImmersion Pl hPl ρ hρ 0
    have hcomp : Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ)) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ Spec.map (CommRingCat.ofHom ρ) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hbig : IsPullback (bc ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))
        (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ))))
        (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ Spec.map (CommRingCat.ofHom ρ)) := by
      rw [hbc₁, ← hcomp]
      exact IsPullback.of_hasPullback _ _
    have hsq : IsPullback bc (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ))))
        (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))) :=
      IsPullback.of_right hbig hbc₂ (IsPullback.of_hasPullback _ _)
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))) :=
      IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
    haveI : IsClosedImmersion bc := MorphismProperty.of_isPullback hsq.flip inferInstance
    rintro _ ⟨Pbar, -, rfl⟩
    have h1 : IsClosed ({(𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1} : Set _) := by
      rw [← Set.image_singleton, ← (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).isClosedEmbedding.isClosed_iff_image_isClosed]
      exact Pbar.2
    rw [← Set.image_singleton, ← bc.isClosedEmbedding.isClosed_iff_image_isClosed]
    exact h1

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in

theorem ModularCurve.XHDRModelAtP.ord_eq_zero_of_isUnit_of_mem
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    [IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]
    (e : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(ModularCurve.xHFunctionFieldBar M H))
    (he : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))) (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
      haveI : Nonempty (Scheme.Opens.toScheme U) := by
        obtain ⟨⟨x, hx⟩⟩ := hne
        exact ⟨⟨gA.base x, hx⟩⟩
      e ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) =
        𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a))) :
    ∀ (W : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) (U' : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
      (hxU' : gA.base ((𝔛.Meta.pointEquivPlace.symm W).1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ∈ U')
      (w : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U')), IsUnit w →
      haveI : Nonempty (Scheme.Opens.toScheme U') := ⟨⟨_, hxU'⟩⟩
      W.ord (e ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U' w)) = 0 := by
  intro W U' hxU' w hw
  have hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U')) :=
    ⟨⟨(𝔛.Meta.pointEquivPlace.symm W).1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)), hxU'⟩⟩
  have h1 := he U' hne w
  simp only at h1
  rw [h1]
  haveI := hne
  have h2 := AlgebraicCurve.CurveModel.ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit 𝔛.Meta (gA ⁻¹ᵁ U')
    (pointEquivClosedPoint 𝔛.Meta.toBase (𝔛.Meta.pointEquivPlace.symm W)) hxU' ((gA.app U').hom w) (hw.map _)
  rwa [← AlgebraicCurve.CurveModel.pointEquivPlace_apply, Equiv.apply_symm_apply] at h2

namespace GaussAux

theorem mem_of_pow_mem {K : Type*} [Field K] (A : ValuationSubring K) {x : K} (hx : x ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (h : x ^ n ∈ A) : x ∈ A := by
  rcases A.mem_or_inv_mem x with hA | hA
  · exact hA
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have key : x = x ^ (m + 1) * (x⁻¹) ^ m := by
      rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ hx, one_pow, mul_one]
    rw [key]
    exact A.mul_mem _ _ h (A.pow_mem hA m)

end GaussAux

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
set_option maxHeartbeats 1600000 in

theorem ModularCurve.XHDRModelAtP.exists_gaussWitness_of_isUnit_of_ffEquiv_symm_germToFunctionField_eq_mul_pow
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

    (f h : ↥(ModularCurve.xHFunctionFieldBar M H))
    (y : LaurentSeries ↥Pl)
    (hfy : (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y)
    (hy : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0)

    (Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
    (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (hzU : bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1) ∈ U)
    (hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U)))
    (s : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)) (hsu : IsUnit s)
    (hsF : 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s)) = f * h ^ p) :
    ∃ (xh yh : LaurentSeries ↥Pl) (hbar : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xh ≠ 0 ∧
      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) yh ≠ 0 ∧
      (h : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype yh = ModularCurve.coeffMap Pl.subtype xh ∧
      (hbar : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) yh =
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xh := by
  haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos).ne'⟩
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero

  let Φ : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U) →+* ↥(ModularCurve.xHFunctionFieldBar M H) :=
    (𝔛.Meta.ffEquiv.symm : 𝔛.Meta.C.functionField ≃+* ↥(ModularCurve.xHFunctionFieldBar M H)).toRingHom.comp
      ((𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U)).hom.comp (gA.app U).hom)
  have hΦ : ∀ t, Φ t = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t)) := fun t => rfl
  have hΦs : Φ s = f * h ^ p := (hΦ s).trans hsF

  let sinv : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U) := ((hsu.unit⁻¹ : (Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U))ˣ) : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U))
  have hFinv : (f * h ^ p) * Φ sinv = 1 := by
    rw [← hΦs, ← map_mul, IsUnit.mul_val_inv, map_one]
  have hF0 : f * h ^ p ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hFinv
    exact zero_ne_one hFinv

  obtain ⟨-, xs, ys, hys, hFw, -, -⟩ :=
    ModularCurve.XHDRModelAtP.exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ Pbar U hzU hne s
  obtain ⟨-, xs', ys', hys', hFw', -, -⟩ :=
    ModularCurve.XHDRModelAtP.exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ Pbar U hzU hne sinv
  rw [← hΦ sinv] at hFw'

  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H :=
    ModularCurve.Gamma1_le_GammaH M _ (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  obtain ⟨Rg, hRi, -, hRiii⟩ :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
      (AlgebraicClosure ℚ) Pl (CohCarrier.GammaH M H) hT

  have hFmem : f * h ^ p ∈ Rg.integers := (hRi (f * h ^ p)).mpr ⟨xs, ys, hys, by rw [← hsF]; exact hFw⟩
  have hFinvmem : Φ sinv ∈ Rg.integers := (hRi (Φ sinv)).mpr ⟨xs', ys', hys', hFw'⟩
  have hιy0 : ModularCurve.coeffMap Pl.subtype y ≠ 0 := fun h0 => by
    apply hy
    have : y = 0 := by
      have hinj : Function.Injective (ModularCurve.coeffMap Pl.subtype) := fun a b hab => by
        ext k
        have hk := congrArg (fun t : LaurentSeries (AlgebraicClosure ℚ) => t.coeff k) hab
        simp only [ModularCurve.coeffMap_coeff] at hk
        exact hk
      exact hinj (h0.trans (map_zero _).symm)
    rw [this, map_zero]
  have hf0 : f ≠ 0 := fun h0 => by
    apply hιy0
    rw [← hfy, h0]
    rfl
  have hfmem : f ∈ Rg.integers := (hRi f).mpr ⟨y, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one, hfy]⟩
  have hcoe : ((f⁻¹ : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = ((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ := by
    push_cast
    rfl
  have hfinvmem : f⁻¹ ∈ Rg.integers := (hRi f⁻¹).mpr ⟨1, y, hy, by
    rw [map_one]
    show ((f⁻¹ : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype y = 1
    rw [hcoe, hfy, inv_mul_cancel₀ hιy0]⟩

  have hh0 : h ≠ 0 := fun h0 => by
    apply hF0
    rw [h0, zero_pow hp0, mul_zero]
  have hhp : h ^ p ∈ Rg.integers := by
    have : h ^ p = (f * h ^ p) * f⁻¹ := by rw [mul_comm f, mul_assoc, mul_inv_cancel₀ hf0, mul_one]
    rw [this]
    exact Rg.integers.mul_mem _ _ hFmem hfinvmem
  have hhinvp : (h⁻¹) ^ p ∈ Rg.integers := by
    have hFinv' : Φ sinv = (f * h ^ p)⁻¹ := (eq_inv_of_mul_eq_one_right hFinv)
    have : (h⁻¹) ^ p = Φ sinv * f := by
      rw [hFinv', inv_pow, mul_inv, mul_comm f⁻¹, mul_assoc, inv_mul_cancel₀ hf0, mul_one]
    rw [this]
    exact Rg.integers.mul_mem _ _ hFinvmem hfmem
  have hhA : h ∈ Rg.integers := GaussAux.mem_of_pow_mem _ hh0 hp0 hhp
  have hhA' : h⁻¹ ∈ Rg.integers := GaussAux.mem_of_pow_mem _ (inv_ne_zero hh0) hp0 hhinvp

  have hunit : IsUnit (⟨h, hhA⟩ : Rg.integers) :=
    ⟨⟨⟨h, hhA⟩, ⟨h⁻¹, hhA'⟩, Subtype.ext (mul_inv_cancel₀ hh0), Subtype.ext (inv_mul_cancel₀ hh0)⟩, rfl⟩
  have hres : Rg.residue ⟨h, hhA⟩ ≠ 0 := AlgebraicCurve.RegularProlongation.residue_ne_zero_of_isUnit Rg hunit

  obtain ⟨xh, yh, hyh, hhw⟩ := (hRi h).mp hhA
  have hiii := hRiii h hhA xh yh hyh hhw
  have hxh : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xh ≠ 0 := by
    rw [← hiii]
    refine mul_ne_zero ?_ hyh
    exact_mod_cast hres

  obtain ⟨g', hg'⟩ := ModularCurve.exists_qExpFunctionFieldC_infSubgroup_coe_eq_of_charP p M H hpM hpM2 hHp
    (IsLocalRing.ResidueField ↥Pl) (Rg.residue ⟨h, hhA⟩)
  exact ⟨xh, yh, g', hxh, hyh, hhw, hg' ▸ hiii⟩

set_option maxHeartbeats 3200000 in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero.ModularCurve in
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

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

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
    (hy : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0) :
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
        ((Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) =
          ∑ i, n i • Finsupp.single (𝔛.Meta.pointEquivPlace (yv i)) 1) ∧

        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v =
            (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v + v.ord h) ∧

        (∀ Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
          (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∈
            ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
            (_ : bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1) ∈ U)
            (_ : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U)))
            (s : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
            IsUnit s ∧
            𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s)) = f * h ^ p) := by
  classical
  haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) (Fact.out : p.Prime).pos).ne'⟩

  obtain ⟨hint, hdens, -⟩ :=
    ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
      p M hpM H Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂
  haveI := hint

  have hS1 : ∃ σ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) O.g,
      barPt Pl ≫ σ.1 = (O.pts z).1 ∧
      (fun τ => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ τ σ)^[p] ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).one _) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).one _ := by
    have hext : ExtendsToPlace Pl (Spec.map (CommRingCat.ofHom ρ)) (O.pts (AlgebraicCurve.Pic0.mk D')) := by
      rw [hσA, ← hD'] at hz
      exact hz
    have hm : p • AlgebraicCurve.Pic0.mk D' = 0 := by rw [hD']; exact hpz
    obtain ⟨σ, hσ, hpσ⟩ :=
      ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_barPt_comp_eq_pts_and_iterate_mul_eq_one_of_extendsToPlace_of_nsmul_eq_zero
        p M hpM H Pl hPl hj 𝔛 Λ O hD hpts_law ρ hρ D' hext p hm
    refine ⟨σ, ?_, hpσ⟩
    rw [hσ, hD']
  obtain ⟨σ, hσ, hpσ⟩ := hS1

  let 𝓛 : RigidifiedLineBundle (toBase p (ΓM M H) hj) 𝔛.εinf (Spec.map (CommRingCat.ofHom ρ)) := hD.poincare.pullbackAlong σ

  have hpow : Nonempty ((((fun N : RigidifiedLineBundle (toBase p (ΓM M H) hj) 𝔛.εinf (Spec.map (CommRingCat.ofHom ρ)) => N.tensor 𝓛)^[p]) (RigidifiedLineBundle.unit _)).L ≅
      (RigidifiedLineBundle.unit (c := toBase p (ΓM M H) hj) (ε := 𝔛.εinf) (Spec.map (CommRingCat.ofHom ρ))).L) :=
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_iterate_tensor_pullbackAlong_unit_iso_unit_of_iterate_mul_one_eq_one
      (P := algEquivZeroGroupCut _ _) hD (Spec.map (CommRingCat.ofHom ρ)) σ p hpσ

  have hH3 : IsOpenImmersion gA ∧
      ∃ e : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(xHFunctionFieldBar M H),
        ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))) (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
          haveI : Nonempty (Scheme.Opens.toScheme U) := by
            obtain ⟨⟨x, hx⟩⟩ := hne
            exact ⟨⟨gA.base x, hx⟩⟩
          e ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) =
            𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a)) :=
    ModularCurve.XHDRModelAtP.isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre p M H hpM hj 𝔛 Pl hPl ρ hρ gA hgA₁ hgA₂
  obtain ⟨hgAoi, e, he⟩ := hH3

  have hSSne : (ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p).Nonempty := by
    have hpN : ¬ p ∣ M / p := by
      rintro ⟨c, hc⟩
      apply hpM2
      refine ⟨c, ?_⟩
      rw [pow_two, mul_assoc, ← hc, Nat.mul_div_cancel' hpM]
    exact ModularCurve.nonempty_ssPlacesQExp (M / p) (ΓN p M H hpM)
      (ModularCurve.Gamma1_le_GammaH _ _) (CohCarrier.GammaH_le_Gamma0 _) p hpN (IsLocalRing.ResidueField ↥Pl)
  obtain ⟨Pss, hPss⟩ : ∃ Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
      (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p := by
    obtain ⟨v, hv⟩ := hSSne
    obtain ⟨Pbar, rfl⟩ := (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint_bijective.2 v
    exact ⟨Pbar, hv⟩

  have hS3 : ∃ φ : ∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Γ(𝓛.L, U) →+ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField : Type),
      (∀ (U V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(𝓛.L, U), φ V (𝓛.L.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty U] (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)) (m : Γ(𝓛.L, U)),
          φ U (a • m) = algebraMap Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField a * φ U m) ∧
      (∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Nonempty U → Function.Injective (φ U)) :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_functionField_presentation 𝓛.L 𝓛.isInvertible
  obtain ⟨φ, hφnat, hφsmul, hφinj⟩ := hS3

  have hS4 : ∃ Uaff : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, IsAffineOpen Uaff ∧
      ∀ Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
        (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p →
        bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1) ∈ Uaff :=
    ModularCurve.XHDRModelAtP.exists_isAffineOpen_forall_mem_of_placeOfPoint_mem_ssPlacesQExp p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ bc hbc₁ hbc₂
  obtain ⟨Uaff, hUaff, hTU⟩ := hS4

  have hS5 : ∃ (V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hVU : V ≤ Uaff) (s : Γ(𝓛.L, V)),
      (∀ Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
        (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p →
        bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1) ∈ V) ∧
      AlgebraicGeometry.Scheme.Modules.IsFrameOn s V := by

    let T : Set ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) := {x | ∃ Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
      (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p ∧
      x = bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1)}
    obtain ⟨hTfin, hTcl⟩ :
        T.Finite ∧ ∀ t ∈ T, IsClosed ({t} : Set ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))) :=
      ModularCurve.XHDRModelAtP.finite_and_isClosed_bc_comp_zero_of_ssPlacesQExp p M hpM H Pl hPl hj 𝔛 ρ hρ bc hbc₁ hbc₂
    have hTU' : T ⊆ (Uaff : Set ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))) := by
      rintro _ ⟨Pbar, hss, rfl⟩
      exact hTU Pbar hss
    obtain ⟨V, hVU, s, hTV, hframe⟩ :=
      AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn_of_finite_subset_affineOpen 𝓛.L 𝓛.isInvertible Uaff hUaff T hTfin hTU' hTcl
    exact ⟨V, hVU, s, fun Pbar hss => hTV ⟨Pbar, hss, rfl⟩, hframe⟩
  obtain ⟨V, hVU, s, hTV, hframe⟩ := hS5

  have hgen : ∀ Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
      (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p →
      ∀ (W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hW : W ≤ V), bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1) ∈ W →
        ∀ m : Γ(𝓛.L, W), ∃ a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), W), m = a • 𝓛.L.presheaf.map (homOfLE hW).op s := by
    intro Pbar _ W hW _ m
    obtain ⟨a, ha⟩ := (hframe hW hW).2 m
    exact ⟨a, ha.symm⟩

  have hS6 : ∃ c' : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField, c' ≠ 0 ∧
      ∀ (x : ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))) (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hxU : x ∈ U) (m : Γ(𝓛.L, U)),
        (∀ (W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hW : W ≤ U), x ∈ W →
          ∀ m' : Γ(𝓛.L, W), ∃ a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), W), m' = a • 𝓛.L.presheaf.map (homOfLE hW).op m) →
        ∃ (U' : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : x ∈ U') (_ : U' ≤ U) (w : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U')),
          IsUnit w ∧
          haveI : Nonempty (Scheme.Opens.toScheme U') := ⟨⟨x, ‹x ∈ U'›⟩⟩
          haveI : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨x, hxU⟩⟩
          (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U' w = c' * (φ U m) ^ p := by

    have hLeq : ∀ n : ℕ, (((fun N : RigidifiedLineBundle (toBase p (ΓM M H) hj) 𝔛.εinf (Spec.map (CommRingCat.ofHom ρ)) => N.tensor 𝓛)^[n]) (RigidifiedLineBundle.unit _)).L = 𝓛.L.tensorPow n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', AlgebraicGeometry.Scheme.Modules.tensorPow_succ, ← ih]
        rfl
    have eL : 𝓛.L.tensorPow p ≅ 𝟙_ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules := by
      refine (eqToIso (hLeq p)).symm ≪≫ hpow.some ≪≫ eqToIso ?_
      rfl
    obtain ⟨F, hF0, hFx⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_exists_isFrameOn_isUnit_germToFunctionField_eq_mul_pow_of_tensorPow_iso
      𝓛.L 𝓛.isInvertible p eL φ hφnat hφsmul hφinj
    refine ⟨F, hF0, fun x U hxU m hgenm => ?_⟩
    obtain ⟨U₀, hx₀, e₀, u₀, he₀, hu₀, hgerm₀⟩ := hFx x

    let W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens := U ⊓ U₀
    have hxW : x ∈ W := ⟨hxU, hx₀⟩
    haveI : Nonempty (Scheme.Opens.toScheme W) := ⟨⟨x, hxW⟩⟩
    haveI : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨x, hxU⟩⟩
    haveI : Nonempty (Scheme.Opens.toScheme U₀) := ⟨⟨x, hx₀⟩⟩
    obtain ⟨a, ha⟩ := hgenm W inf_le_left hxW (𝓛.L.presheaf.map (homOfLE (inf_le_right : W ≤ U₀)).op e₀)
    obtain ⟨b, hb⟩ := (he₀ (inf_le_right : W ≤ U₀) inf_le_right).2 (𝓛.L.presheaf.map (homOfLE (inf_le_left : W ≤ U)).op m)

    have hb' : b • 𝓛.L.presheaf.map (homOfLE (inf_le_right : W ≤ U₀)).op e₀ =
        𝓛.L.presheaf.map (homOfLE (inf_le_left : W ≤ U)).op m := hb
    have hab : a * b = 1 := by
      have h1 : (a * b) • 𝓛.L.presheaf.map (homOfLE (inf_le_right : W ≤ U₀)).op e₀ =
          (1 : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), W)) • 𝓛.L.presheaf.map (homOfLE (inf_le_right : W ≤ U₀)).op e₀ := by
        rw [mul_smul, hb', ← ha, one_smul]
      exact (he₀ (inf_le_right : W ≤ U₀) inf_le_right).1 h1

    have hφe : φ U₀ e₀ = algebraMap Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), W) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField a * φ U m := by
      rw [← hφnat U₀ W inf_le_right inferInstance e₀, ha, hφsmul, hφnat U W inf_le_left inferInstance m]

    obtain ⟨ainv, hainv⟩ : ∃ ainv : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), W), a * ainv = 1 := ⟨b, hab⟩
    refine ⟨W, hxW, inf_le_left, (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.map (homOfLE (inf_le_right : W ≤ U₀)).op u₀ * ainv ^ p, ?_, ?_⟩
    · have hainvU : IsUnit ainv := ⟨⟨ainv, a, by rw [mul_comm]; exact hainv, hainv⟩, rfl⟩
      exact (hu₀.map _).mul (hainvU.pow _)
    · have hg0 : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField W ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.map (homOfLE (inf_le_right : W ≤ U₀)).op u₀) =
          (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U₀ u₀ := by
        show ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.map (homOfLE (inf_le_right : W ≤ U₀)).op ≫ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField W).hom u₀ = _
        unfold Scheme.germToFunctionField
        rw [TopCat.Presheaf.germ_res]
      have halg : ∀ z : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), W), algebraMap Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), W) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField z = (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField W z :=
        fun z => rfl
      rw [map_mul, map_pow, hg0, hgerm₀, hφe, mul_pow]
      have hu1 : (algebraMap Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), W) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField a) ^ p *
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField W ainv) ^ p = 1 := by
        rw [← halg ainv, ← mul_pow, ← map_mul, hainv, map_one, one_pow]
      linear_combination (F * (φ U m) ^ p) * hu1
  obtain ⟨c', hc'0, hunit⟩ := hS6

  have hGEN : ∃ (Dφ : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) (g₁ : ↥(ModularCurve.xHFunctionFieldBar M H)), g₁ ≠ 0 ∧
      (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
        Dφ v = (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v + v.ord g₁) ∧
      ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (q : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (hq : gA.base (q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ∈ U) (m : Γ(𝓛.L, U)),
        haveI : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨_, hq⟩⟩
        (φ U m ≠ 0 → -Dφ (𝔛.Meta.pointEquivPlace q) ≤ (𝔛.Meta.pointEquivPlace q).ord (e (φ U m))) ∧
        ((∀ (W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hW : W ≤ U), gA.base (q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ∈ W →
            ∀ m' : Γ(𝓛.L, W), ∃ a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), W), m' = a • 𝓛.L.presheaf.map (homOfLE hW).op m) →
          (𝔛.Meta.pointEquivPlace q).ord (e (φ U m)) = -Dφ (𝔛.Meta.pointEquivPlace q)) :=
    ModularCurve.JHNeronObjectAtP.exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts
      p M hpM hpM2 H hHp Pl hPl hj 𝔛 Λ O hD hDQ hsep ajQ kQ ajbar εbar hpoinc hajQε hajQ hkQ₁ hkQ₂ hajbar hajbar_over
      hεbar hεbar_aj hpts_law hAJ ρ hρ gA hgA₁ hgA₂ z D' hD' σ hσ φ hφnat hφsmul hφinj e he
  obtain ⟨Dφ, g₁, hg₁, hDφ, hordφ⟩ := hGEN

  have hS7b : ∃ cst : AlgebraicClosure ℚ, cst ≠ 0 ∧
      e c' = algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) cst * f * g₁ ^ p := by

    have hunitord : ∀ (W : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) (U' : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
        (hxU' : gA.base ((𝔛.Meta.pointEquivPlace.symm W).1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ∈ U')
        (w : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U')), IsUnit w →
        haveI : Nonempty (Scheme.Opens.toScheme U') := ⟨⟨_, hxU'⟩⟩
        W.ord (e ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U' w)) = 0 :=
      ModularCurve.XHDRModelAtP.ord_eq_zero_of_isUnit_of_mem p M hpM H Pl hj 𝔛 ρ gA e he

    have hconst : ∀ u : ↥(ModularCurve.xHFunctionFieldBar M H), u ≠ 0 → (∀ W : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H), W.ord u = 0) →
        ∃ cst : AlgebraicClosure ℚ, u = algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) cst := by
      haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
      have hjmem : ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.jqModC ℚ) ∈ ModularCurve.xHFunctionFieldBar M H :=
        ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC_mono ℚ le_top hj)
      obtain ⟨htr, hfd⟩ :=
        ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
          (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H) ⟨_, hjmem⟩
          (show (ModularCurve.jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = _ from ModularCurve.map_jqModC _)
      haveI := hfd
      intro x _ hx
      obtain ⟨c, hc⟩ := AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed _ htr hx
      exact ⟨c, hc.symm⟩

    have hordc : ∀ W : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H), W.ord (e c') = (p : ℤ) * Dφ W := by
      intro W
      set q := 𝔛.Meta.pointEquivPlace.symm W with hq_def
      have hWq : 𝔛.Meta.pointEquivPlace q = W := by rw [hq_def, Equiv.apply_symm_apply]
      set x : ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) := gA.base (q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) with hx_def
      obtain ⟨U, m, hxU, hm⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn 𝓛.isInvertible x
      have hgenm : ∀ (W' : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hW' : W' ≤ U), x ∈ W' →
          ∀ m' : Γ(𝓛.L, W'), ∃ a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), W'), m' = a • 𝓛.L.presheaf.map (homOfLE hW').op m := by
        intro W' hW' _ m'
        obtain ⟨a, ha⟩ := (hm hW' hW').2 m'
        exact ⟨a, ha.symm⟩
      obtain ⟨U', hxU', hU'U, w, hw, hgerm⟩ := hunit x U hxU m hgenm
      have h1 : (𝔛.Meta.pointEquivPlace q).ord (e (φ U m)) = -Dφ (𝔛.Meta.pointEquivPlace q) := (hordφ U q hxU m).2 hgenm
      rw [hWq] at h1
      have h2 := hunitord W U' hxU' w hw
      haveI : Nonempty (Scheme.Opens.toScheme U') := ⟨⟨_, hxU'⟩⟩
      haveI : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨_, hxU⟩⟩
      have hφm0 : φ U m ≠ 0 := by
        intro h0
        rw [h0, zero_pow (Fact.out : p.Prime).ne_zero, mul_zero,
          map_eq_zero_iff _ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField_injective U')] at hgerm
        rw [hgerm] at hw
        exact not_isUnit_zero hw
      have h3 : W.ord (e ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U' w)) = W.ord (e c') + (p : ℤ) * W.ord (e (φ U m)) := by
        rw [hgerm, map_mul, map_pow, AlgebraicCurve.Place.ord_mul _ ((map_ne_zero e).mpr hc'0)
          (pow_ne_zero _ ((map_ne_zero e).mpr hφm0)), ← zpow_natCast, AlgebraicCurve.Place.ord_zpow]
      rw [h2, h1] at h3
      linarith

    have hf0 : f ≠ 0 := hf
    have hu0 : e c' * (f * g₁ ^ p)⁻¹ ≠ 0 :=
      mul_ne_zero ((map_ne_zero e).mpr hc'0) (inv_ne_zero (mul_ne_zero hf0 (pow_ne_zero _ hg₁)))
    obtain ⟨cst, hcst⟩ := hconst _ hu0 fun W => by
      rw [AlgebraicCurve.Place.ord_mul _ ((map_ne_zero e).mpr hc'0) (inv_ne_zero (mul_ne_zero hf0 (pow_ne_zero _ hg₁))),
        AlgebraicCurve.Place.ord_inv, AlgebraicCurve.Place.ord_mul _ hf0 (pow_ne_zero _ hg₁), ← zpow_natCast,
        AlgebraicCurve.Place.ord_zpow, hordc W, hDφ W, ← hdiv W]
      ring
    refine ⟨cst, ?_, ?_⟩
    · rintro rfl
      rw [map_zero] at hcst
      exact hu0 hcst
    · have : e c' = algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) cst * (f * g₁ ^ p) := by
        rw [← hcst, mul_assoc, inv_mul_cancel₀ (mul_ne_zero hf0 (pow_ne_zero _ hg₁)), mul_one]
      rw [this, mul_assoc]
  obtain ⟨cst, hcst, hc'⟩ := hS7b

  obtain ⟨r, hr⟩ : ∃ r : AlgebraicClosure ℚ, r ^ p = cst := IsAlgClosed.exists_pow_nat_eq cst (Fact.out : p.Prime).pos
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hcst (by rw [← hr, zero_pow (Fact.out : p.Prime).ne_zero])

  have hVne : Nonempty (Scheme.Opens.toScheme V) := ⟨⟨_, hTV Pss hPss⟩⟩
  have hs0 : φ V s ≠ 0 := by
    intro h0
    obtain ⟨U', hzU', -, w, hw, hgerm⟩ := hunit _ V (hTV Pss hPss) s (hgen Pss hPss)
    haveI : Nonempty (Scheme.Opens.toScheme U') := ⟨⟨_, hzU'⟩⟩
    rw [h0, zero_pow (Fact.out : p.Prime).ne_zero, mul_zero, map_eq_zero_iff _ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField_injective U')] at hgerm
    rw [hgerm] at hw
    exact not_isUnit_zero hw
  let h : ↥(ModularCurve.xHFunctionFieldBar M H) := algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) r * g₁ * e (φ V s)
  have hh0 : h ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ hg₁) ?_
    · exact (map_ne_zero (algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))).mpr hr0
    · exact (map_ne_zero e).mpr hs0
  have hfh : f * h ^ p = e (c' * (φ V s) ^ p) := by
    rw [map_mul, map_pow, hc']
    simp only [h, mul_pow, ← map_pow, hr]
    ring

  have hexp : ∀ Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
      (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p →
      ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
        (_ : bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1) ∈ U)
        (_ : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U)))
        (s : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
        IsUnit s ∧
        𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s)) = f * h ^ p := by
    intro Pbar hss
    obtain ⟨U', hzU', -, w, hw, hgerm⟩ := hunit _ V (hTV Pbar hss) s (hgen Pbar hss)
    have hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U')) := hdens U' ⟨⟨_, hzU'⟩⟩
    refine ⟨U', hzU', hne, w, hw, ?_⟩
    rw [← he U' hne w, hfh, ← hgerm]

  have hgauss : ∃ (xh yh : LaurentSeries ↥Pl) (hbar : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xh ≠ 0 ∧
      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) yh ≠ 0 ∧
      (h : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype yh = ModularCurve.coeffMap Pl.subtype xh ∧
      (hbar : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) yh =
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xh := by
    obtain ⟨U, hzU, hne, s, hsu, hsF⟩ := hexp Pss hPss
    exact ModularCurve.XHDRModelAtP.exists_gaussWitness_of_isUnit_of_ffEquiv_symm_germToFunctionField_eq_mul_pow
      p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ f h y hfy hy Pss U hzU hne s hsu hsF
  obtain ⟨xh, yh, hbar, hxh, hyh, hhw, hhbar⟩ := hgauss

  have hDv : ∃ Dv : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)),
      ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
        (Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v =
          (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v + v.ord h := by
    haveI hCOgen : AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) :=
      AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        𝔛.Meta.toBase 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap
    haveI := AlgebraicCurve.IsCurveOver.hasPrincipalDivisors (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))
    obtain ⟨Dh, hDh, hDhdeg⟩ := AlgebraicCurve.HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) h hh0
    refine ⟨⟨(D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) + Dh, ?_⟩, fun v => ?_⟩
    · rw [AlgebraicCurve.Divisor.mem_degZero, map_add, hDhdeg, add_zero]
      exact AlgebraicCurve.Divisor.mem_degZero.mp D'.2
    · show ((D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) + Dh) v = _
      rw [Finsupp.add_apply, hDh v]
  obtain ⟨Dv, hDvD⟩ := hDv

  have hPACK : ∃ (k : ℕ) (c : Fin k → Fin 2)
      (yv : Fin k → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : Fin k → NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (uκ : Fin k → (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ)))
      (P : Fin k → closedPoints (𝔛.Mfib Pl hPl ρ hρ).C) (n : Fin k → ℤ),
      (∀ i, ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ (u i).1 = (yv i).1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ∧
      (∀ i, Set.range (u i).1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) ∧
      (∀ i, uκ i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ (u i).1) ∧
      (∀ i, uκ i ≫ pullback.snd _ _ = 𝟙 _) ∧
      (∀ i, (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ (c i)).base (P i).1 = (uκ i).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥Pl))) ∧
      ((Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) = ∑ i, n i • Finsupp.single (𝔛.Meta.pointEquivPlace (yv i)) 1) := by
    have hV : ∀ q : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _},
        gA.base (q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ∈ V →
        (Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) (𝔛.Meta.pointEquivPlace q) = 0 := fun q hq =>
      AlgebraicCurve.Divisor.apply_eq_zero_of_ord_eq_neg (Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
        (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) Dφ r hr0 g₁ (e (φ V s)) hg₁ ((map_ne_zero e).mpr hs0)
        (by intro w; simpa only [h] using hDvD w) hDφ _
        ((hordφ V q hq s).2 (fun W hW _ m' => ((hframe hW hW).2 m').imp fun a ha => ha.symm))
    exact ModularCurve.XHDRModelAtP.exists_configured_family_of_support_avoids p M hpM hpM2 H Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂
      bc hbc₁ hbc₂ V hTV Dv hV
  obtain ⟨k, c, yv, u, uκ, P, n, hu, husm, huκ₁, huκ₂, hP, hDv'⟩ := hPACK
  exact ⟨h, xh, yh, hbar, k, c, yv, u, uκ, P, n, Dv, hh0, hxh, hyh, hhw, hhbar, hu, husm, huκ₁, huκ₂, hP, hDv', hDvD, hexp⟩

end S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero (solution)
