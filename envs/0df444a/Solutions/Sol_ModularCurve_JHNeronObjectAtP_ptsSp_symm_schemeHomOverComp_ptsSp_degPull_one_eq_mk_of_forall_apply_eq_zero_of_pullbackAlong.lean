-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.ptsSp_symm_schemeHomOverComp_ptsSp_degPull_one_eq_mk_of_forall_apply_eq_zero_of_pullbackAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/9ab1f532-fe1d-51a2-83c9-d6bb1ccec483

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Theorems.Thm_ModularCurve_XHDRModelAtP_smul_frob_mem_ssPlacesQExp_and_frob_smul_frob_eq_of_mem_ssPlacesQExp
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_smul
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
import Theorems.Thm_ModularCurve_finrankAlong_eq_add_one_and_finrankAlong_eq_add_one_of_coe_eq_qExpand
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_degeneracyEmb_curveModel_iso_genericFibre_restrictAlong_chartPin_of_atkinLehner_generic
import Theorems.Thm_ModularCurve_XHDRModelAtP_ramificationIndexAlong_degeneracyEmb_pointEquivPlace_eq_one_of_formallyUnramified
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_opens_formallyUnramified_pi_of_comp_zero_of_forall_ne_placeOn0
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_one_frob_placeOfPoint_eq_of_comp_pi_eq_of_ne
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_eq_of_isSeparated_of_valuationRing_of_fst_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_ptsSp_degPull_one_eq_mk_of_forall_apply_eq_zero_of_pullbackAlong
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10"
p2m_attr_erase "simp" "CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_ptsSp_degPull_one_eq_mk_of_forall_apply_eq_zero_of_pullbackAlong.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_ptsSp_degPull_one_eq_mk_of_forall_apply_eq_zero_of_pullbackAlong.ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

open scoped MatrixGroups
open _root_.ModularCurve.JHNeronObjectAtP (Fbar)

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_ptsSp_degPull_one_eq_mk_of_forall_apply_eq_zero_of_pullbackAlong.AlgebraicCurve"

namespace Pull1FF

section Generic

variable {K F F₁ Z : Type*} [Field K] [Field F] [Field F₁] [Field Z] [Algebra K F] [Algebra K F₁] [Algebra K Z]

theorem restrictAlong_comp (φ : F →ₐ[K] F₁) (χ : F₁ →ₐ[K] Z) (hφ : φ.toRingHom.IsIntegral)
    (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K Z) :
    W.restrictAlong (χ.comp φ) hχφ = (W.restrictAlong χ hχ).restrictAlong φ hφ := by
  apply Place.ext
  show W.toValuationSubring.comap (χ.comp φ).toRingHom = (W.toValuationSubring.comap χ.toRingHom).comap φ.toRingHom
  rw [ValuationSubring.comap_comap]
  rfl

theorem isIntegral_algEquiv (σ : Z ≃ₐ[K] Z) : σ.toAlgHom.toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ σ.surjective

theorem isIntegral_comp_algEquiv (α : F₁ →ₐ[K] Z) (hα : α.toRingHom.IsIntegral) (σ : Z ≃ₐ[K] Z) :
    (σ.toAlgHom.comp α).toRingHom.IsIntegral :=
  RingHom.IsIntegral.trans _ _ hα (isIntegral_algEquiv σ)

theorem ofAlgAut_smul_place (σ : Z ≃ₐ[K] Z) (v : Place K Z) : SemilinearAut.ofAlgAut σ • v = σ • v :=
  Place.ext rfl

theorem ofAlgAut_symm_eq_inv (σ : Z ≃ₐ[K] Z) : SemilinearAut.ofAlgAut σ.symm = (SemilinearAut.ofAlgAut σ)⁻¹ := by
  rw [← map_inv]
  rfl

variable [HasPrincipalDivisors K Z]

theorem mem_fiberAlong_comp_algEquiv_iff (α : F₁ →ₐ[K] Z) (hα : α.toRingHom.IsIntegral) (σ : Z ≃ₐ[K] Z)
    (h : (σ.toAlgHom.comp α).toRingHom.IsIntegral) (w₀ : Place K F₁) (W : Place K Z) :
    W ∈ Place.fiberAlong (σ.toAlgHom.comp α) h w₀ ↔ (SemilinearAut.ofAlgAut σ)⁻¹ • W ∈ Place.fiberAlong α hα w₀ := by
  rw [Place.mem_fiberAlong, Place.mem_fiberAlong, restrictAlong_comp α σ.toAlgHom hα (isIntegral_algEquiv σ) h,
    Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul σ (isIntegral_algEquiv σ), ofAlgAut_symm_eq_inv]

theorem pullbackAlong_comp_algEquiv_single (α : F₁ →ₐ[K] Z) (hα : α.toRingHom.IsIntegral) (σ : Z ≃ₐ[K] Z)
    (h : (σ.toAlgHom.comp α).toRingHom.IsIntegral) (w₀ : Place K F₁) (n : ℤ) :
    Divisor.pullbackAlong (σ.toAlgHom.comp α) h (Finsupp.single w₀ n) =
      ∑ W ∈ Place.fiberAlong α hα w₀,
        Finsupp.single (SemilinearAut.ofAlgAut σ • W) (n * (W.ramificationIndexAlong α : ℤ)) := by
  rw [Divisor.pullbackAlong_single]
  symm
  refine Finset.sum_bij' (fun W _ => SemilinearAut.ofAlgAut σ • W) (fun W _ => (SemilinearAut.ofAlgAut σ)⁻¹ • W)
    ?_ ?_ ?_ ?_ ?_
  · intro W hW
    rw [mem_fiberAlong_comp_algEquiv_iff α hα σ h w₀, inv_smul_smul]
    exact hW
  · intro W hW
    exact (mem_fiberAlong_comp_algEquiv_iff α hα σ h w₀ W).1 hW
  · intro W hW
    exact inv_smul_smul _ _
  · intro W hW
    exact smul_inv_smul _ _
  · intro W hW

    congr 2
    have := Place.ramificationIndexAlong_smul (σ.toAlgHom.comp α) α σ AlgEquiv.refl (fun x => rfl) W
    rw [← ofAlgAut_smul_place] at this
    exact_mod_cast this.symm

end Generic

section Modular

p2m_open "ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_ptsSp_degPull_one_eq_mk_of_forall_apply_eq_zero_of_pullbackAlong.ModularCurve"
open scoped MatrixGroups

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)

theorem betaH_eq_comp
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαq : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβq : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) :
    βH = θ.toAlgHom.comp αH := by
  apply AlgHom.ext
  intro u
  apply Subtype.ext
  exact (hβq u).trans (hθ (αH u) u (hαq u)).symm

theorem pullbackAlong_betaH_single
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (hβ : βH = θ.toAlgHom.comp αH) (w₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (n : ℤ) :
    Divisor.pullbackAlong βH hβint (Finsupp.single w₀ n) =
      ∑ W ∈ Place.fiberAlong αH hαint w₀,
        Finsupp.single (SemilinearAut.ofAlgAut θ • W) (n * (W.ramificationIndexAlong αH : ℤ)) := by
  subst hβ
  exact pullbackAlong_comp_algEquiv_single αH hαint θ hβint w₀ n

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem sum_ramificationIndexAlong_alphaH_eq (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (hαint : αH.toRingHom.IsIntegral)
    (hαq : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβq : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    [IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)] [IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))]
    (w₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    ∑ W ∈ Place.fiberAlong αH hαint w₀, (W.ramificationIndexAlong αH : ℤ) = p + 1 := by
  have hfr := (ModularCurve.finrankAlong_eq_add_one_and_finrankAlong_eq_add_one_of_coe_eq_qExpand
    p M H hpM hpM2 hHp θ hθ αH βH hαq hβq).1
  have hfin : FiniteAlong (AlgebraicClosure ℚ) αH := by
    letI := algebraAlong αH
    have hpos : 0 < Module.finrank ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := by
      have hh : Module.finrank ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) = p + 1 := hfr
      omega
    exact Module.finite_of_finrank_pos hpos
  have hsep := separableAlong_of_charZero αH hαint
  have h := Place.sum_ramificationIndexAlong_mul_inertiaDegAlong αH hαint hfin hsep w₀
  rw [hfr] at h

  have hf : ∀ W ∈ Place.fiberAlong αH hαint w₀,
      (W.ramificationIndexAlong αH : ℤ) * (W.inertiaDegAlong αH hαint : ℤ) = (W.ramificationIndexAlong αH : ℤ) := by
    intro W _
    have hdeg := IsCurveOver.deg_eq_one_of_isAlgClosed (K := AlgebraicClosure ℚ) W
    have hdeg₀ := IsCurveOver.deg_eq_one_of_isAlgClosed (K := AlgebraicClosure ℚ) (W.restrictAlong αH hαint)
    have hmul : (W.restrictAlong αH hαint).deg * W.inertiaDegAlong αH hαint = W.deg := by
      letI := algebraAlong αH
      haveI := isScalarTower_along αH
      haveI := isIntegral_along αH hαint
      exact W.deg_restrict_mul_inertiaDeg
    rw [hdeg, hdeg₀, one_mul] at hmul
    rw [hmul, Nat.cast_one, mul_one]
  rw [Finset.sum_congr rfl hf] at h
  exact_mod_cast h

end Modular

section Geometric

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_ptsSp_degPull_one_eq_mk_of_forall_apply_eq_zero_of_pullbackAlong.ModularCurve ModularCurve.XHDRLevel"
open scoped MatrixGroups

theorem restrictAlong_pointEquivPlace_eq_iff
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (αH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral)
    (hαq : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (y z : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) :
    (𝔛.Meta.pointEquivPlace y).restrictAlong αH hαint = (𝔛.Meta.pointEquivPlace z).restrictAlong αH hαint ↔
      y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 = z.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 := by
  obtain ⟨αH', βH', hα'int, -, hα'q, -, Meta₀, eeta₀, hiso, heeta₀, hMπ, -, -, -⟩ :=
    ModularCurve.XHDRModelAtP.exists_degeneracyEmb_curveModel_iso_genericFibre_restrictAlong_chartPin_of_atkinLehner_generic
      p M H hpM hpM2 hHp hj 𝔛 θ hθ hwgen
  have hαα : αH = αH' := AlgHom.ext fun u => Subtype.ext ((hαq u).trans (hα'q u).symm)
  subst hαα
  haveI := hiso

  have hT : ∀ x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _},
      (x.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1) ≫ toBase p (XHDRLevel.ΓN p M H hpM) hj =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    intro x
    simp only [Category.assoc, Category.id_comp]
    rw [𝔛.π.2, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, x.2, Category.id_comp]
  have hinvB : inv eeta₀ ≫ Meta₀.toBase = pullback.snd _ _ := by
    rw [← heeta₀, IsIso.inv_hom_id_assoc]
  let push : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} →
      {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _} := fun x =>
    ⟨pullback.lift _ _ (hT x) ≫ inv eeta₀, by rw [Category.assoc, hinvB, pullback.lift_snd]⟩
  have hpush : ∀ x, (push x).1 ≫ eeta₀ ≫ pullback.fst _ _ = x.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 := fun x => by
    show (pullback.lift _ _ (hT x) ≫ inv eeta₀) ≫ eeta₀ ≫ pullback.fst _ _ = _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  have hread : ∀ x, (𝔛.Meta.pointEquivPlace x).restrictAlong αH hαint = Meta₀.pointEquivPlace (push x) := fun x =>
    (hMπ x (push x) (hpush x)).symm
  rw [hread, hread]
  constructor
  · intro h
    have h' : push y = push z := Meta₀.pointEquivPlace.injective h
    have h'' := congrArg (fun q => q.1 ≫ eeta₀ ≫ pullback.fst _ _) h'
    simp only [hpush] at h''
    exact h''
  · intro h
    congr 1
    apply Subtype.ext
    show pullback.lift _ _ (hT y) ≫ inv eeta₀ = pullback.lift _ _ (hT z) ≫ inv eeta₀
    congr 1
    apply pullback.hom_ext
    · rw [pullback.lift_fst, pullback.lift_fst]
      exact h
    · rw [pullback.lift_snd, pullback.lift_snd]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem pullback_pushforward_single_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (hαq : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβq : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (z : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = z.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP₀ : ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P ≠ 𝔛.placeOn0 A hA ρ hρ n) :
    ∃ (others : Finset {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (e : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} → ℕ),
      z ∉ others ∧
      (∀ y' ∈ others, y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 = z.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 ∧ y' ≠ z) ∧
      (∑ y' ∈ others, e y' = p) ∧
      Divisor.pullbackAlong βH hβint (Divisor.pushforwardAlong αH hαint (Finsupp.single (𝔛.Meta.pointEquivPlace z) 1)) =
        Finsupp.single (SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace z) 1 +
          ∑ y' ∈ others, Finsupp.single (SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y') (e y' : ℤ) := by
  classical
  obtain ⟨αH', βH', hα'int, -, hα'q, -, Meta₀, eeta₀, hiso, heeta₀, -, -, hne₀, hpin₀⟩ :=
    ModularCurve.XHDRModelAtP.exists_degeneracyEmb_curveModel_iso_genericFibre_restrictAlong_chartPin_of_atkinLehner_generic
      p M H hpM hpM2 hHp hj 𝔛 θ hθ hwgen
  have hαα : αH = αH' := AlgHom.ext fun u => Subtype.ext ((hαq u).trans (hα'q u).symm)
  subst hαα
  haveI := hiso

  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      𝔛.Meta.toBase 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap
  haveI hCO₀ : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      Meta₀.toBase Meta₀.ffEquiv Meta₀.ffEquiv_algebraMap
  have hβ := betaH_eq_comp p M H hpM θ hθ αH βH hαq hβq
  set w₀ := (𝔛.Meta.pointEquivPlace z).restrictAlong αH hαint with hw₀

  have hfW : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.inertiaDegAlong αH hαint = 1 := by
    intro W
    have hdeg := IsCurveOver.deg_eq_one_of_isAlgClosed (K := AlgebraicClosure ℚ) W
    have hdeg₀ := IsCurveOver.deg_eq_one_of_isAlgClosed (K := AlgebraicClosure ℚ) (W.restrictAlong αH hαint)
    have hmul : (W.restrictAlong αH hαint).deg * W.inertiaDegAlong αH hαint = W.deg := by
      letI := algebraAlong αH
      haveI := isScalarTower_along αH
      haveI := isIntegral_along αH hαint
      exact W.deg_restrict_mul_inertiaDeg
    rwa [hdeg, hdeg₀, one_mul] at hmul
  have hpf : Divisor.pushforwardAlong αH hαint (Finsupp.single (𝔛.Meta.pointEquivPlace z) 1) = Finsupp.single w₀ 1 := by
    rw [Divisor.pushforwardAlong_single, hfW, Nat.cast_one, mul_one]

  obtain ⟨V, hV, hVunr⟩ :=
    ModularCurve.XHDRModelAtP.exists_opens_formallyUnramified_pi_of_comp_zero_of_forall_ne_placeOn0
      p M H hpM hj 𝔛 A hA ρ hρ z u hu uκ huκ₁ huκ₂ P hP hP₀
  have hzV : (z.1 ≫ 𝔛.eeta ≫ pullback.fst _ _).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ V := by
    apply hV
    rw [← hu, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have he1 := ModularCurve.XHDRModelAtP.ramificationIndexAlong_degeneracyEmb_pointEquivPlace_eq_one_of_formallyUnramified
    p M H hpM hj 𝔛 αH hαq hαint Meta₀ eeta₀ heeta₀ hne₀ hpin₀ z V hzV hVunr

  have hcount := sum_ramificationIndexAlong_alphaH_eq p M H hpM hpM2 hHp θ hθ αH βH hαint hαq hβq w₀
  have hzmem : 𝔛.Meta.pointEquivPlace z ∈ Place.fiberAlong αH hαint w₀ := Place.mem_fiberAlong.2 rfl
  refine ⟨((Place.fiberAlong αH hαint w₀).erase (𝔛.Meta.pointEquivPlace z)).image 𝔛.Meta.pointEquivPlace.symm,
    fun y' => (𝔛.Meta.pointEquivPlace y').ramificationIndexAlong αH, ?_, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨W, hW, hWz⟩ := Finset.mem_image.1 h
    rw [Equiv.symm_apply_eq] at hWz
    exact (Finset.mem_erase.1 hW).1 hWz
  · intro y' hy'
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hy'
    obtain ⟨hWz, hWmem⟩ := Finset.mem_erase.1 hW
    refine ⟨?_, fun h => hWz (by rw [← h, Equiv.apply_symm_apply])⟩
    rw [← restrictAlong_pointEquivPlace_eq_iff p M H hpM hpM2 hHp hj 𝔛 θ hθ hwgen αH hαint hαq, Equiv.apply_symm_apply]
    exact Place.mem_fiberAlong.1 hWmem
  ·
    rw [Finset.sum_image fun a _ b _ h => 𝔛.Meta.pointEquivPlace.symm.injective h]
    simp only [Equiv.apply_symm_apply]
    have hsplit := Finset.add_sum_erase _ (fun W => W.ramificationIndexAlong αH) hzmem
    beta_reduce at hsplit
    rw [he1] at hsplit
    have hnat : ∑ W ∈ Place.fiberAlong αH hαint w₀, W.ramificationIndexAlong αH = p + 1 := by
      have := hcount
      push_cast [← Nat.cast_sum] at this
      exact_mod_cast this
    omega
  · rw [hpf, pullbackAlong_betaH_single p M H hpM θ αH βH hαint hβint hβ w₀ 1, ← Finset.add_sum_erase _ _ hzmem, he1,
      Finset.sum_image fun a _ b _ h => 𝔛.Meta.pointEquivPlace.symm.injective h]
    simp only [Equiv.apply_symm_apply, one_mul, Nat.cast_one]

end Geometric

end Pull1FF

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "SemilinearAut SemilinearAut.ofAlgAut SemilinearAut.smul_single SemilinearAut.divisor_smul_apply SemilinearAut.smul_mem_degZero SemilinearAut.degZeroSMulHom SemilinearAut.coe_degZeroSMulHom Place Place.ext Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_zero algebraAlong isScalarTower_along isIntegral_along FiniteAlong Divisor.pullbackAlong Divisor.pushforwardAlong Divisor.pushforwardAlong_mem_degZero Divisor.pushforwardAlong_single Place.fiberAlong Place.mem_fiberAlong Divisor.pullbackAlong_single GluingData GluingData.admissible GluingData.mem_admissible GluedPic0 GluedPic0.mk GluedPic0.toPic0Pair GluedPic0.toPic0Pair_mk IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one Place.deg_eq_one_iff_surjective_algebraMap_residueField Place.ramificationIndexAlong_smul Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul Place.sum_ramificationIndexAlong_mul_inertiaDegAlong separableAlong_of_charZero" namespace SemilinearAut p2m_export "AlgebraicCurve.SemilinearAut" "ofAlgAut smul_single divisor_smul_apply smul_mem_degZero degZeroSMulHom coe_degZeroSMulHom" end AlgebraicCurve.SemilinearAut
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.SemilinearAut" in

theorem AlgebraicCurve.SemilinearAut.hsup_coe_degZeroSMulHom_single_sub_single
    {K F : Type*} [Field K] [Field F] [Algebra K F] (g : SemilinearAut K F)
    (D : Divisor.degZero (K := K) (F := F)) (P Q P' Q' : Place K F) (hP : P' = g • P) (hQ : Q' = g • Q)
    (hD : (D : Divisor K F) = Finsupp.single P 1 - Finsupp.single Q 1) :
    ((SemilinearAut.degZeroSMulHom g D : Divisor.degZero (K := K) (F := F)) : Divisor K F) =
      Finsupp.single P' 1 - Finsupp.single Q' 1 := by
  subst hP hQ
  rw [SemilinearAut.coe_degZeroSMulHom, hD, smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single]

namespace ModularCurve p2m_export "ModularCurve" "XHDRLevel.ΓN XHDRModelAtP ssPlacesQExp diamondActionModL infSubgroup mem_ssNodePairsQExp_iff xHFunctionFieldBar JH qExpFunctionFieldC qExpand qExpFrobeniusPlaceModL qExpFrobeniusPushforwardModL jqModC genOpH JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP XHDRModelAtP.smul_frob_mem_ssPlacesQExp_and_frob_smul_frob_eq_of_mem_ssPlacesQExp XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus finrankAlong_eq_add_one_and_finrankAlong_eq_add_one_of_coe_eq_qExpand XHDRModelAtP.exists_degeneracyEmb_curveModel_iso_genericFibre_restrictAlong_chartPin_of_atkinLehner_generic XHDRModelAtP.ramificationIndexAlong_degeneracyEmb_pointEquivPlace_eq_one_of_formallyUnramified XHDRModelAtP.exists_opens_formallyUnramified_pi_of_comp_zero_of_forall_ne_placeOn0 XHDRModelAtP.exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq XHDRModelAtP.exists_schemeHomOver_comp_one_frob_placeOfPoint_eq_of_comp_pi_eq_of_ne" namespace JHNeronObjectAtP p2m_export "ModularCurve.JHNeronObjectAtP" "ΓN Fbar LevelData ptsSp comm abqFibre_ptsSp ssFinset degeneracyHom_mul mk pts surjective g pts_add degeneracyHom_pts separated degeneracyHom_special degPts degeneracyHom G smooth ptsSp_add mem_ssFinset_iff L" end ModularCurve.JHNeronObjectAtP
p2m_open_scoped "ModularCurve ModularCurve.JHNeronObjectAtP" in
set_option maxHeartbeats 12800000 in

theorem ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_pts_sum_zsmul_ptsSp_symm_eq_sum
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    {ι : Type*} (t : Finset ι) (zz : ι → JH M H) (n : ι → ℤ) (ss : ι → SchemeHomOver Λ.σA O.g)
    (hss : ∀ k ∈ t, (O.pts (zz k)).1 = barPt A ≫ (ss k).1) :
    ∃ S : SchemeHomOver Λ.σA O.g,
      (O.pts (∑ k ∈ t, n k • zz k)).1 = barPt A ≫ S.1 ∧
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ S) =
        ∑ k ∈ t, n k • O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (ss k)) := by
  classical

  letI Gσ : CommGroup (SchemeHomOver Λ.σA O.g) := { O.L.pointGroup Λ.σA with mul_comm := O.comm Λ.σA }
  letI Gg : CommGroup (SchemeHomOver (genPt p) O.g) := { O.L.pointGroup (genPt p) with mul_comm := O.comm (genPt p) }
  letI Gr : CommGroup (SchemeHomOver (resPt A ≫ Λ.σA) O.g) :=
    { O.L.pointGroup (resPt A ≫ Λ.σA) with mul_comm := O.comm (resPt A ≫ Λ.σA) }

  let gen : SchemeHomOver Λ.σA O.g →* SchemeHomOver (genPt p) O.g :=
    MonoidHom.mk' (fun X => GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA X)
      (fun X Y => O.L.mul_natural Λ.σA (genPt p) (barPt A) Λ.hσA X Y)

  let φ : Multiplicative (JH M H) →* SchemeHomOver (genPt p) O.g :=
    MonoidHom.mk' (fun x => O.pts x.toAdd) (fun x y => O.pts_add x.toAdd y.toAdd)

  have R1 : ∀ U V : SchemeHomOver (resPt A ≫ Λ.σA) O.g,
      O.ptsSp.symm (O.L.mul _ U V) = O.ptsSp.symm U + O.ptsSp.symm V := by
    intro U V
    apply O.ptsSp.injective
    rw [Equiv.apply_symm_apply, O.ptsSp_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    apply Subtype.ext
    simp only [toFibrePt, ofFibrePt, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase]
    have hn := congrArg Subtype.val (O.L.mul_natural (resPt A ≫ Λ.σA) (𝟙 _ ≫ resPt A ≫ Λ.σA) (𝟙 _) rfl U V)
    rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp] at hn
    rw [hn]
    have hU : GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl U = overId U := Subtype.ext (Category.id_comp _)
    have hV : GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl V = overId V := Subtype.ext (Category.id_comp _)
    rw [hU, hV]
  let sp : Additive (SchemeHomOver Λ.σA O.g) →+ GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset :=
    AddMonoidHom.mk' (fun X => O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ X.toMul))
      (fun X' Y' => by
        obtain ⟨X, rfl⟩ := Additive.ofMul.surjective X'
        obtain ⟨Y, rfl⟩ := Additive.ofMul.surjective Y'
        show O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (O.L.mul Λ.σA X Y)) =
          O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ X) +
            O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ Y)
        have hn := O.L.mul_natural Λ.σA (resPt A ≫ Λ.σA) (resPt A) rfl X Y
        have e1 : ∀ W : SchemeHomOver Λ.σA O.g, GoodReductionJacobian.schemeHomOverComp (resPt A) rfl W =
            NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ W := fun W => Subtype.ext rfl
        rw [e1, e1, e1] at hn
        rw [hn, R1])

  refine ⟨∏ k ∈ t, ss k ^ n k, ?_, ?_⟩
  ·
    have hgen : ∀ k ∈ t, gen (ss k) = φ (Multiplicative.ofAdd (zz k)) := fun k hk =>
      Subtype.ext (hss k hk).symm
    have h1 : gen (∏ k ∈ t, ss k ^ n k) = φ (Multiplicative.ofAdd (∑ k ∈ t, n k • zz k)) := by
      rw [map_prod, ofAdd_sum, map_prod]
      refine Finset.prod_congr rfl fun k hk => ?_
      rw [map_zpow, hgen k hk, ofAdd_zsmul, map_zpow]
    have h2 := congrArg Subtype.val h1
    exact h2.symm
  ·
    have h1 : sp (Additive.ofMul (∏ k ∈ t, ss k ^ n k)) = ∑ k ∈ t, n k • sp (Additive.ofMul (ss k)) := by
      rw [ofMul_prod, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ofMul_zpow, map_zsmul]
    exact h1

p2m_open_scoped "ModularCurve ModularCurve.JHNeronObjectAtP" in
set_option maxHeartbeats 6400000 in

theorem ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_pts_add_sum_zsmul_ptsSp_symm_eq_add_sum
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (S₀ : SchemeHomOver Λ.σA O.g) (z₀ : JH M H) (hS₀ : (O.pts z₀).1 = barPt A ≫ S₀.1)
    {ι : Type*} (t : Finset ι) (zz : ι → JH M H) (n : ι → ℤ) (ss : ι → SchemeHomOver Λ.σA O.g)
    (hss : ∀ k ∈ t, (O.pts (zz k)).1 = barPt A ≫ (ss k).1) :
    ∃ S : SchemeHomOver Λ.σA O.g,
      (O.pts (z₀ + ∑ k ∈ t, n k • zz k)).1 = barPt A ≫ S.1 ∧
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ S) =
        O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ S₀) +
          ∑ k ∈ t, n k • O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (ss k)) := by
  classical
  obtain ⟨S, h1, h2⟩ := ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_pts_sum_zsmul_ptsSp_symm_eq_sum p M H hpM A hA Λ O
    (Finset.insertNone t) (fun o => o.elim z₀ zz) (fun o => o.elim 1 n) (fun o => o.elim S₀ ss)
    (by
      intro o ho
      rcases o with _ | k
      · exact hS₀
      · exact hss k (Finset.some_mem_insertNone.mp ho))
  refine ⟨S, ?_, ?_⟩
  · rw [Finset.sum_insertNone] at h1
    simpa only [Option.elim, one_zsmul] using h1
  · rw [Finset.sum_insertNone] at h2
    simpa only [Option.elim, one_zsmul] using h2

theorem pull1sp_sum_zsmul_const {G : Type*} [AddCommGroup G] {ι : Type*} (s : Finset ι) (n : ι → ℤ) (x : G) :
    ∑ i ∈ s, n i • x = (∑ i ∈ s, n i) • x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, add_zsmul]

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "SemilinearAut SemilinearAut.ofAlgAut SemilinearAut.smul_single SemilinearAut.divisor_smul_apply SemilinearAut.smul_mem_degZero SemilinearAut.degZeroSMulHom SemilinearAut.coe_degZeroSMulHom Place Place.ext Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_zero algebraAlong isScalarTower_along isIntegral_along FiniteAlong Divisor.pullbackAlong Divisor.pushforwardAlong Divisor.pushforwardAlong_mem_degZero Divisor.pushforwardAlong_single Place.fiberAlong Place.mem_fiberAlong Divisor.pullbackAlong_single GluingData GluingData.admissible GluingData.mem_admissible GluedPic0 GluedPic0.mk GluedPic0.toPic0Pair GluedPic0.toPic0Pair_mk IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one Place.deg_eq_one_iff_surjective_algebraMap_residueField Place.ramificationIndexAlong_smul Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul Place.sum_ramificationIndexAlong_mul_inertiaDegAlong separableAlong_of_charZero" namespace Divisor p2m_export "AlgebraicCurve.Divisor" "degree degree_single degZero mem_degZero smul_single smul_apply smul_mem_degZero pullbackAlong pushforwardAlong pushforwardAlong_mem_degZero pushforwardAlong_single pullbackAlong_single pushforward pullback" end AlgebraicCurve.Divisor
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Divisor" in

theorem AlgebraicCurve.Divisor.hsup_single_sub_single_mem_degZero_and_apply
    {K F : Type*} [Field K] [Field F] [Algebra K F] (hdeg : ∀ v : Place K F, v.deg = 1) (P Q : Place K F) :
    (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor K F) ∈ Divisor.degZero (K := K) (F := F) ∧
      ∀ w : Place K F, P ≠ w → Q ≠ w → (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor K F) w = 0 := by
  refine ⟨?_, fun w hP hQ => ?_⟩
  · rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg, sub_self]
  · classical
    rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg hP, if_neg hQ, sub_zero]

p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Divisor" in

theorem AlgebraicCurve.Divisor.pull1sp_degree_eq_sum {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hdeg : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) : Divisor.degree D = D.sum fun _ n => n := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v _ => ?_
  show D v * ((v.deg : ℕ) : ℤ) = D v
  rw [hdeg v, Nat.cast_one, mul_one]

p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Divisor" in

theorem AlgebraicCurve.Divisor.pull1sp_degree_mapDomain {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hdeg : ∀ v : Place K F, v.deg = 1) (f : Place K F → Place K F) (D : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain f D) = Divisor.degree D := by
  rw [AlgebraicCurve.Divisor.pull1sp_degree_eq_sum hdeg, AlgebraicCurve.Divisor.pull1sp_degree_eq_sum hdeg]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Divisor" in

theorem AlgebraicCurve.Divisor.pull1sp_addMonoidHom_eq_of_eqOn_single_sub_single
    {K F : Type*} [Field K] [Field F] [Algebra K F] (hdeg : ∀ v : Place K F, v.deg = 1)
    (T : Set (Place K F)) (AV : AddSubgroup (Divisor K F))
    (hAV₀ : ∀ D ∈ AV, D ∈ Divisor.degZero (K := K) (F := F))
    (hAVT : ∀ D ∈ AV, ∀ v ∈ T, D v = 0)
    (hdiff : ∀ P Q : Place K F, P ∉ T → Q ∉ T → (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor K F) ∈ AV)
    {G : Type*} [AddCommGroup G] (L R : ↥AV →+ G)
    (h : ∀ (P Q : Place K F) (hP : P ∉ T) (hQ : Q ∉ T), L ⟨_, hdiff P Q hP hQ⟩ = R ⟨_, hdiff P Q hP hQ⟩) :
    L = R := by
  classical

  suffices key : ∀ (n : ℕ) (D : ↥AV), (D : Divisor K F).support.card ≤ n → L D = R D by
    ext D; exact key _ D le_rfl
  intro n
  induction n with
  | zero =>
    intro D hD
    have h0 : (D : Divisor K F) = 0 := Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hD))
    have hD0 : D = 0 := Subtype.ext h0
    rw [hD0, map_zero, map_zero]
  | succ n ih =>
    intro D hD
    by_cases hz : (D : Divisor K F) = 0
    · have hD0 : D = 0 := Subtype.ext hz
      rw [hD0, map_zero, map_zero]

    obtain ⟨Q₀, hQ₀⟩ := Finsupp.support_nonempty_iff.mpr hz

    have hQ₁ : ∃ Q₁ ∈ (D : Divisor K F).support, Q₁ ≠ Q₀ := by
      by_contra hcon
      push_neg at hcon
      have hsupp : (D : Divisor K F).support ⊆ {Q₀} := fun v hv => Finset.mem_singleton.mpr (hcon v hv)
      have hDeq : (D : Divisor K F) = Finsupp.single Q₀ ((D : Divisor K F) Q₀) := Finsupp.eq_single_iff.mpr ⟨hsupp, rfl⟩
      have hdeg0 := hAV₀ _ D.2
      rw [Divisor.mem_degZero, hDeq, Divisor.degree_single, hdeg Q₀, Nat.cast_one, mul_one] at hdeg0
      exact (Finsupp.mem_support_iff.mp hQ₀) hdeg0
    obtain ⟨Q₁, hQ₁, hne⟩ := hQ₁
    have hT₀ : Q₀ ∉ T := fun hT => (Finsupp.mem_support_iff.mp hQ₀) (hAVT _ D.2 _ hT)
    have hT₁ : Q₁ ∉ T := fun hT => (Finsupp.mem_support_iff.mp hQ₁) (hAVT _ D.2 _ hT)

    let c : ℤ := (D : Divisor K F) Q₀
    let E : ↥AV := ⟨_, hdiff Q₀ Q₁ hT₀ hT₁⟩
    have hsplit : D = (D - c • E) + c • E := by abel
    have hcard : ((D - c • E : ↥AV) : Divisor K F).support.card ≤ n := by
      have hsub : ((D - c • E : ↥AV) : Divisor K F).support ⊆ (D : Divisor K F).support.erase Q₀ := by
        intro v hv
        rw [Finset.mem_erase]
        rw [Finsupp.mem_support_iff] at hv
        have hv' : (D : Divisor K F) v - c * (Finsupp.single Q₀ (1 : ℤ) v - Finsupp.single Q₁ (1 : ℤ) v) ≠ 0 := by
          simpa [E, c, Finsupp.single_apply] using hv
        constructor
        · intro hvQ
          rw [hvQ] at hv'
          apply hv'
          rw [Finsupp.single_apply, Finsupp.single_apply, if_pos rfl, if_neg hne]
          show (D : Divisor K F) Q₀ - (D : Divisor K F) Q₀ * (1 - 0) = 0
          ring
        · rw [Finsupp.mem_support_iff]
          intro hDv
          apply hv'
          rw [hDv, zero_sub, neg_eq_zero]
          have hv0 : ¬ Q₀ = v := fun h => by rw [← h] at hDv; exact (Finsupp.mem_support_iff.mp hQ₀) hDv
          have hv1 : ¬ Q₁ = v := fun h => by rw [← h] at hDv; exact (Finsupp.mem_support_iff.mp hQ₁) hDv
          rw [Finsupp.single_apply, Finsupp.single_apply, if_neg hv0, if_neg hv1, sub_self, mul_zero]
      calc ((D - c • E : ↥AV) : Divisor K F).support.card ≤ ((D : Divisor K F).support.erase Q₀).card := Finset.card_le_card hsub
        _ = (D : Divisor K F).support.card - 1 := Finset.card_erase_of_mem hQ₀
        _ ≤ n := by omega
    rw [hsplit, map_add, map_add, map_zsmul, map_zsmul, ih _ hcard, h Q₀ Q₁ hT₀ hT₁]

set_option synthInstance.maxHeartbeats 6400000 in
set_option maxHeartbeats 64000000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt A ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (S : Set ℕ)
    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))

    (σ : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hσ : ∀ n : ↥O.ssFinset, (σ n).1.2 = n.1.1)

    (Φ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃ Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hΦ : ∀ v, Φ v = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v)
    (hFdiv : ∀ (D D' : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A))),
      (D' : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.mapDomain Φ (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) →
      F (Pic0.mk D) = Pic0.mk D')

    (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgenθ : wgen = SemilinearAut.ofAlgAut θ)
    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (hαq : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβq : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hpull1div : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = Divisor.pullbackAlong βH hβint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
      αpull 1 (Pic0.mk Dw) = Pic0.mk Dv)
    (hdeg0div : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
      O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    :
    ∀ (D : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (x₁ : ↥(GluingData.admissible O.ssFinset)),
      (∀ s ∈ O.ssFinset, (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) s.1 = 0 ∧
        (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (Φ s.1) = 0) →
      (x₁ : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (p : ℤ) • Finsupp.mapDomain Φ.symm (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) →
      (x₁ : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
        SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb)) • (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) →
      (x₁ : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0 →
      O.ptsSp.symm (schemeHomOverComp (Λ.ptsSp (Pic0.mk D)) (degPull 1)) = GluedPic0.mk O.ssFinset x₁ := by

  intro D x₁ hD hx₁1 hx₁2 hx₁3

  haveI hCO : IsCurveOver (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      (𝔛.Mfib A hA ρ hρ).toBase (𝔛.Mfib A hA ρ hρ).ffEquiv (𝔛.Mfib A hA ρ hρ).ffEquiv_algebraMap
  have hrat : ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), Function.Surjective (algebraMap (ResidueField ↥A) v.ResidueField) := by
    intro v
    haveI := IsCurveOver.finiteResidue (K := (ResidueField ↥A)) (F := (Fbar p M H hpM (ResidueField ↥A))) v
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  have hdegF : ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), v.deg = 1 := fun v =>
    (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField v).mpr (hrat v)
  haveI hCOgen : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      𝔛.Meta.toBase 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap
  have hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), v.deg = 1 := by
    intro v
    haveI := IsCurveOver.finiteResidue (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) v
    exact (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField v).mpr
      IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  have hinv : ∀ s ∈ O.ssFinset, (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb)))⁻¹ • s.2 = Φ s.1 := by
    intro s hs
    have hs' := (O.mem_ssFinset_iff s).mp hs
    rw [mem_ssNodePairsQExp_iff] at hs'
    obtain ⟨hy, hs1⟩ := hs'
    have hs1ss : s.1 ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p := by
      have hm := ((O.mem_ssFinset_iff _).mp (σ ⟨s, hs⟩).2)
      rw [mem_ssNodePairsQExp_iff] at hm
      rw [← hσ ⟨s, hs⟩]
      exact hm.1
    obtain ⟨-, h2⟩ := ModularCurve.XHDRModelAtP.smul_frob_mem_ssPlacesQExp_and_frob_smul_frob_eq_of_mem_ssPlacesQExp
      p M H hpM hj 𝔛 A hA ρ hρ hdia0 pb hpb s.1 hs1ss
    rw [← hΦ, ← hΦ] at h2
    rw [inv_smul_eq_iff]
    apply Φ.injective
    rw [h2, hs1, hΦ]

  let e : SchemeHomOver O.g O.g := NeronModelInfra.schemeHomOverComp (O.degeneracyHom 0) (degPull 1)
  have he_mul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp (O.L.mul s x y) e =
        O.L.mul s (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y e) := by
    intro T s x y
    show NeronModelInfra.schemeHomOverComp (O.L.mul s x y)
        (NeronModelInfra.schemeHomOverComp (O.degeneracyHom 0) (degPull 1)) = _
    rw [← NeronModelInfra.schemeHomOverComp_assoc, O.degeneracyHom_mul, hpull_mul,
      NeronModelInfra.schemeHomOverComp_assoc, NeronModelInfra.schemeHomOverComp_assoc]
  have key : ∀ X Y : SchemeHomOver (resPt A ≫ Λ.σA) O.g,
      NeronModelInfra.schemeHomOverComp
          (ofFibrePt ((O.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt X) (toFibrePt Y))) e =
        ofFibrePt ((O.L.baseChange (resPt A ≫ Λ.σA)).mul _
          (toFibrePt (NeronModelInfra.schemeHomOverComp X e))
          (toFibrePt (NeronModelInfra.schemeHomOverComp Y e))) := by
    intro X Y
    apply Subtype.ext
    simp only [NeronModelInfra.schemeHomOverComp_coe, toFibrePt, ofFibrePt, RelativeGroupLaw.baseChange_mul,
      RelativeGroupLaw.baseChangePointToBase_ofBase]
    have h := congrArg Subtype.val (he_mul (𝟙 _ ≫ resPt A ≫ Λ.σA) (overId X) (overId Y))
    rw [NeronModelInfra.schemeHomOverComp_coe] at h
    rw [h]
    rfl
  let T₁ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset →+ GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset :=
    AddMonoidHom.mk' (fun ξ => O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ) e)) (by
      intro ξ η
      apply O.ptsSp.injective
      rw [Equiv.apply_symm_apply, O.ptsSp_add, O.ptsSp_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply, key])
  have hT₁ : ∀ ξ, T₁ ξ = O.ptsSp.symm (NeronModelInfra.schemeHomOverComp
      (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ) (O.degeneracyHom 0)) (degPull 1)) := fun ξ => by
    show O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ)
      (NeronModelInfra.schemeHomOverComp (O.degeneracyHom 0) (degPull 1))) = _
    rw [NeronModelInfra.schemeHomOverComp_assoc]

  have hadmD : ∀ D : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)), (∀ s ∈ O.ssFinset, (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) s.1 = 0 ∧ (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (Φ s.1) = 0) →
      (((D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (0 : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)) : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) ∈
        GluingData.admissible O.ssFinset := fun D hD =>
    ⟨D.2, zero_mem _, fun s hs => ⟨(hD s hs).1, rfl⟩⟩
  have hLHS : ∀ (D : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A))) (hD : ∀ s ∈ O.ssFinset, (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) s.1 = 0 ∧ (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (Φ s.1) = 0),
      O.ptsSp.symm (schemeHomOverComp (Λ.ptsSp (Pic0.mk D)) (degPull 1)) = T₁ (GluedPic0.mk O.ssFinset ⟨_, hadmD D hD⟩) := by
    intro D hD

    have hē : (((pb⁻¹ : (ZMod (M / p))ˣ) : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 := by
      rw [← hpb, Units.inv_mul]
    have h := (O.degeneracyHom_special pb⁻¹ hē (O.ptsSp (GluedPic0.mk O.ssFinset ⟨_, hadmD D hD⟩))).1
    rw [O.abqFibre_ptsSp _ 0, O.abqFibre_ptsSp _ 1, if_pos rfl, if_neg (by decide), ← hF, GluedPic0.toPic0Pair_mk] at h
    have h0 : (⟨(0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (GluingData.mem_admissible O.ssFinset |>.1 (hadmD D hD)).2.1⟩ : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A))) = 0 := Subtype.ext rfl
    have hx₁' : NeronModelInfra.schemeHomOverComp (O.ptsSp (GluedPic0.mk O.ssFinset ⟨_, hadmD D hD⟩)) (O.degeneracyHom 0) =
        Λ.ptsSp (Pic0.mk D) := by
      apply Λ.ptsSp.symm.injective
      rw [h, Equiv.symm_apply_apply]
      show Pic0.mk ⟨(D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), _⟩ + F (Pic0.mk ⟨(0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), _⟩) = Pic0.mk D
      rw [h0, Pic0.mk_zero, map_zero, add_zero]
    rw [hT₁, hx₁']

  have hdegmap : ∀ D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), D ∈ Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)) → Finsupp.mapDomain Φ.symm D ∈ Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)) := by
    intro D hDm
    rw [Divisor.mem_degZero] at hDm ⊢
    rw [AlgebraicCurve.Divisor.pull1sp_degree_mapDomain hdegF, hDm]
  have hadmR : ∀ D : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)), (∀ s ∈ O.ssFinset, (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) s.1 = 0 ∧ (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (Φ s.1) = 0) →
      (((p : ℤ) • Finsupp.mapDomain Φ.symm (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),
        (0 : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)) : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) ∈ GluingData.admissible O.ssFinset := by
    intro D hD
    refine ⟨AddSubgroup.zsmul_mem _ (hdegmap _ D.2) _, SemilinearAut.smul_mem_degZero _ D.2, fun s hs => ⟨?_, ?_⟩⟩
    · show ((p : ℤ) • Finsupp.mapDomain Φ.symm (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) s.1 = 0
      rw [Finsupp.smul_apply, Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, (hD s hs).2, smul_zero]
    · show ((SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) s.2 = 0
      rw [SemilinearAut.divisor_smul_apply, hinv s hs]
      exact (hD s hs).2
  have hRHS : GluedPic0.mk O.ssFinset x₁ = GluedPic0.mk O.ssFinset ⟨_, hadmR D hD⟩ :=
    congrArg (GluedPic0.mk O.ssFinset) (Subtype.ext (Prod.ext hx₁1 (Prod.ext hx₁2 hx₁3)))

  let AV : AddSubgroup (Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) :=
    { carrier := {E | E ∈ Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)) ∧ ∀ s ∈ O.ssFinset, E s.1 = 0 ∧ E (Φ s.1) = 0}
      zero_mem' := ⟨zero_mem _, fun _ _ => ⟨rfl, rfl⟩⟩
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun s hs => by
        simp only [Finsupp.add_apply, (ha.2 s hs).1, (hb.2 s hs).1, (ha.2 s hs).2, (hb.2 s hs).2, add_zero, and_self]⟩
      neg_mem' := fun {a} ha => ⟨neg_mem ha.1, fun s hs => by
        simp only [Finsupp.neg_apply, (ha.2 s hs).1, (ha.2 s hs).2, neg_zero, and_self]⟩ }
  have hAVd : ∀ E : ↥AV, ∀ s ∈ O.ssFinset, ((⟨(E : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), E.2.1⟩ : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A))) : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) s.1 = 0 ∧
      ((⟨(E : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), E.2.1⟩ : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A))) : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (Φ s.1) = 0 := fun E => E.2.2
  let Lm : ↥AV →+ GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset :=
    AddMonoidHom.mk' (fun E => T₁ (GluedPic0.mk O.ssFinset ⟨_, hadmD ⟨(E : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), E.2.1⟩ (hAVd E)⟩)) (fun a b => by
      show T₁ (GluedPic0.mk O.ssFinset _) = T₁ (GluedPic0.mk O.ssFinset _) + T₁ (GluedPic0.mk O.ssFinset _)
      rw [← T₁.map_add, ← (GluedPic0.mk O.ssFinset).map_add]
      exact congrArg T₁ (congrArg (GluedPic0.mk O.ssFinset) (Subtype.ext
        (Prod.ext rfl (Prod.ext (add_zero _).symm (add_zero _).symm)))))
  let Rm : ↥AV →+ GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset :=
    AddMonoidHom.mk' (fun E => GluedPic0.mk O.ssFinset ⟨_, hadmR ⟨(E : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), E.2.1⟩ (hAVd E)⟩) (fun a b => by
      show GluedPic0.mk O.ssFinset _ = GluedPic0.mk O.ssFinset _ + GluedPic0.mk O.ssFinset _
      rw [← (GluedPic0.mk O.ssFinset).map_add]
      refine congrArg (GluedPic0.mk O.ssFinset) (Subtype.ext ?_)
      show (((p : ℤ) • Finsupp.mapDomain Φ.symm ((a : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) + (b : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))), (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((a : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) + (b : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))),
        (0 : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)) : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) = _
      rw [Finsupp.mapDomain_add, smul_add, smul_add]
      exact Prod.ext rfl (Prod.ext rfl (add_zero _).symm))

  have hGEN : ∀ (P Q : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
      (hP : ∀ s ∈ O.ssFinset, P ≠ s.1 ∧ P ≠ Φ s.1) (hQ : ∀ s ∈ O.ssFinset, Q ≠ s.1 ∧ Q ≠ Φ s.1)
      (hm : (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) ∈ AV),
      Lm ⟨_, hm⟩ = Rm ⟨_, hm⟩ := by
    intro P Q hP hQ hm

    obtain ⟨Pc, rfl⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.2 P
    obtain ⟨Qc, rfl⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.2 Q

    have hoff : ∀ (Rc : closedPoints (𝔛.Mfib A hA ρ hρ).C), (∀ s ∈ O.ssFinset, (𝔛.Mfib A hA ρ hρ).placeOfPoint Rc ≠ s.1 ∧ (𝔛.Mfib A hA ρ hρ).placeOfPoint Rc ≠ Φ s.1) →
        ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)), (𝔛.Mfib A hA ρ hρ).placeOfPoint Rc ≠ 𝔛.placeOn0 A hA ρ hρ n := by
      intro Rc hR n
      exact (hR _ ((O.mem_ssFinset_iff _).mpr (𝔛.nodePair_mem A hA ρ hρ n))).1

    have hsm : ∀ (Rc : closedPoints (𝔛.Mfib A hA ρ hρ).C), (∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint Rc ≠ 𝔛.placeOn0 A hA ρ hρ n) →
        (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
          (((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ 0).base Rc.1) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) := by
      intro Rc hR
      have h := (ModularCurve.XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter p M H hpM hpM2 hj 𝔛 A hA ρ hρ
        (((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ 0).base Rc.1)).mpr ?_
      · exact h
      rintro ⟨-, ⟨b, hb⟩⟩

      obtain ⟨n, hn1, hn2⟩ := Scheme.Pullback.exists_preimage_pullback ((𝔛.efib A hA ρ hρ).base Rc.1) b
        (by rw [← Scheme.Hom.comp_apply]; exact hb.symm)
      obtain ⟨hmem, hpl⟩ := (𝔛.node_pin A hA ρ hρ n).2
      apply hR n
      show _ = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.nodeEquiv A hA ρ hρ n : ↥(ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p)) : Place _ _)
      rw [← hpl]
      congr 1
      apply Subtype.ext
      show Rc.1 = (inv (𝔛.efib A hA ρ hρ)).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)
      rw [hn1, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
      rfl
    have hP0 := hoff Pc hP
    have hQ0 := hoff Qc hQ
    obtain ⟨z, u, hu, husm, uκ, huκ₁, huκ₂, hPz⟩ :=
      ModularCurve.XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
        p M H hpM hj 𝔛 A hA ρ hρ 0 Pc (hsm Pc hP0)
    obtain ⟨z', u', hu', husm', uκ', huκ'₁, huκ'₂, hQz⟩ :=
      ModularCurve.XHDRModelAtP.exists_schemeHomOver_range_subset_smoothLocus_of_mem_smoothLocus
        p M H hpM hj 𝔛 A hA ρ hρ 0 Qc (hsm Qc hQ0)

    have hDvmem : (Finsupp.single (𝔛.Meta.pointEquivPlace z) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace z') 1 :
        Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
      rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1, sub_self]
    obtain ⟨s, hs, hsx⟩ := hsp 0 z u hu husm uκ huκ₁ huκ₂ Pc hPz z' u' hu' husm' uκ' huκ'₁ huκ'₂ Qc hQz ⟨_, hDvmem⟩ rfl
      ⟨_, hadmD ⟨_, hm.1⟩ (hAVd ⟨_, hm⟩)⟩ (by rw [if_pos rfl]) (by rw [if_neg (by decide)]) rfl
    have hsx' : O.ptsSp (GluedPic0.mk O.ssFinset ⟨_, hadmD ⟨_, hm.1⟩ (hAVd ⟨_, hm⟩)⟩) =
        NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s := ((Equiv.symm_apply_eq _).mp hsx).symm
    have hLmZ : Lm ⟨_, hm⟩ = O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1))) := by
      show T₁ (GluedPic0.mk O.ssFinset _) = _
      rw [hT₁, hsx']
      exact congrArg O.ptsSp.symm ((congrArg (fun t => NeronModelInfra.schemeHomOverComp t (degPull 1))
        (NeronModelInfra.schemeHomOverComp_assoc _ _ _)).trans (NeronModelInfra.schemeHomOverComp_assoc _ _ _))
    have hZ : (O.pts (αpull 1 (O.degPts 0 (Pic0.mk ⟨_, hDvmem⟩)))).1 =
        barPt A ≫ (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1)).1 := by
      rw [hpull 1, O.degeneracyHom_pts 0, hs]
      simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]

    have hwgen' : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}), y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y := by
      intro y y' h
      rw [← hwgenθ]
      exact hwgen y y' h
    obtain ⟨oth, e, hzno, hoth, hsum, hFFz⟩ := Pull1FF.pullback_pushforward_single_eq p M H hpM hpM2 hHp hj 𝔛 θ hθ hwgen' αH βH
      hαint hβint hαq hβq A hA ρ hρ z u hu uκ huκ₁ huκ₂ Pc hPz hP0
    obtain ⟨oth', e', hzno', hoth', hsum', hFFz'⟩ := Pull1FF.pullback_pushforward_single_eq p M H hpM hpM2 hHp hj 𝔛 θ hθ hwgen' αH βH
      hαint hβint hαq hβq A hA ρ hρ z' u' hu' uκ' huκ'₁ huκ'₂ Qc hQz hQ0

    have hDw0 := AlgebraicCurve.Divisor.pushforwardAlong_mem_degZero αH hαint hDvmem
    have hdp0 := hdeg0div ⟨_, hDvmem⟩ ⟨_, hDw0⟩ rfl
    have hDv₁eq : AlgebraicCurve.Divisor.pullbackAlong βH hβint (AlgebraicCurve.Divisor.pushforwardAlong αH hαint
        (Finsupp.single (𝔛.Meta.pointEquivPlace z) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace z') 1 : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) =
        (Finsupp.single (SemilinearAut.ofAlgAut θ • (𝔛.Meta.pointEquivPlace z)) 1 +
            ∑ y' ∈ oth, Finsupp.single (SemilinearAut.ofAlgAut θ • (𝔛.Meta.pointEquivPlace y')) (e y' : ℤ)) -
          (Finsupp.single (SemilinearAut.ofAlgAut θ • (𝔛.Meta.pointEquivPlace z')) 1 +
            ∑ y' ∈ oth', Finsupp.single (SemilinearAut.ofAlgAut θ • (𝔛.Meta.pointEquivPlace y')) (e' y' : ℤ)) := by
      rw [map_sub, map_sub, hFFz, hFFz']
    have hDv₁0 : AlgebraicCurve.Divisor.pullbackAlong βH hβint (AlgebraicCurve.Divisor.pushforwardAlong αH hαint
        (Finsupp.single (𝔛.Meta.pointEquivPlace z) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace z') 1 : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
      rw [Divisor.mem_degZero, hDv₁eq]
      simp only [map_sub, map_add, map_sum, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one]
      rw [← Nat.cast_sum, ← Nat.cast_sum, hsum, hsum']
      ring
    have hp1 := hpull1div ⟨_, hDw0⟩ ⟨_, hDv₁0⟩ rfl
    have hgenclass : αpull 1 (O.degPts 0 (Pic0.mk ⟨_, hDvmem⟩)) = Pic0.mk ⟨_, hDv₁0⟩ := by rw [hdp0, hp1]

    have ej0 : (if (0 : Fin 2) = 0 then (1 : Fin 2) else 0) = 1 := by decide
    have ej1 : (if (1 : Fin 2) = 0 then (1 : Fin 2) else 0) = 0 := by decide
    obtain ⟨z₁, u₁, hu₁, -, hu₁sm, hz₁pl, uκ₁, huκ₁₁, huκ₁₂, -, P₁, hP₁, hP₁pl⟩ :=
      ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq p M H hpM hj 𝔛 A hA ρ hρ hdia0 pb hpb wgen hwgen 0 z u hu husm uκ huκ₁ huκ₂ Pc hPz
    obtain ⟨z'₁, u'₁, hu'₁, -, hu'₁sm, hz'₁pl, uκ'₁, huκ'₁₁, huκ'₁₂, -, P'₁, hP'₁, hP'₁pl⟩ :=
      ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq p M H hpM hj 𝔛 A hA ρ hρ hdia0 pb hpb wgen hwgen 0 z' u' hu' husm' uκ' huκ'₁ huκ'₂ Qc hQz
    rw [ej0] at hP₁ hP'₁
    have hpl₁ : (𝔛.Mfib A hA ρ hρ).placeOfPoint P₁ = (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • (𝔛.Mfib A hA ρ hρ).placeOfPoint Pc := by simpa using hP₁pl
    have hpl'₁ : (𝔛.Mfib A hA ρ hρ).placeOfPoint P'₁ = (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • (𝔛.Mfib A hA ρ hρ).placeOfPoint Qc := by simpa using hP'₁pl

    have hC : ∀ (Rc : closedPoints (𝔛.Mfib A hA ρ hρ).C) (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (v : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (hv : barPt A ≫ v.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) (vκ : (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
        (hvκ₁ : vκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v.1) (hvκ₂ : vκ ≫ pullback.snd _ _ = 𝟙 _)
        (hR : ((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ 0).base Rc.1 = vκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
        (hR0 : ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)), (𝔛.Mfib A hA ρ hρ).placeOfPoint Rc ≠ 𝔛.placeOn0 A hA ρ hρ n)
        (y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}), y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 → y' ≠ y →
        ∃ (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (w₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)) (_ : barPt A ≫ w₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
          (_ : Set.range w₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) (wκ₁ : (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
          (_ : wκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ w₁.1) (_ : wκ₁ ≫ pullback.snd _ _ = 𝟙 _)
          (R₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C) (_ : ((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ 0).base R₁.1 = wκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A))),
          𝔛.Meta.pointEquivPlace y₁ = wgen • 𝔛.Meta.pointEquivPlace y' ∧ (𝔛.Mfib A hA ρ hρ).placeOfPoint R₁ = Φ.symm ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc) := by
      intro Rc y v hv vκ hvκ₁ hvκ₂ hR hR0 y' hπ hne
      obtain ⟨-, vy, hvy, -, hvysm, vκy, hvκy₁, hvκy₂, -, Ry, hRy, hFrob⟩ :=
        ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_one_frob_placeOfPoint_eq_of_comp_pi_eq_of_ne p M H hpM hj 𝔛 A hA ρ hρ y v hv vκ hvκ₁ hvκ₂ Rc hR hR0 y' hπ hne
      obtain ⟨y₁, w₁, hw₁, -, hw₁sm, hy₁pl, wκ₁, hwκ₁₁, hwκ₁₂, -, R₁, hR₁, hR₁pl⟩ :=
        ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_w_inv_pointEquivPlace_eq_smul_placeOfPoint_eq p M H hpM hj 𝔛 A hA ρ hρ hdia0 pb hpb wgen hwgen 1 y' vy hvy hvysm vκy hvκy₁ hvκy₂ Ry hRy
      rw [ej1] at hR₁
      refine ⟨y₁, w₁, hw₁, hw₁sm, wκ₁, hwκ₁₁, hwκ₁₂, R₁, hR₁, hy₁pl, ?_⟩
      have hpl : (𝔛.Mfib A hA ρ hρ).placeOfPoint R₁ = (𝔛.Mfib A hA ρ hρ).placeOfPoint Ry := by simpa using hR₁pl
      rw [hpl, Equiv.eq_symm_apply, hΦ]
      exact hFrob
    choose fy fu hfu hfusm fuκ hfuκ₁ hfuκ₂ fR hfR hfypl hfRpl using hC Pc z u hu uκ huκ₁ huκ₂ hPz hP0
    choose gy gu hgu hgusm guκ hguκ₁ hguκ₂ gR hgR hgypl hgRpl using hC Qc z' u' hu' uκ' huκ'₁ huκ'₂ hQz hQ0

    have hg₀ne : ∀ (Rc : closedPoints (𝔛.Mfib A hA ρ hρ).C), (∀ s ∈ O.ssFinset, ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc) ≠ s.1 ∧ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc) ≠ Φ s.1) →
        ∀ s ∈ O.ssFinset, (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc) ≠ s.2 := by
      intro Rc hR s hs h
      apply (hR s hs).2
      rw [← hinv s hs, ← h, inv_smul_smul]
    have hΦne : ∀ (Rc : closedPoints (𝔛.Mfib A hA ρ hρ).C), (∀ s ∈ O.ssFinset, ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc) ≠ s.1 ∧ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc) ≠ Φ s.1) →
        ∀ s ∈ O.ssFinset, Φ.symm ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc) ≠ s.1 := by
      intro Rc hR s hs h
      apply (hR s hs).2
      rw [← h, Equiv.apply_symm_apply]

    have hDvw := AlgebraicCurve.SemilinearAut.hsup_coe_degZeroSMulHom_single_sub_single wgen ⟨_, hDvmem⟩ _ _ _ _ hz₁pl hz'₁pl rfl
    have hdw := AlgebraicCurve.Divisor.hsup_single_sub_single_mem_degZero_and_apply hdegF
      ((SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint Pc)) ((SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint Qc))
    have hadmw : (((0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (Finsupp.single ((SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint Pc)) 1 - Finsupp.single ((SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint Qc)) 1 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),
        (0 : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)) : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) ∈ GluingData.admissible O.ssFinset :=
      ⟨zero_mem _, hdw.1, fun s hs => ⟨rfl, hdw.2 s.2 (hg₀ne Pc hP s hs) (hg₀ne Qc hQ s hs)⟩⟩
    obtain ⟨sw, hsw, hswx⟩ := hsp 1 z₁ u₁ hu₁ hu₁sm uκ₁ huκ₁₁ huκ₁₂ P₁ hP₁ z'₁ u'₁ hu'₁ hu'₁sm uκ'₁ huκ'₁₁ huκ'₁₂ P'₁ hP'₁
      (SemilinearAut.degZeroSMulHom wgen ⟨_, hDvmem⟩) hDvw ⟨_, hadmw⟩ (by rw [if_neg (by decide)]) (by rw [if_pos rfl, hpl₁, hpl'₁]) rfl

    have hdt : ∀ (Rc : closedPoints (𝔛.Mfib A hA ρ hρ).C), (Finsupp.single (Φ.symm ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc)) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Pc) 1 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) ∈ Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)) ∧
        ∀ w, Φ.symm ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc) ≠ w → ((𝔛.Mfib A hA ρ hρ).placeOfPoint Pc) ≠ w → (Finsupp.single (Φ.symm ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc)) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Pc) 1 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) w = 0 :=
      fun Rc => AlgebraicCurve.Divisor.hsup_single_sub_single_mem_degZero_and_apply hdegF _ _
    have hadmt : ∀ (Rc : closedPoints (𝔛.Mfib A hA ρ hρ).C), (∀ s ∈ O.ssFinset, ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc) ≠ s.1 ∧ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc) ≠ Φ s.1) →
        (((Finsupp.single (Φ.symm ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc)) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Pc) 1 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),
          (0 : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)) : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) ∈ GluingData.admissible O.ssFinset :=
      fun Rc hR => ⟨(hdt Rc).1, zero_mem _, fun s hs => ⟨(hdt Rc).2 s.1 (hΦne Rc hR s hs) (hP s hs).1, rfl⟩⟩
    have hpair : ∀ (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}), (Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace z) 1 : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈
        Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := fun y₁ => by
      rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1, sub_self]
    have hT : ∀ (Rc : closedPoints (𝔛.Mfib A hA ρ hρ).C) (hR : ∀ s ∈ O.ssFinset, ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc) ≠ s.1 ∧ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc) ≠ Φ s.1)
        (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (w₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)) (_ : barPt A ≫ w₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (_ : Set.range w₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) (wκ₁ : (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
        (_ : wκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ w₁.1) (_ : wκ₁ ≫ pullback.snd _ _ = 𝟙 _)
        (R₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C) (_ : ((𝔛.efib A hA ρ hρ) ≫ 𝔛.comp A hA ρ hρ 0).base R₁.1 = wκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
        (_ : ((𝔛.Mfib A hA ρ hρ).placeOfPoint R₁) = Φ.symm ((𝔛.Mfib A hA ρ hρ).placeOfPoint Rc)),
        ∃ tt : SchemeHomOver Λ.σA O.g, (O.pts (Pic0.mk ⟨_, hpair y₁⟩)).1 = barPt A ≫ tt.1 ∧
          O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ tt) = GluedPic0.mk O.ssFinset ⟨_, hadmt Rc hR⟩ := by
      intro Rc hR y₁ w₁ hw₁ hw₁sm wκ₁ hwκ₁₁ hwκ₁₂ R₁ hR₁ hR₁pl
      exact hsp 0 y₁ w₁ hw₁ hw₁sm wκ₁ hwκ₁₁ hwκ₁₂ R₁ hR₁ z u hu husm uκ huκ₁ huκ₂ Pc hPz ⟨_, hpair y₁⟩ rfl ⟨_, hadmt Rc hR⟩
        (by rw [if_pos rfl, hR₁pl]) (by rw [if_neg (by decide)]) rfl

    have hTf : ∀ y' ∈ oth, ∃ (D₁ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))) (tt : SchemeHomOver Λ.σA O.g),
        (D₁ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = Finsupp.single (wgen • 𝔛.Meta.pointEquivPlace y') 1 - Finsupp.single (𝔛.Meta.pointEquivPlace z) 1 ∧
        (O.pts (Pic0.mk D₁)).1 = barPt A ≫ tt.1 ∧
        O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ tt) = GluedPic0.mk O.ssFinset ⟨_, hadmt Pc hP⟩ := by
      intro y' hy'
      have h1 := (hoth y' hy').1
      have h2 := (hoth y' hy').2
      obtain ⟨tt, htt, httx⟩ := hT Pc hP (fy y' h1 h2) (fu y' h1 h2) (hfu y' h1 h2) (hfusm y' h1 h2) (fuκ y' h1 h2)
        (hfuκ₁ y' h1 h2) (hfuκ₂ y' h1 h2) (fR y' h1 h2) (hfR y' h1 h2) (hfRpl y' h1 h2)
      exact ⟨_, tt, by rw [← hfypl y' h1 h2], htt, httx⟩
    have hTg : ∀ y' ∈ oth', ∃ (D₁ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))) (tt : SchemeHomOver Λ.σA O.g),
        (D₁ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = Finsupp.single (wgen • 𝔛.Meta.pointEquivPlace y') 1 - Finsupp.single (𝔛.Meta.pointEquivPlace z) 1 ∧
        (O.pts (Pic0.mk D₁)).1 = barPt A ≫ tt.1 ∧
        O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ tt) = GluedPic0.mk O.ssFinset ⟨_, hadmt Qc hQ⟩ := by
      intro y' hy'
      have h1 := (hoth' y' hy').1
      have h2 := (hoth' y' hy').2
      obtain ⟨tt, htt, httx⟩ := hT Qc hQ (gy y' h1 h2) (gu y' h1 h2) (hgu y' h1 h2) (hgusm y' h1 h2) (guκ y' h1 h2)
        (hguκ₁ y' h1 h2) (hguκ₂ y' h1 h2) (gR y' h1 h2) (hgR y' h1 h2) (hgRpl y' h1 h2)
      exact ⟨_, tt, by rw [← hgypl y' h1 h2], htt, httx⟩
    haveI : Inhabited (SchemeHomOver Λ.σA O.g) := ⟨sw⟩
    choose! fD ft hfD hft hftx using hTf
    choose! gD gt hgD hgt hgtx using hTg

    have hsw' : (O.pts (Pic0.mk (SemilinearAut.degZeroSMulHom wgen ⟨_, hDvmem⟩))).1 = barPt A ≫ sw.1 := hsw
    obtain ⟨S₁, hS₁, hS₁x⟩ := ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_pts_add_sum_zsmul_ptsSp_symm_eq_add_sum p M H hpM A hA Λ O
      sw _ hsw' oth (fun y' => Pic0.mk (fD y')) (fun y' => (e y' : ℤ)) ft hft
    obtain ⟨S, hS, hSx⟩ := ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_pts_add_sum_zsmul_ptsSp_symm_eq_add_sum p M H hpM A hA Λ O
      S₁ _ hS₁ oth' (fun y' => Pic0.mk (gD y')) (fun y' => -(e' y' : ℤ)) gt hgt
    rw [hS₁x, hswx] at hSx

    have hsumZ : ∑ y' ∈ oth, (e y' : ℤ) = ((p : ℕ) : ℤ) := by rw [← Nat.cast_sum, hsum]
    have hsumZ' : ∑ y' ∈ oth', (e' y' : ℤ) = ((p : ℕ) : ℤ) := by rw [← Nat.cast_sum, hsum']
    have L1 : ∑ y' ∈ oth, (e y' : ℤ) • ((fD y' : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        ∑ y' ∈ oth, Finsupp.single (SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y') (e y' : ℤ) -
          ((p : ℕ) : ℤ) • Finsupp.single (𝔛.Meta.pointEquivPlace z) 1 := by
      rw [← hsumZ, Finset.sum_smul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y' hy' => ?_
      rw [hfD y' hy', hwgenθ, smul_sub, Finsupp.smul_single', mul_one]
    have L2 : ∑ y' ∈ oth', (-(e' y' : ℤ)) • ((gD y' : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        -(∑ y' ∈ oth', Finsupp.single (SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y') (e' y' : ℤ) -
          ((p : ℕ) : ℤ) • Finsupp.single (𝔛.Meta.pointEquivPlace z) 1) := by
      rw [← hsumZ', Finset.sum_smul, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y' hy' => ?_
      rw [hgD y' hy', hwgenθ, neg_smul, smul_sub, Finsupp.smul_single', mul_one]
    let mkH : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) →+ JH M H := QuotientAddGroup.mk' _
    have hmkH : ∀ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))), mkH D = Pic0.mk D := fun _ => rfl
    have hDID : Pic0.mk (SemilinearAut.degZeroSMulHom wgen ⟨_, hDvmem⟩) + ∑ y' ∈ oth, (e y' : ℤ) • Pic0.mk (fD y') +
        ∑ y' ∈ oth', (-(e' y' : ℤ)) • Pic0.mk (gD y') = Pic0.mk ⟨_, hDv₁0⟩ := by
      have h1 : mkH (SemilinearAut.degZeroSMulHom wgen ⟨_, hDvmem⟩ + ∑ y' ∈ oth, (e y' : ℤ) • fD y' +
          ∑ y' ∈ oth', (-(e' y' : ℤ)) • gD y') = mkH ⟨_, hDv₁0⟩ := by
        refine congrArg mkH (Subtype.ext ?_)
        rw [AddMemClass.coe_add, AddMemClass.coe_add, AddSubmonoidClass.coe_finset_sum, AddSubmonoidClass.coe_finset_sum]
        simp only [AddSubgroupClass.coe_zsmul]
        rw [hDvw, L1, L2, hDv₁eq, hz₁pl, hz'₁pl, hwgenθ]
        abel
      rw [map_add, map_add, map_sum, map_sum] at h1
      simp only [map_zsmul, hmkH] at h1
      exact h1

    rw [hDID, ← hgenclass] at hS
    haveI : IsSeparated O.g := O.separated
    letI : Algebra (R p) ↥A := ρ.toAlgebra
    have hgen_eq : Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) ≫
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1)).1 =
        Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) ≫ S.1 := by
      show barPt A ≫ _ = barPt A ≫ _
      rw [← hZ, ← hS]
    have hZS := @AlgebraicGeometry.SchemeHomOver.eq_of_isSeparated_of_valuationRing_of_fst_eq (R p) _ O.G O.g _ ↥A _ _ _ _
      (AlgebraicClosure ℚ) _ _ _ _ (IsScalarTower.of_algebraMap_eq' hρ.symm)
      ⟨(NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1)).1,
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1)).2.trans hσA⟩
      ⟨S.1, S.2.trans hσA⟩ hgen_eq
    have hZS1 : (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1)).1 = S.1 := by
      have h := congrArg Subtype.val hZS
      exact h
    have hZS' : NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom 0)) (degPull 1)) =
        NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ S := by
      apply Subtype.ext
      show resPt A ≫ _ = resPt A ≫ _
      rw [hZS1]
    rw [hLmZ, hZS', hSx]

    have M1 : ∑ y' ∈ oth, (e y' : ℤ) • O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (ft y')) =
        ((p : ℕ) : ℤ) • GluedPic0.mk O.ssFinset ⟨_, hadmt Pc hP⟩ := by
      refine (Finset.sum_congr rfl fun y' hy' => by rw [hftx y' hy']).trans ((pull1sp_sum_zsmul_const _ _ _).trans ?_)
      rw [hsumZ]
    have M2 : ∑ y' ∈ oth', (-(e' y' : ℤ)) • O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (gt y')) =
        (-((p : ℕ) : ℤ)) • GluedPic0.mk O.ssFinset ⟨_, hadmt Qc hQ⟩ := by
      refine (Finset.sum_congr rfl fun y' hy' => by rw [hgtx y' hy']).trans ((pull1sp_sum_zsmul_const _ _ _).trans ?_)
      rw [Finset.sum_neg_distrib, hsumZ']
    rw [M1, M2]
    have hadmEq : ((⟨_, hadmw⟩ : ↥(GluingData.admissible O.ssFinset)) + ((p : ℕ) : ℤ) • (⟨_, hadmt Pc hP⟩ : ↥(GluingData.admissible O.ssFinset)) +
        (-((p : ℕ) : ℤ)) • (⟨_, hadmt Qc hQ⟩ : ↥(GluingData.admissible O.ssFinset))) =
        ⟨_, hadmR ⟨_, hm.1⟩ (hAVd ⟨_, hm⟩)⟩ := by
      refine Subtype.ext (Prod.ext ?_ (Prod.ext ?_ ?_))
      · show (0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) + ((p : ℕ) : ℤ) • (Finsupp.single (Φ.symm ((𝔛.Mfib A hA ρ hρ).placeOfPoint Pc)) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Pc) 1 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) +
            (-((p : ℕ) : ℤ)) • (Finsupp.single (Φ.symm ((𝔛.Mfib A hA ρ hρ).placeOfPoint Qc)) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Pc) 1 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
          ((p : ℕ) : ℤ) • Finsupp.mapDomain Φ.symm (Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Pc) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Qc) 1 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
        rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
        simp only [smul_sub, neg_smul, zero_add]
        abel
      · show (Finsupp.single ((SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint Pc)) 1 - Finsupp.single ((SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb))) • ((𝔛.Mfib A hA ρ hρ).placeOfPoint Qc)) 1 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) +
            ((p : ℕ) : ℤ) • (0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) + (-((p : ℕ) : ℤ)) • (0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) = (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb))) • (Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Pc) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Qc) 1 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
        rw [smul_zero, smul_zero, add_zero, add_zero, smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single]
      · show (0 : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ) + ((p : ℕ) : ℤ) • (0 : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ) +
            (-((p : ℕ) : ℤ)) • (0 : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ) = 0
        rw [smul_zero, smul_zero, add_zero, add_zero]
    have hfin := congrArg (GluedPic0.mk O.ssFinset) hadmEq
    rw [map_add, map_add, map_zsmul, map_zsmul] at hfin
    exact hfin
  have hLR : Lm = Rm := by
    refine AlgebraicCurve.Divisor.pull1sp_addMonoidHom_eq_of_eqOn_single_sub_single (G := GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) hdegF
      {v | ∃ s ∈ O.ssFinset, v = s.1 ∨ v = Φ s.1} AV (fun E hE => hE.1) ?_ ?_ Lm Rm ?_
    · intro E hE v hv
      obtain ⟨s, hs, rfl | rfl⟩ := hv
      · exact (hE.2 s hs).1
      · exact (hE.2 s hs).2
    · intro P Q hP hQ
      have hP' : ∀ s ∈ O.ssFinset, P ≠ s.1 ∧ P ≠ Φ s.1 := fun s hs =>
        ⟨fun h => hP ⟨s, hs, Or.inl h⟩, fun h => hP ⟨s, hs, Or.inr h⟩⟩
      have hQ' : ∀ s ∈ O.ssFinset, Q ≠ s.1 ∧ Q ≠ Φ s.1 := fun s hs =>
        ⟨fun h => hQ ⟨s, hs, Or.inl h⟩, fun h => hQ ⟨s, hs, Or.inr h⟩⟩
      refine ⟨(AlgebraicCurve.Divisor.hsup_single_sub_single_mem_degZero_and_apply hdegF P Q).1, fun s hs => ⟨?_, ?_⟩⟩
      · exact (AlgebraicCurve.Divisor.hsup_single_sub_single_mem_degZero_and_apply hdegF P Q).2 _ (hP' s hs).1 (hQ' s hs).1
      · exact (AlgebraicCurve.Divisor.hsup_single_sub_single_mem_degZero_and_apply hdegF P Q).2 _ (hP' s hs).2 (hQ' s hs).2
    · intro P Q hP hQ
      have hP' : ∀ s ∈ O.ssFinset, P ≠ s.1 ∧ P ≠ Φ s.1 := fun s hs =>
        ⟨fun h => hP ⟨s, hs, Or.inl h⟩, fun h => hP ⟨s, hs, Or.inr h⟩⟩
      have hQ' : ∀ s ∈ O.ssFinset, Q ≠ s.1 ∧ Q ≠ Φ s.1 := fun s hs =>
        ⟨fun h => hQ ⟨s, hs, Or.inl h⟩, fun h => hQ ⟨s, hs, Or.inr h⟩⟩
      exact hGEN P Q hP' hQ' _
  have hfinal := DFunLike.congr_fun hLR ⟨(D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), D.2, hD⟩
  rw [hLHS D hD, hRHS]
  exact hfinal

end S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_ptsSp_degPull_one_eq_mk_of_forall_apply_eq_zero_of_pullbackAlong
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_ptsSp_degPull_one_eq_mk_of_forall_apply_eq_zero_of_pullbackAlong (solution)
