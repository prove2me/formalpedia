-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.ord_residue_nonneg_of_fixed_of_isAffinePlace_of_forall_ord_nonneg_fst_and_snd_of_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/75c00565-c3d7-5a6a-bd4f-bf3170b38e7e

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd
import Theorems.Thm_ModularCurve_ord_eq_zero_of_not_mem_ssPlacesQExp_of_hasValue_of_coe_eq_coeffMap_modularUnitSeries
import Theorems.Thm_ModularCurve_hasValue_zero_of_mem_ssPlacesQExp_of_coe_eq_coeffMap_modularUnitSeries
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_finite_setOf_fixed_of_eq_gammaLift
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_of_isAffinePlace_qExpFrobeniusPlaceModL
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffinePlace_prolongationDatum
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_delta_injective_and_not_isAffinePlace_reduce_of_isCuspidal_isZeroSide
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residue_snd_eq_zero_of_residue_fst_hasValue_zero_of_nodeValueLaw
import Theorems.Thm_ModularCurve_nonempty_ssPlacesQExp
import Theorems.Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_unit_pair_divisor_oneSidedLaws_jump_prolongationDatum_of_isModel_of_nodeValueLaw
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_ModularCurve_algEquiv_apply_eq_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_of_qExpand_of_arithmeticGalois_comm
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_ord_residue_nonneg_of_fixed_of_isAffinePlace_of_forall_ord_nonneg_fst_and_snd_of_offDiag
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule"
p2m_attr_erase "instance" "KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free ModularCurve.TwoChart.isOpenImmersion_fInf ModularCurve.TwoChart.isOpenImmersion_ιFin ModularCurve.TwoChart.isOpenImmersion_ιInf ModularCurve.TwoChart.isOpenImmersion_fFin GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ValuationSubring.instIsAlgClosedResidueField ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.TwoChart.coe_jChartFin ModularCurve.TwoChart.ιFin_modelTo ModularCurve.TwoChart.ιInf_modelTo ModularCurve.TwoChart.ιInf_modelTo_assoc ModularCurve.TwoChart.coe_jInvChartInf ModularCurve.TwoChart.ιFin_modelTo_assoc ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_jqNGen ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false

section UnitCalcSec

open AlgebraicCurve IsLocalRing

namespace UnitCalc

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
variable (R : RegularProlongation A F Fbar)

theorem residue_inv_eq {u : F} (hu : u ∈ R.integers) (hu0 : R.residue ⟨u, hu⟩ ≠ 0) (hu' : u⁻¹ ∈ R.integers) :
    R.residue ⟨u⁻¹, hu'⟩ = (R.residue ⟨u, hu⟩)⁻¹ := by
  have hu_ne : u ≠ 0 := by
    intro h
    apply hu0
    have : (⟨u, hu⟩ : ↥R.integers) = 0 := Subtype.ext h
    rw [this, map_zero]
  have hmul : (⟨u, hu⟩ : ↥R.integers) * ⟨u⁻¹, hu'⟩ = 1 := Subtype.ext (by
    show u * u⁻¹ = 1
    exact mul_inv_cancel₀ hu_ne)
  have h := congrArg R.residue hmul
  rw [map_mul, map_one] at h
  exact (eq_inv_of_mul_eq_one_right h).symm ▸ rfl

theorem pow_mul_pow_mem {g w : F} (hg : g ∈ R.integers) (hw : w ∈ R.integers) (m n : ℕ) :
    ∃ h : g ^ m * w ^ n ∈ R.integers, R.residue ⟨g ^ m * w ^ n, h⟩ = R.residue ⟨g, hg⟩ ^ m * R.residue ⟨w, hw⟩ ^ n := by
  refine ⟨mul_mem (pow_mem hg m) (pow_mem hw n), ?_⟩
  have : (⟨g ^ m * w ^ n, mul_mem (pow_mem hg m) (pow_mem hw n)⟩ : ↥R.integers) = ⟨g, hg⟩ ^ m * ⟨w, hw⟩ ^ n :=
    Subtype.ext (by simp)
  rw [this, map_mul, map_pow, map_pow]

theorem pow_mul_zpow_mem {g u : F} (hg : g ∈ R.integers) (hu : u ∈ R.integers) (hu0 : R.residue ⟨u, hu⟩ ≠ 0)
    (hu' : u⁻¹ ∈ R.integers) (m : ℕ) (j : ℤ) :
    ∃ h : g ^ m * u ^ j ∈ R.integers, R.residue ⟨g ^ m * u ^ j, h⟩ = R.residue ⟨g, hg⟩ ^ m * R.residue ⟨u, hu⟩ ^ j := by
  rcases Int.eq_nat_or_neg j with ⟨n, rfl | rfl⟩
  · obtain ⟨h, hres⟩ := pow_mul_pow_mem R hg hu m n
    refine ⟨by rw [zpow_natCast]; exact h, ?_⟩
    have : (⟨g ^ m * u ^ (n : ℤ), by rw [zpow_natCast]; exact h⟩ : ↥R.integers) = ⟨g ^ m * u ^ n, h⟩ :=
      Subtype.ext (by simp)
    rw [this, hres, zpow_natCast]
  · obtain ⟨h, hres⟩ := pow_mul_pow_mem R hg hu' m n
    have heq : g ^ m * u ^ (-(n : ℤ)) = g ^ m * u⁻¹ ^ n := by rw [zpow_neg, zpow_natCast, inv_pow]
    refine ⟨by rw [heq]; exact h, ?_⟩
    have : (⟨g ^ m * u ^ (-(n : ℤ)), by rw [heq]; exact h⟩ : ↥R.integers) = ⟨g ^ m * u⁻¹ ^ n, h⟩ := Subtype.ext heq
    rw [this, hres, residue_inv_eq R hu hu0 hu', zpow_neg, zpow_natCast, inv_pow]

theorem residue_pow_mul_zpow_ne_zero {g u : F} (hg : g ∈ R.integers) (hg0 : R.residue ⟨g, hg⟩ ≠ 0)
    (hu : u ∈ R.integers) (hu0 : R.residue ⟨u, hu⟩ ≠ 0) (hu' : u⁻¹ ∈ R.integers) (m : ℕ) (j : ℤ)
    (h : g ^ m * u ^ j ∈ R.integers) : R.residue ⟨g ^ m * u ^ j, h⟩ ≠ 0 := by
  obtain ⟨h', hres⟩ := pow_mul_zpow_mem R hg hu hu0 hu' m j
  rw [hres]
  exact mul_ne_zero (pow_ne_zero _ hg0) (zpow_ne_zero _ hu0)

theorem ord_residue_pow_mul_zpow {k : Type*} [Field k] [Algebra k Fbar] (v : Place k Fbar)
    {g u : F} (hg : g ∈ R.integers) (hg0 : R.residue ⟨g, hg⟩ ≠ 0)
    (hu : u ∈ R.integers) (hu0 : R.residue ⟨u, hu⟩ ≠ 0) (hu' : u⁻¹ ∈ R.integers) (m : ℕ) (j : ℤ)
    (h : g ^ m * u ^ j ∈ R.integers) :
    v.ord (R.residue ⟨g ^ m * u ^ j, h⟩) = (m : ℤ) * v.ord (R.residue ⟨g, hg⟩) + j * v.ord (R.residue ⟨u, hu⟩) := by
  obtain ⟨h', hres⟩ := pow_mul_zpow_mem R hg hu hu0 hu' m j
  rw [hres, v.ord_mul (pow_ne_zero _ hg0) (zpow_ne_zero _ hu0),
    show R.residue ⟨g, hg⟩ ^ m = R.residue ⟨g, hg⟩ ^ ((m : ℕ) : ℤ) from (zpow_natCast _ m).symm,
    Place.ord_zpow, Place.ord_zpow]

theorem ord_residue_eq_zero_of_pow_mul_zpow {k : Type*} [Field k] [Algebra k Fbar] (v : Place k Fbar)
    {g u : F} (hg : g ∈ R.integers) (hg0 : R.residue ⟨g, hg⟩ ≠ 0)
    (hu : u ∈ R.integers) (hu0 : R.residue ⟨u, hu⟩ ≠ 0) (hu' : u⁻¹ ∈ R.integers) {m : ℕ} (hm : m ≠ 0) (j : ℤ)
    (h : g ^ m * u ^ j ∈ R.integers)
    (hordu : v.ord (R.residue ⟨u, hu⟩) = 0) (hord : v.ord (R.residue ⟨g ^ m * u ^ j, h⟩) = 0) :
    v.ord (R.residue ⟨g, hg⟩) = 0 := by
  rw [ord_residue_pow_mul_zpow R v hg hg0 hu hu0 hu' m j h, hordu, mul_zero, add_zero] at hord
  rcases mul_eq_zero.mp hord with h0 | h0
  · exact absurd (by exact_mod_cast h0) hm
  · exact h0

end UnitCalc

end UnitCalcSec

namespace FixReadAux

theorem mapDomain_filter_apply_eq_sum {X Y : Type*} [DecidableEq X] [DecidableEq Y] (f : X → Y) (P : X → Prop) [DecidablePred P]
    (G : X →₀ ℤ) (v : Y) (S : Finset X) (hS : G.support ⊆ S) :
    Finsupp.mapDomain f (G.filter P) v = ∑ W ∈ S, if f W = v ∧ P W then G W else 0 := by
  have h1 : Finsupp.mapDomain f (G.filter P) v = ∑ W ∈ (G.filter P).support, if f W = v then (G.filter P) W else 0 := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun W _ => ?_
    rw [Finsupp.single_apply]
  rw [h1]
  have hsub : (G.filter P).support ⊆ S := fun W hW => by
    rw [Finsupp.support_filter, Finset.mem_filter] at hW
    exact hS hW.1
  rw [Finset.sum_subset hsub (fun W _ hW => by
    have h0 : (G.filter P) W = 0 := Finsupp.notMem_support_iff.mp hW
    rw [h0]; simp)]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finsupp.filter_apply]
  by_cases hv : f W = v <;> by_cases hP : P W <;> simp [hv, hP]

theorem mapDomain_apply_eq_zero_of_forall {X Y : Type*} (f : X → Y) (D : X →₀ ℤ) (v : Y)
    (h : ∀ W : X, f W = v → D W = 0) : Finsupp.mapDomain f D v = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun W _ => ?_
  rw [Finsupp.single_apply]
  split_ifs with hv
  · exact h W hv
  · rfl

theorem mapDomain_filter_apply_eq_mul_of_forall {X Y : Type*} (f : X → Y) (P : X → Prop) [DecidablePred P]
    (D E : X →₀ ℤ) (v : Y) (j : ℤ)
    (h : ∀ W : X, f W = v → D W = j * E W) :
    Finsupp.mapDomain f (D.filter P) v = j * Finsupp.mapDomain f (E.filter P) v := by
  classical
  rw [mapDomain_filter_apply_eq_sum f P D v (D.support ∪ E.support) Finset.subset_union_left,
    mapDomain_filter_apply_eq_sum f P E v (D.support ∪ E.support) Finset.subset_union_right,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases hv : f W = v
  · by_cases hP : P W
    · simp [hv, hP, h W hv]
    · simp [hP]
  · simp [hv]

end FixReadAux

section L123
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP

namespace FixReadAux

section Frame

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]
  {Psp : JHPlaceSpecialization p M H hpM A}
  {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}
  (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
  (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (hα : α.IsIntegral) (hβ : β.IsIntegral)
  (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
  (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))

theorem ne_zero_of_residue_ne_zero {L : Type*} [Field L] {A' : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (ResidueField ↥A') Fb] (R : RegularProlongation A' F Fb)
    {f : F} (hf : f ∈ R.integers) (h : R.residue ⟨f, hf⟩ ≠ 0) : f ≠ 0 := by
  intro h0
  apply h
  have : (⟨f, hf⟩ : ↥R.integers) = 0 := Subtype.ext h0
  rw [this, map_zero]

theorem ord_residue_fst_eq_zero_of_orderLawFixed_of_regularityLaw
    (hO : Rpd.OrderLawFixed α β hα hβ δ) (hRL : Rpd.RegularityLaw α β hα hβ δ SS)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    {F : ↥(xHFunctionFieldBar M H)} (h₁ : F ∈ Rpd.R₁.integers) (h₂ : F ∈ Rpd.R₂.integers)
    (hr₁ : Rpd.R₁.residue ⟨F, h₁⟩ ≠ 0) (hr₂ : Rpd.R₂.residue ⟨F, h₂⟩ ≠ 0)
    (v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v)
    (haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v)
    (hV : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → V.ord F = 0) :
    v.ord (Rpd.R₁.residue ⟨F, h₁⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0 := by
  have hF0 : F ≠ 0 := ne_zero_of_residue_ne_zero Rpd.R₁ h₁ hr₁
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) F hF0
  have hlaw := hO F h₁ h₂ hr₁ hr₂ D hD v hfix haff
  have hzero : Finsupp.mapDomain (Psp.reduceFst α hα) D v = 0 :=
    mapDomain_apply_eq_zero_of_forall _ D v fun W hW => by rw [hD W, hV W hW]
  rw [hzero] at hlaw
  obtain ⟨hge₁, hge₂⟩ := hRL.1 F h₁ h₂ v hfix haff (fun V hV' => by rw [hV V hV'])
  have h1 := hge₁ hr₁
  have h2 := hge₂ hr₂
  omega

open Classical in

theorem ord_residue_fst_eq_mul_of_cuspLawInfty
    (hCL : Rpd.CuspLawInfty α hα)
    {F : ↥(xHFunctionFieldBar M H)} (h₁ : F ∈ Rpd.R₁.integers) (h₂ : F ∈ Rpd.R₂.integers)
    (hr₁ : Rpd.R₁.residue ⟨F, h₁⟩ ≠ 0) (hr₂ : Rpd.R₂.residue ⟨F, h₂⟩ ≠ 0)
    (DF : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hDF : ∀ W, DF W = W.ord F)
    {u : ↥(xHFunctionFieldBar M H)} (hu₁ : u ∈ Rpd.R₁.integers)
    (Du : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hc : JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) c)
    (hone : Finsupp.mapDomain (Psp.reduceFst α hα)
        (Du.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα c) =
      (Psp.reduceFst α hα c).ord (Rpd.R₁.residue ⟨u, hu₁⟩ : Fbar p M H hpM (ResidueField ↥A)))
    (j : ℤ) (hfib : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα W = Psp.reduceFst α hα c → DF W = j * Du W) :
    (Psp.reduceFst α hα c).ord (Rpd.R₁.residue ⟨F, h₁⟩ : Fbar p M H hpM (ResidueField ↥A)) =
      j * (Psp.reduceFst α hα c).ord (Rpd.R₁.residue ⟨u, hu₁⟩ : Fbar p M H hpM (ResidueField ↥A)) := by
  have hlaw := hCL F h₁ h₂ hr₁ hr₂ DF hDF c hc
  rw [← hlaw, ← hone]
  exact mapDomain_filter_apply_eq_mul_of_forall _ _ DF Du _ j hfib

end Frame

end FixReadAux
end L123

section L4a
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace FixReadAux

section Ogg

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]
  {Psp : JHPlaceSpecialization p M H hpM A}
  {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}
  (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

theorem exists_oggUnit :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ (x : LaurentSeries ℤ) (u : ↥(xHFunctionFieldBar M H)) (h₁ : u ∈ Rpd.R₁.integers),
      coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p ∧
      ((u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p) ∧
      ((Rpd.R₁.residue ⟨u, h₁⟩ : Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
        coeffMap (Int.castRingHom (ResidueField ↥A)) x ∧
      Rpd.R₁.residue ⟨u, h₁⟩ ≠ 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨⟨x, hx, hx1, -⟩, hmem, -, -⟩ :=
    ModularCurve.exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd p M H hpM

  let y : LaurentSeries ↥A := coeffMap (Int.castRingHom ↥A) x
  have hyQ : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p) := by
    show coeffMap A.subtype (coeffMap (Int.castRingHom ↥A) x) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (modularUnitSeries p)
    rw [coeffMap_coeffMap, ← hx, coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext_int _ _) x
  have hyκ : coeffMap (IsLocalRing.residue ↥A) y = coeffMap (Int.castRingHom (ResidueField ↥A)) x := by
    show coeffMap (IsLocalRing.residue ↥A) (coeffMap (Int.castRingHom ↥A) x) = _
    rw [coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext_int _ _) x
  have hmemBar : coeffMap A.subtype y ∈ xHFunctionFieldBar M H := by
    rw [hyQ]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem
  obtain ⟨h₁, hres⟩ := Rpd.residue₁_coeffMap y hmemBar
  refine ⟨x, ⟨coeffMap A.subtype y, hmemBar⟩, h₁, hx, hyQ, hres.trans hyκ, ?_⟩

  intro h0
  have h := congrArg (fun g : Fbar p M H hpM (ResidueField ↥A) => ((g : Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)).coeff (1 - (p : ℤ))) h0
  try simp only at h
  rw [hres.trans hyκ, coeffMap_coeff, hx1, map_one, ZeroMemClass.coe_zero] at h
  exact one_ne_zero (h.trans (by simp))

theorem ord_residue_oggUnit_eq_zero_and_hasValue_zero
    {x : LaurentSeries ℤ} {u : ↥(xHFunctionFieldBar M H)} {h₁ : u ∈ Rpd.R₁.integers}
    (hx : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p)
    (hres : ((Rpd.R₁.residue ⟨u, h₁⟩ : Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
      coeffMap (Int.castRingHom (ResidueField ↥A)) x) :
    (∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
        v ∉ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p →
        JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v →
        v.ord (Rpd.R₁.residue ⟨u, h₁⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0) ∧
    (∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
        v ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p →
        v.HasValue (Rpd.R₁.residue ⟨u, h₁⟩ : Fbar p M H hpM (ResidueField ↥A)) 0) := by
  refine ⟨fun v hv haff => ?_, fun v hv => ?_⟩
  · obtain ⟨xj, a, hxj, hva⟩ := haff
    exact ModularCurve.ord_eq_zero_of_not_mem_ssPlacesQExp_of_hasValue_of_coe_eq_coeffMap_modularUnitSeries p (ResidueField ↥A)
      (ΓN p M H hpM) x hx _ hres v hv xj hxj a hva
  · exact ModularCurve.hasValue_zero_of_mem_ssPlacesQExp_of_coe_eq_coeffMap_modularUnitSeries p (ResidueField ↥A)
      (ΓN p M H hpM) x hx _ hres v hv

end Ogg

end FixReadAux
end L4a

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups
open ModularCurve.JHNeronObjectAtP (Fbar)

namespace FixReadAux

theorem frame_facts
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)
    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS)
    (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    {v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) |
        JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite ∧
    (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) C →
        ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα C)) ∧
    (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) C →
        ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)) ∧
    (∀ w : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
        ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) w →
        ∃ c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
          JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) c ∧ Psp.reduceFst α hα c = w) := by
  have hFix := ModularCurve.JHPlaceSpecialization.finite_setOf_fixed_of_eq_gammaLift p M H hpM hpM2 A hA pb hpb δ hδ
  have hread := ModularCurve.JHPlaceSpecialization.delta_injective_and_not_isAffinePlace_reduce_of_isCuspidal_isZeroSide
    p M H hpM hpM2 hHp A hA θ α (θ.toAlgHom.comp α) hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hFix hmodel hα_coe hβ_coe hcusp
  exact ⟨hFix, hread.2.1, hread.2.2.1, fun w hw => (hcusp w hw).1⟩

theorem ord_pow_mul_zpow {K F : Type*} [Field K] [Field F] [Algebra K F] (W : Place K F) {g u : F} (hg : g ≠ 0) (hu : u ≠ 0)
    (m : ℕ) (j : ℤ) : W.ord (g ^ m * u ^ j) = (m : ℤ) * W.ord g + j * W.ord u := by
  rw [W.ord_mul (pow_ne_zero _ hg) (zpow_ne_zero _ hu), show g ^ m = g ^ ((m : ℕ) : ℤ) from (zpow_natCast g m).symm,
    Place.ord_zpow, Place.ord_zpow]

theorem inv_mem_of_residue_ne_zero {L : Type*} [Field L] {A' : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (ResidueField ↥A') Fb] (R : RegularProlongation A' F Fb)
    {f : F} (hf : f ∈ R.integers) (h : R.residue ⟨f, hf⟩ ≠ 0) : f⁻¹ ∈ R.integers := by
  have hu : IsUnit (⟨f, hf⟩ : ↥R.integers) := R.isUnit_of_residue_ne_zero h
  have hmul' : ((hu.unit : ↥R.integers) : F) * (((hu.unit⁻¹ : (↥R.integers)ˣ) : ↥R.integers) : F) = 1 := by
    rw [← MulMemClass.coe_mul, hu.unit.mul_inv]
    rfl
  have hspec : ((hu.unit : ↥R.integers) : F) = f := congrArg Subtype.val hu.unit_spec
  rw [hspec] at hmul'
  have hval : f⁻¹ = (((hu.unit⁻¹ : (↥R.integers)ˣ) : ↥R.integers) : F) := (eq_inv_of_mul_eq_one_right hmul').symm
  rw [hval]
  exact ((hu.unit⁻¹ : (↥R.integers)ˣ) : ↥R.integers).2

theorem isAffinePlace_of_mem_ssPlacesQExp {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p]
    {v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))}
    (hv : v ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p) :
    JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v :=
  hv.elim fun x hx => hx.elim fun a ha => ⟨x, a, ha.1, ha.2.1⟩

theorem gamma1_le_gammaH (N : ℕ) (H' : Subgroup (ZMod N)ˣ) : CongruenceSubgroup.Gamma1 N ≤ CohCarrier.GammaH N H' := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have h1 := (CongruenceSubgroup.Gamma1_mem N A).mp hA
  refine ⟨CongruenceSubgroup.Gamma1_in_Gamma0 N hA, ?_⟩
  have hone : CohCarrier.gamma0Units N ⟨A, CongruenceSubgroup.Gamma1_in_Gamma0 N hA⟩ = 1 :=
    Units.ext (by rw [CohCarrier.val_gamma0Units]; exact h1.2.1)
  rw [hone]
  exact one_mem H'

theorem fst_conjunct
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)
    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS)
    (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
    (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers) (hg0 : Rpd.R₁.residue ⟨g, hg⟩ ≠ 0)
    (v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v) (hnode : ∀ s ∈ SS, v ≠ s.1)
    (hV : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → V.ord g = 0) :
    v.ord (Rpd.R₁.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI := ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar M H
  have hgne : g ≠ 0 := ne_zero_of_residue_ne_zero Rpd.R₁ hg hg0

  have hff := frame_facts p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hβ_coe hTD hmodel
    hO hRL hNV hθgal hcusp hcompat hcompat'

  have hvss : v ∉ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p := fun hv => by
    have himg := ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq (ResidueField ↥A) p (ΓN p M H hpM)
    have hv' : v ∈ qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p '' ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p := by
      rw [himg]; exact hv
    exact hv'.elim fun w hw => hnode (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p w, w)
      ((hSS _).mpr (frob_mk_mem_ssNodePairsQExp hw.1)) hw.2.symm
  by_cases haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v
  ·

    refine (exists_oggUnit Rpd).elim fun x hx' => hx'.elim fun u hu' => hu'.elim fun h₁ hu => ?_
    have hx := hu.1
    have hucoe := hu.2.1
    have hres := hu.2.2.1
    have hres0 := hu.2.2.2
    have hune : u ≠ 0 := ne_zero_of_residue_ne_zero Rpd.R₁ h₁ hres0
    have hinv : u⁻¹ ∈ Rpd.R₁.integers := inv_mem_of_residue_ne_zero Rpd.R₁ h₁ hres0
    have hordu := (ord_residue_oggUnit_eq_zero_and_hasValue_zero Rpd hx hres).1 v hvss haff
    have hvan := (ord_residue_oggUnit_eq_zero_and_hasValue_zero Rpd hx hres).2

    have hucusp : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord u ≠ 0 →
        ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V) :=
      fun V hVu => hff.2.1 V
        (ModularCurve.JHPlaceSpecialization.isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries p M H hpM A u hucoe V hVu)

    have hssne := ModularCurve.nonempty_ssPlacesQExp (M / p) (ΓN p M H hpM)
      (gamma1_le_gammaH _ _) (CohCarrier.GammaH_le_Gamma0 _) p
      (fun h => hpM2 (by rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h)) (ResidueField ↥A)
    refine hssne.elim fun y hy => ?_
    have hs : (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y, y) ∈ SS := (hSS _).mpr (frob_mk_mem_ssNodePairsQExp hy)
    have hs1 : qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p := by
      have himg := ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq (ResidueField ↥A) p (ΓN p M H hpM)
      exact himg ▸ Set.mem_image_of_mem _ hy

    have hsep : ∀ h₂ : u ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u, h₂⟩ = 0 :=
      ModularCurve.JHPlaceSpecialization.ProlongationDatum.residue_snd_eq_zero_of_residue_fst_hasValue_zero_of_nodeValueLaw
        p M H hpM A θ α (θ.toAlgHom.comp α) hα hβ δ SS Psp Rpd hNV u h₁ hres0 _ hs
        (fun V hVu hboth => hucusp V hVu (hboth.1 ▸ isAffinePlace_of_mem_ssPlacesQExp hs1))
        (hvan _ hs1)

    refine (AlgebraicCurve.RegularProlongation.exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero
      A _ _ Rpd.R₂ u hune hsep g hgne).elim fun m hm' => hm'.elim fun j hj' => ?_
    have hm : m ≠ 0 := hj'.1
    refine hj'.2.elim fun h₂F hresF₂ => ?_

    refine (UnitCalc.pow_mul_zpow_mem Rpd.R₁ hg h₁ hres0 hinv m j).elim fun h₁F hresF₁eq => ?_
    have hresF₁ : Rpd.R₁.residue ⟨g ^ m * u ^ j, h₁F⟩ ≠ 0 :=
      UnitCalc.residue_pow_mul_zpow_ne_zero Rpd.R₁ hg hg0 h₁ hres0 hinv m j h₁F

    have hVF : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → V.ord (g ^ m * u ^ j) = 0 := by
      intro V hVv
      have hVu : V.ord u = 0 := by
        by_contra h
        exact hucusp V h (hVv ▸ haff)
      rw [ord_pow_mul_zpow V hgne hune, hV V hVv, hVu, mul_zero, mul_zero, add_zero]

    have hF := ord_residue_fst_eq_zero_of_orderLawFixed_of_regularityLaw Rpd α (θ.toAlgHom.comp α) hα hβ δ SS hO hRL
      h₁F h₂F hresF₁ hresF₂ v hfix haff hVF
    exact UnitCalc.ord_residue_eq_zero_of_pow_mul_zpow Rpd.R₁ v hg hg0 h₁ hres0 hinv hm j h₁F hordu hF
  ·

    refine (hff.2.2.2 v haff).elim fun c hc => ?_

    have hθ : ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) := by
      intro f u' hfu
      have hfα : f = α u' := Subtype.ext (hfu.trans (hα_coe u').symm)
      rw [hfα]
      exact hβ_coe u'
    refine (ModularCurve.XHDRModelAtP.exists_unit_pair_divisor_oneSidedLaws_jump_prolongationDatum_of_isModel_of_nodeValueLaw
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hθ hα_coe hTD hmodel hNV hcompat hcompat').elim
      fun u₁ hu₁ => hu₁.elim fun u₂ hu₂ => hu₂.elim fun D₁ hD₁' => hD₁'.elim fun D₂ hall => ?_
    have hD₁ : ∀ W, D₁ W = W.ord u₁ := hall.1
    refine hall.2.2.1.elim fun h₁u hu₁props => ?_
    have hres1u : Rpd.R₁.residue ⟨u₁, h₁u⟩ ≠ 0 := hu₁props.1
    have hinv1 : u₁⁻¹ ∈ Rpd.R₁.integers := hu₁props.2.1
    have hone := hu₁props.2.2.2 c hc.1
    have hjump := hall.2.2.2.1 g hgne
    have hu1ne : u₁ ≠ 0 := ne_zero_of_residue_ne_zero Rpd.R₁ h₁u hres1u
    refine hjump.elim fun m hm' => hm'.elim fun j hj' => ?_
    have hm : m ≠ 0 := hj'.1
    refine hj'.2.elim fun h₂F hresF₂ => ?_
    refine (UnitCalc.pow_mul_zpow_mem Rpd.R₁ hg h₁u hres1u hinv1 m j).elim fun h₁F hresF₁eq => ?_
    have hresF₁ : Rpd.R₁.residue ⟨g ^ m * u₁ ^ j, h₁F⟩ ≠ 0 :=
      UnitCalc.residue_pow_mul_zpow_ne_zero Rpd.R₁ hg hg0 h₁u hres1u hinv1 m j h₁F

    have hgmune : g ^ m * u₁ ^ j ≠ 0 := mul_ne_zero (pow_ne_zero _ hgne) (zpow_ne_zero _ hu1ne)
    refine (HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (g ^ m * u₁ ^ j) hgmune).elim fun DF hDF' => ?_
    have hDF : ∀ W, DF W = W.ord (g ^ m * u₁ ^ j) := hDF'.1
    have hfib : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα W = Psp.reduceFst α hα c → DF W = j * D₁ W := by
      intro W hW
      rw [hDF W, hD₁ W, ord_pow_mul_zpow W hgne hu1ne, hV W (hW.trans hc.2), mul_zero, zero_add]
    have hCL : Rpd.CuspLawInfty α hα := hmodel.2.2.1
    have hrel := ord_residue_fst_eq_mul_of_cuspLawInfty Rpd α hα hCL h₁F h₂F hresF₁ hresF₂ DF hDF h₁u D₁ c hc.1
      hone j hfib

    have hmul := UnitCalc.ord_residue_pow_mul_zpow Rpd.R₁ (Psp.reduceFst α hα c) hg hg0 h₁u hres1u hinv1 m j h₁F
    rw [hmul] at hrel
    have hzero : (m : ℤ) * (Psp.reduceFst α hα c).ord (Rpd.R₁.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0 := by linarith
    have hc2 : Psp.reduceFst α hα c = v := hc.2
    rw [hc2] at hzero
    rcases mul_eq_zero.mp hzero with h0 | h0
    · exact absurd (by exact_mod_cast h0) hm
    · exact h0

open Classical in

theorem ord_residue_snd_eq_mul_of_cuspLawZero
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]
    {Psp : JHPlaceSpecialization p M H hpM A}
    {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}
    (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hCL : Rpd.CuspLawZero β hβ δ)
    {F : ↥(xHFunctionFieldBar M H)} (h₁ : F ∈ Rpd.R₁.integers) (h₂ : F ∈ Rpd.R₂.integers)
    (hr₁ : Rpd.R₁.residue ⟨F, h₁⟩ ≠ 0) (hr₂ : Rpd.R₂.residue ⟨F, h₂⟩ ≠ 0)
    (DF : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hDF : ∀ W, DF W = W.ord F)
    {u : ↥(xHFunctionFieldBar M H)} (hu₂ : u ∈ Rpd.R₂.integers)
    (Du : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hc : JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) c)
    (hone : Finsupp.mapDomain (Psp.reduceSnd β hβ δ)
        (Du.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd β hβ δ c) =
      (Psp.reduceSnd β hβ δ c).ord (Rpd.R₂.residue ⟨u, hu₂⟩ : Fbar p M H hpM (ResidueField ↥A)))
    (j : ℤ) (hfib : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd β hβ δ W = Psp.reduceSnd β hβ δ c → DF W = j * Du W) :
    (Psp.reduceSnd β hβ δ c).ord (Rpd.R₂.residue ⟨F, h₂⟩ : Fbar p M H hpM (ResidueField ↥A)) =
      j * (Psp.reduceSnd β hβ δ c).ord (Rpd.R₂.residue ⟨u, hu₂⟩ : Fbar p M H hpM (ResidueField ↥A)) := by
  have hlaw := hCL F h₁ h₂ hr₁ hr₂ DF hDF c hc
  rw [← hlaw, ← hone]
  exact mapDomain_filter_apply_eq_mul_of_forall _ _ DF Du _ j hfib

theorem ord_algebraMap_eq_zero' {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) {c : K} (hc : c ≠ 0) :
    w.ord (algebraMap K F c) = 0 := by
  have hne : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  have h1 : 0 ≤ w.ord (algebraMap K F c) := (Place.mem_iff_ord_nonneg _ hne).mp (w.algebraMap_mem' c)
  have h2 : 0 ≤ w.ord (algebraMap K F c)⁻¹ := by
    rw [show (algebraMap K F c)⁻¹ = algebraMap K F c⁻¹ from (map_inv₀ _ c).symm]
    exact (Place.mem_iff_ord_nonneg _ ((map_ne_zero _).mpr (inv_ne_zero hc))).mp (w.algebraMap_mem' c⁻¹)
  rw [Place.ord_inv] at h2
  omega

theorem exists_sndUnit
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]
    {Psp : JHPlaceSpecialization p M H hpM A}
    {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}
    (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    {u : ↥(xHFunctionFieldBar M H)} (h₁ : u ∈ Rpd.R₁.integers) (hres0 : Rpd.R₁.residue ⟨u, h₁⟩ ≠ 0)
    (hAL : θ u = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((p : ℕ) : AlgebraicClosure ℚ) ^ 12) * u⁻¹) :
    ∃ (u₂ : ↥(xHFunctionFieldBar M H)) (h₂ : u₂ ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨u₂, h₂⟩ = Rpd.R₁.residue ⟨u, h₁⟩ ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧ u₂ ≠ 0 ∧
      (∀ h : u₂ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₂, h⟩ = 0) ∧
      ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord u₂ = - V.ord u := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hune : u ≠ 0 := ne_zero_of_residue_ne_zero Rpd.R₁ h₁ hres0
  have hinv : u⁻¹ ∈ Rpd.R₁.integers := inv_mem_of_residue_ne_zero Rpd.R₁ h₁ hres0

  let a : ↥A := ((p : ↥A)) ^ 12
  have ha : ((a : ↥A) : AlgebraicClosure ℚ) = ((p : ℕ) : AlgebraicClosure ℚ) ^ 12 := by
    show ((((p : ↥A)) ^ 12 : ↥A) : AlgebraicClosure ℚ) = _
    push_cast
    rfl
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ^ 12 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  set cst : ↥(xHFunctionFieldBar M H) := algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((p : ℕ) : AlgebraicClosure ℚ) ^ 12)
    with hcstdef
  have hcst0 : cst ≠ 0 := (map_ne_zero _).mpr hp0
  have hcsta : cst = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) := by rw [ha]
  have hcst1 : cst ∈ Rpd.R₁.integers := by rw [hcsta]; exact (Rpd.R₁.algebraMap_mem_iff _).mpr a.2
  have hrescst : Rpd.R₁.residue ⟨cst, hcst1⟩ = 0 := by
    have hsub : (⟨cst, hcst1⟩ : ↥Rpd.R₁.integers) =
        ⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ), (Rpd.R₁.algebraMap_mem_iff _).mpr a.2⟩ :=
      Subtype.ext hcsta
    rw [hsub, Rpd.R₁.residue_algebraMap a]
    have hra : IsLocalRing.residue ↥A a = 0 := by
      show IsLocalRing.residue ↥A (((p : ↥A)) ^ 12) = 0
      rw [map_pow, map_natCast, CharP.cast_eq_zero (ResidueField ↥A) p, zero_pow (by norm_num)]
    rw [hra, map_zero]
  refine ⟨cst * u⁻¹, ?_⟩
  have hθu₂ : θ (cst * u⁻¹) = u := by
    rw [map_mul, map_inv₀, hAL, hcstdef, AlgEquiv.commutes, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ hcst0, one_mul]
  have hu2ne : cst * u⁻¹ ≠ 0 := mul_ne_zero hcst0 (inv_ne_zero hune)
  have h₂u : cst * u⁻¹ ∈ Rpd.R₂.integers := (Rpd.mem_integers₂_iff _).mpr (by rw [hθu₂]; exact h₁)
  have hres2u := Rpd.residue₂_eq (cst * u⁻¹) h₂u
  have hsubθ : (⟨θ (cst * u⁻¹), (Rpd.mem_integers₂_iff _).mp h₂u⟩ : ↥Rpd.R₁.integers) = ⟨u, h₁⟩ := Subtype.ext hθu₂
  rw [hsubθ] at hres2u
  have hinv2 : (cst * u⁻¹)⁻¹ ∈ Rpd.R₂.integers := (Rpd.mem_integers₂_iff _).mpr (by rw [map_inv₀, hθu₂]; exact hinv)
  refine ⟨h₂u, hres2u, hinv2, hu2ne, fun h => ?_, fun V => ?_⟩
  · have hsub : (⟨cst * u⁻¹, h⟩ : ↥Rpd.R₁.integers) = ⟨cst, hcst1⟩ * ⟨u⁻¹, hinv⟩ := Subtype.ext rfl
    rw [hsub, map_mul, hrescst, zero_mul]
  · rw [V.ord_mul hcst0 (inv_ne_zero hune), Place.ord_inv, hcstdef, ord_algebraMap_eq_zero' V hp0, zero_add]

theorem ord_residue_snd_eq_zero_of_laws
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]
    {Psp : JHPlaceSpecialization p M H hpM A}
    {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}
    (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hO : Rpd.OrderLawFixed α β hα hβ δ) (hRL : Rpd.RegularityLaw α β hα hβ δ SS)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    {g : ↥(xHFunctionFieldBar M H)} (hg : g ∈ Rpd.R₂.integers) (hg0 : Rpd.R₂.residue ⟨g, hg⟩ ≠ 0)
    (v v' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hkey : δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v') = v)
    (hfix' : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v')
    (haff' : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v')
    (hVg : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v' → V.ord g = 0)
    {u : ↥(xHFunctionFieldBar M H)}
    (hVu : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v' → V.ord u = 0)
    {u₂ : ↥(xHFunctionFieldBar M H)} (h₂u : u₂ ∈ Rpd.R₂.integers) (hres2u0 : Rpd.R₂.residue ⟨u₂, h₂u⟩ ≠ 0)
    (hinv2 : u₂⁻¹ ∈ Rpd.R₂.integers) (hu2ne : u₂ ≠ 0) (hu2R1 : ∀ h : u₂ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₂, h⟩ = 0)
    (hordV2 : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord u₂ = - V.ord u)
    (hordu2 : v.ord (Rpd.R₂.residue ⟨u₂, h₂u⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0) :
    v.ord (Rpd.R₂.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0 := by
  have hgne : g ≠ 0 := ne_zero_of_residue_ne_zero Rpd.R₂ hg hg0

  refine (AlgebraicCurve.RegularProlongation.exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero
    A _ _ Rpd.R₁ u₂ hu2ne hu2R1 g hgne).elim fun m hm' => hm'.elim fun j hj' => ?_
  have hm : m ≠ 0 := hj'.1
  refine hj'.2.elim fun h₁F hresF₁ => ?_
  refine (UnitCalc.pow_mul_zpow_mem Rpd.R₂ hg h₂u hres2u0 hinv2 m j).elim fun h₂F hresF₂eq => ?_
  have hresF₂ : Rpd.R₂.residue ⟨g ^ m * u₂ ^ j, h₂F⟩ ≠ 0 := UnitCalc.residue_pow_mul_zpow_ne_zero Rpd.R₂ hg hg0 h₂u hres2u0 hinv2 m j h₂F

  have hVF : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v' → V.ord (g ^ m * u₂ ^ j) = 0 := by
    intro V hVv
    rw [ord_pow_mul_zpow V hgne hu2ne, hVg V hVv, hordV2 V, hVu V hVv, neg_zero, mul_zero, mul_zero, add_zero]
  have hgmune : g ^ m * u₂ ^ j ≠ 0 := mul_ne_zero (pow_ne_zero _ hgne) (zpow_ne_zero _ hu2ne)
  refine (HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (g ^ m * u₂ ^ j) hgmune).elim fun D hD' => ?_
  have hD : ∀ W, D W = W.ord (g ^ m * u₂ ^ j) := hD'.1
  have hlaw := hO (g ^ m * u₂ ^ j) h₁F h₂F hresF₁ hresF₂ D hD v' hfix' haff'
  rw [hkey, mapDomain_apply_eq_zero_of_forall _ D _ (fun W hW => by rw [hD W, hVF W hW])] at hlaw
  have hreg := hRL.1 (g ^ m * u₂ ^ j) h₁F h₂F v' hfix' haff' (fun V hV' => by rw [hVF V hV'])
  have hge₁ := hreg.1 hresF₁
  have hge₂ := hreg.2 hresF₂
  rw [hkey] at hge₂
  have hF : v.ord (Rpd.R₂.residue ⟨g ^ m * u₂ ^ j, h₂F⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0 := by omega
  exact UnitCalc.ord_residue_eq_zero_of_pow_mul_zpow Rpd.R₂ v hg hg0 h₂u hres2u0 hinv2 hm j h₂F hordu2 hF

theorem snd_conjunct
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)
    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS)
    (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
    (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers) (hg0 : Rpd.R₂.residue ⟨g, hg⟩ ≠ 0)
    (v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v) (hnode : ∀ s ∈ SS, v ≠ s.2)
    (hV : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → V.ord g = 0) :
    v.ord (Rpd.R₂.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI := ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar M H
  have hgne : g ≠ 0 := ne_zero_of_residue_ne_zero Rpd.R₂ hg hg0
  have hff := frame_facts p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hβ_coe hTD hmodel
    hO hRL hNV hθgal hcusp hcompat hcompat'
  have hpMp : ¬ p ∣ M / p := fun h => hpM2 (by rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h)
  have hbij := ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (ΓN p M H hpM)
  have hcomm : ∀ w : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (δ w) = δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p w) :=
    fun w => (congrArg (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p) (hδ w)).trans
      ((ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpMp
        (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) w).trans (hδ _).symm)

  have hkey : δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p
      (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v)) = v := by
    have h : qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v)) = v := hfix
    rw [hcomm] at h
    exact h
  have hfix' : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ
      (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v) := by
    show qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v))) = _
    rw [hkey]
  have hvss : v ∉ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p := fun hv =>
    hnode (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v, v) ((hSS _).mpr (frob_mk_mem_ssNodePairsQExp hv)) rfl
  have hfibre : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα V = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v →
        Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v := by
    intro V hV1
    rcases hTD V with h | h
    · rw [hV1] at h
      exact (hbij.1 h).symm
    · rw [hV1] at h
      rw [← h, hkey]
  by_cases haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v
  ·
    have haff' := (ModularCurve.JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
      p M H hpM A hA).1 v haff
    refine (exists_oggUnit Rpd).elim fun x hx' => hx'.elim fun u hu' => hu'.elim fun h₁ hu => ?_
    have hordu := (ord_residue_oggUnit_eq_zero_and_hasValue_zero Rpd hu.1 hu.2.2.1).1 v hvss haff
    have hucusp : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord u ≠ 0 →
        ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V) :=
      fun V hVu => hff.2.1 V
        (ModularCurve.JHPlaceSpecialization.isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries p M H hpM A u hu.2.1 V hVu)
    have hθ : ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) := by
      intro f u' hfu
      have hfα : f = α u' := Subtype.ext (hfu.trans (hα_coe u').symm)
      rw [hfα]
      exact hβ_coe u'
    have hAL := ModularCurve.algEquiv_apply_eq_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_of_qExpand_of_arithmeticGalois_comm
      p M H hpM hpM2 hHp hj θ hθ hθgal u hu.2.1
    refine (exists_sndUnit Rpd h₁ hu.2.2.2 hAL).elim fun u₂ hu₂' => hu₂'.elim fun h₂u hu₂ => ?_
    have hordu2 : v.ord (Rpd.R₂.residue ⟨u₂, h₂u⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0 := by rw [hu₂.1]; exact hordu
    have hres2u0 : Rpd.R₂.residue ⟨u₂, h₂u⟩ ≠ 0 := by rw [hu₂.1]; exact hu.2.2.2
    exact ord_residue_snd_eq_zero_of_laws Rpd α (θ.toAlgHom.comp α) hα hβ δ SS hO hRL hg hg0 v _ hkey hfix' haff'
      (fun V hV1 => hV V (hfibre V hV1))
      (fun V hV1 => by by_contra h; exact hucusp V h (hV1 ▸ haff'))
      h₂u hres2u0 hu₂.2.1 hu₂.2.2.1 hu₂.2.2.2.1 hu₂.2.2.2.2 hordu2
  ·

    refine ((hcusp v haff).2).elim fun c hc => ?_
    have hθ : ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) := by
      intro f u' hfu
      have hfα : f = α u' := Subtype.ext (hfu.trans (hα_coe u').symm)
      rw [hfα]
      exact hβ_coe u'
    refine (ModularCurve.XHDRModelAtP.exists_unit_pair_divisor_oneSidedLaws_jump_prolongationDatum_of_isModel_of_nodeValueLaw
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hθ hα_coe hTD hmodel hNV hcompat hcompat').elim
      fun u₁ hu₁ => hu₁.elim fun u₂ hu₂ => hu₂.elim fun D₁ hD₁' => hD₁'.elim fun D₂ hall => ?_
    have hD₂ : ∀ W, D₂ W = W.ord u₂ := hall.2.1
    refine hall.2.2.2.2.1.elim fun h₂u hu₂props => ?_
    have hres2u : Rpd.R₂.residue ⟨u₂, h₂u⟩ ≠ 0 := hu₂props.1
    have hinv2 : u₂⁻¹ ∈ Rpd.R₂.integers := hu₂props.2.1
    have hone := hu₂props.2.2.2 c hc.1
    have hjump := hall.2.2.2.2.2 g hgne
    have hu2ne : u₂ ≠ 0 := ne_zero_of_residue_ne_zero Rpd.R₂ h₂u hres2u
    refine hjump.elim fun m hm' => hm'.elim fun j hj' => ?_
    have hm : m ≠ 0 := hj'.1
    refine hj'.2.elim fun h₁F hresF₁ => ?_
    refine (UnitCalc.pow_mul_zpow_mem Rpd.R₂ hg h₂u hres2u hinv2 m j).elim fun h₂F hresF₂eq => ?_
    have hresF₂ : Rpd.R₂.residue ⟨g ^ m * u₂ ^ j, h₂F⟩ ≠ 0 :=
      UnitCalc.residue_pow_mul_zpow_ne_zero Rpd.R₂ hg hg0 h₂u hres2u hinv2 m j h₂F
    have hgmune : g ^ m * u₂ ^ j ≠ 0 := mul_ne_zero (pow_ne_zero _ hgne) (zpow_ne_zero _ hu2ne)
    refine (HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (g ^ m * u₂ ^ j) hgmune).elim fun DF hDF' => ?_
    have hDF : ∀ W, DF W = W.ord (g ^ m * u₂ ^ j) := hDF'.1
    have hfib : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ c → DF W = j * D₂ W := by
      intro W hW
      rw [hDF W, hD₂ W, ord_pow_mul_zpow W hgne hu2ne, hV W (hW.trans hc.2), mul_zero, zero_add]
    have hCL : Rpd.CuspLawZero (θ.toAlgHom.comp α) hβ δ := hmodel.2.2.2
    have hrel := ord_residue_snd_eq_mul_of_cuspLawZero Rpd (θ.toAlgHom.comp α) hβ δ hCL h₁F h₂F hresF₁ hresF₂ DF hDF h₂u D₂ c hc.1
      hone j hfib
    have hmul := UnitCalc.ord_residue_pow_mul_zpow Rpd.R₂ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ c) hg hg0 h₂u hres2u hinv2 m j h₂F
    rw [hmul] at hrel
    have hzero : (m : ℤ) * (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ c).ord (Rpd.R₂.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0 := by
      linarith
    have hc2 : Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ c = v := hc.2
    rw [hc2] at hzero
    rcases mul_eq_zero.mp hzero with h0 | h0
    · exact absurd (by exact_mod_cast h0) hm
    · exact h0

end FixReadAux

namespace FixReadAux

theorem fst_regular
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)
    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS)
    (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
    (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers) (hg0 : Rpd.R₁.residue ⟨g, hg⟩ ≠ 0)
    (v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v) (haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v) (hnode : ∀ s ∈ SS, v ≠ s.1)
    (hV : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord g) :
    0 ≤ v.ord (Rpd.R₁.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hgne : g ≠ 0 := ne_zero_of_residue_ne_zero Rpd.R₁ hg hg0
  have hff := frame_facts p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hβ_coe hTD hmodel
    hO hRL hNV hθgal hcusp hcompat hcompat'
  have hvss : v ∉ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p := fun hv => by
    have himg := ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq (ResidueField ↥A) p (ΓN p M H hpM)
    have hv' : v ∈ qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p '' ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p := by
      rw [himg]; exact hv
    exact hv'.elim fun w hw => hnode (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p w, w)
      ((hSS _).mpr (frob_mk_mem_ssNodePairsQExp hw.1)) hw.2.symm
  refine (exists_oggUnit Rpd).elim fun x hx' => hx'.elim fun u hu' => hu'.elim fun h₁ hu => ?_
  have hx := hu.1
  have hucoe := hu.2.1
  have hres := hu.2.2.1
  have hres0 := hu.2.2.2
  have hune : u ≠ 0 := ne_zero_of_residue_ne_zero Rpd.R₁ h₁ hres0
  have hinv : u⁻¹ ∈ Rpd.R₁.integers := inv_mem_of_residue_ne_zero Rpd.R₁ h₁ hres0
  have hordu := (ord_residue_oggUnit_eq_zero_and_hasValue_zero Rpd hx hres).1 v hvss haff
  have hvan := (ord_residue_oggUnit_eq_zero_and_hasValue_zero Rpd hx hres).2
  have hucusp : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord u ≠ 0 →
      ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V) :=
    fun V hVu => hff.2.1 V
      (ModularCurve.JHPlaceSpecialization.isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries p M H hpM A u hucoe V hVu)
  have hssne := ModularCurve.nonempty_ssPlacesQExp (M / p) (ΓN p M H hpM)
    (gamma1_le_gammaH _ _) (CohCarrier.GammaH_le_Gamma0 _) p
    (fun h => hpM2 (by rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h)) (ResidueField ↥A)
  refine hssne.elim fun y hy => ?_
  have hs : (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y, y) ∈ SS := (hSS _).mpr (frob_mk_mem_ssNodePairsQExp hy)
  have hs1 : qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p := by
    have himg := ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq (ResidueField ↥A) p (ΓN p M H hpM)
    exact himg ▸ Set.mem_image_of_mem _ hy
  have hsep : ∀ h₂ : u ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u, h₂⟩ = 0 :=
    ModularCurve.JHPlaceSpecialization.ProlongationDatum.residue_snd_eq_zero_of_residue_fst_hasValue_zero_of_nodeValueLaw
      p M H hpM A θ α (θ.toAlgHom.comp α) hα hβ δ SS Psp Rpd hNV u h₁ hres0 _ hs
      (fun V hVu hboth => hucusp V hVu (hboth.1 ▸ isAffinePlace_of_mem_ssPlacesQExp hs1))
      (hvan _ hs1)
  refine (AlgebraicCurve.RegularProlongation.exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero
    A _ _ Rpd.R₂ u hune hsep g hgne).elim fun m hm' => hm'.elim fun j hj' => ?_
  have hm : m ≠ 0 := hj'.1
  refine hj'.2.elim fun h₂F hresF₂ => ?_
  refine (UnitCalc.pow_mul_zpow_mem Rpd.R₁ hg h₁ hres0 hinv m j).elim fun h₁F hresF₁eq => ?_
  have hresF₁ : Rpd.R₁.residue ⟨g ^ m * u ^ j, h₁F⟩ ≠ 0 :=
    UnitCalc.residue_pow_mul_zpow_ne_zero Rpd.R₁ hg hg0 h₁ hres0 hinv m j h₁F

  have hVF : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord (g ^ m * u ^ j) := by
    intro V hVv
    have hVu : V.ord u = 0 := by
      by_contra h
      exact hucusp V h (hVv ▸ haff)
    rw [ord_pow_mul_zpow V hgne hune, hVu, mul_zero, add_zero]
    exact mul_nonneg (Int.natCast_nonneg m) (hV V hVv)
  have hreg := (hRL.1 (g ^ m * u ^ j) h₁F h₂F v hfix haff hVF).1 hresF₁
  rw [UnitCalc.ord_residue_pow_mul_zpow Rpd.R₁ v hg hg0 h₁ hres0 hinv m j h₁F, hordu, mul_zero, add_zero] at hreg
  have hmpos : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  by_contra hneg
  exact absurd hreg (not_le.mpr (mul_neg_of_pos_of_neg hmpos (not_le.mp hneg)))

theorem snd_regular
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)
    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS)
    (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
    (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers) (hg0 : Rpd.R₂.residue ⟨g, hg⟩ ≠ 0)
    (v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v) (haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v) (hnode : ∀ s ∈ SS, v ≠ s.2)
    (hV : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → 0 ≤ V.ord g) :
    0 ≤ v.ord (Rpd.R₂.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hgne : g ≠ 0 := ne_zero_of_residue_ne_zero Rpd.R₂ hg hg0
  have hff := frame_facts p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hβ_coe hTD hmodel
    hO hRL hNV hθgal hcusp hcompat hcompat'
  have hpMp : ¬ p ∣ M / p := fun h => hpM2 (by rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h)
  have hbij := ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (ΓN p M H hpM)
  have hcomm : ∀ w : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (δ w) = δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p w) :=
    fun w => (congrArg (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p) (hδ w)).trans
      ((ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpMp
        (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) w).trans (hδ _).symm)
  have hkey : δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p
      (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v)) = v := by
    have h : qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v)) = v := hfix
    rw [hcomm] at h
    exact h
  have hfix' : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v) := by
    show qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v))) = _
    rw [hkey]
  have haff' := (ModularCurve.JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
    p M H hpM A hA).1 v haff
  have hvss : v ∉ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p := fun hv =>
    hnode (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v, v) ((hSS _).mpr (frob_mk_mem_ssNodePairsQExp hv)) rfl
  have hfibre : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα V = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v →
        Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v := by
    intro V hV1
    rcases hTD V with h | h
    · rw [hV1] at h
      exact (hbij.1 h).symm
    · rw [hV1] at h
      rw [← h, hkey]
  refine (exists_oggUnit Rpd).elim fun x hx' => hx'.elim fun u hu' => hu'.elim fun h₁ hu => ?_
  have hordu := (ord_residue_oggUnit_eq_zero_and_hasValue_zero Rpd hu.1 hu.2.2.1).1 v hvss haff
  have hucusp : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord u ≠ 0 →
      ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V) :=
    fun V hVu => hff.2.1 V
      (ModularCurve.JHPlaceSpecialization.isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries p M H hpM A u hu.2.1 V hVu)
  have hθ : ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
      ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro f u' hfu
    have hfα : f = α u' := Subtype.ext (hfu.trans (hα_coe u').symm)
    rw [hfα]
    exact hβ_coe u'
  have hAL := ModularCurve.algEquiv_apply_eq_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_of_qExpand_of_arithmeticGalois_comm
    p M H hpM hpM2 hHp hj θ hθ hθgal u hu.2.1
  refine (exists_sndUnit Rpd h₁ hu.2.2.2 hAL).elim fun u₂ hu₂' => hu₂'.elim fun h₂u hu₂ => ?_
  have hordu2 : v.ord (Rpd.R₂.residue ⟨u₂, h₂u⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0 := by rw [hu₂.1]; exact hordu
  have hres2u0 : Rpd.R₂.residue ⟨u₂, h₂u⟩ ≠ 0 := by rw [hu₂.1]; exact hu.2.2.2
  have hinv2 := hu₂.2.1
  have hu2ne := hu₂.2.2.1
  have hu2R1 := hu₂.2.2.2.1
  have hordV2 := hu₂.2.2.2.2

  refine (AlgebraicCurve.RegularProlongation.exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero
    A _ _ Rpd.R₁ u₂ hu2ne hu2R1 g hgne).elim fun m hm' => hm'.elim fun j hj' => ?_
  have hm : m ≠ 0 := hj'.1
  refine hj'.2.elim fun h₁F hresF₁ => ?_
  refine (UnitCalc.pow_mul_zpow_mem Rpd.R₂ hg h₂u hres2u0 hinv2 m j).elim fun h₂F hresF₂eq => ?_
  have hresF₂ : Rpd.R₂.residue ⟨g ^ m * u₂ ^ j, h₂F⟩ ≠ 0 := UnitCalc.residue_pow_mul_zpow_ne_zero Rpd.R₂ hg hg0 h₂u hres2u0 hinv2 m j h₂F
  have hVF : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα V = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v → 0 ≤ V.ord (g ^ m * u₂ ^ j) := by
    intro V hVv
    have hVu : V.ord u = 0 := by
      by_contra h
      exact hucusp V h (hVv ▸ haff')
    rw [ord_pow_mul_zpow V hgne hu2ne, hordV2 V, hVu, neg_zero, mul_zero, add_zero]
    exact mul_nonneg (Int.natCast_nonneg m) (hV V (hfibre V hVv))
  have hreg := (hRL.1 (g ^ m * u₂ ^ j) h₁F h₂F _ hfix' haff' hVF).2 hresF₂
  rw [hkey, UnitCalc.ord_residue_pow_mul_zpow Rpd.R₂ v hg hg0 h₂u hres2u0 hinv2 m j h₂F, hordu2, mul_zero, add_zero] at hreg
  have hmpos : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  by_contra hneg
  exact absurd hreg (not_le.mpr (mul_neg_of_pos_of_neg hmpos (not_le.mp hneg)))

end FixReadAux

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)
    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS)
    (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :

    (∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.1) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord g) →
        0 ≤ v.ord (Rpd.R₁.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∧
    (∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.2) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → 0 ≤ V.ord g) →
        0 ≤ v.ord (Rpd.R₂.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
  exact ⟨fun g hg hg0 v hfix haff hnode hV => FixReadAux.fst_regular p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hβ_coe hTD hmodel hO hRL hNV hθgal hcusp hcompat hcompat' g hg hg0 v hfix haff hnode hV,
    fun g hg hg0 v hfix haff hnode hV => FixReadAux.snd_regular p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hβ_coe hTD hmodel hO hRL hNV hθgal hcusp hcompat hcompat' g hg hg0 v hfix haff hnode hV⟩

end S_ModularCurve_XHDRModelAtP_ord_residue_nonneg_of_fixed_of_isAffinePlace_of_forall_ord_nonneg_fst_and_snd_of_offDiag
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_ord_residue_nonneg_of_fixed_of_isAffinePlace_of_forall_ord_nonneg_fst_and_snd_of_offDiag (solution)
