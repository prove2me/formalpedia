-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_smul_mem_integers_residue_ne_zero_of_isGoodDiv_of_admissible_of_unit_of_cusp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/72cd6156-1248-584e-a360-9bd22af19de9

import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_oneSidedDivisorLaw_and_oneSidedCuspLaw_of_isModel_of_unit
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_smul_mem_integers_and_residue_ne_zero_or
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Theorems.Thm_ModularCurve_nonempty_ssPlacesQExp
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_fixed_of_mem_ssPlacesQExp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_smul_mem_integers_residue_ne_zero_of_isGoodDiv_of_admissible_of_unit_of_cusp
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing"
p2m_attr_erase "instance" "TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt"
p2m_attr_erase "simp" "ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP"
p2m_attr_erase "simp" "ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups Classical

set_option linter.unusedSectionVars false

set_option quotPrecheck false
set_option hygiene false in
local notation "κ" => ResidueField ↥A
set_option hygiene false in
local notation "FM" => ↥(xHFunctionFieldBar M H)
set_option hygiene false in
local notation "Fb" => JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)
set_option hygiene false in
local notation "Φ" => qExpFrobeniusPlaceModL (ResidueField ↥A) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM) p
set_option hygiene false in
local notation "FixedH" => JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A)
set_option hygiene false in
local notation "AffH" => JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)
set_option hygiene false in
local notation "InftySide" => JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)
set_option hygiene false in
local notation "ZeroSide" => JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)

namespace CommonGaussUnitH

section PlaceHelpers

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem degree_pos_of_nonneg (X : Divisor K F) (hdeg : ∀ v : Place K F, v.deg = 1) (h0 : ∀ v, 0 ≤ X v)
    (v₀ : Place K F) (h1 : 0 < X v₀) : 0 < Divisor.degree X := by
  have hsum : AlgebraicCurve.Divisor.degree X = ∑ v ∈ X.support, X v := by
    simp only [AlgebraicCurve.Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum,
      AddMonoidHom.coe_mulRight, hdeg, Nat.cast_one, mul_one]
  rw [hsum]
  exact Finset.sum_pos' (fun v _ => h0 v) ⟨v₀, Finsupp.mem_support_iff.mpr h1.ne', h1⟩

theorem mapDomain_apply_eq_zero {ι ι' : Type*} (f : ι → ι') (D : ι →₀ ℤ) (w : ι')
    (h : ∀ i, f i = w → D i = 0) : Finsupp.mapDomain f D w = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [Finsupp.single_apply]
  split_ifs with hi
  · exact h i hi
  · rfl

theorem ord_algebraMap' {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hc' : algebraMap K F c ≠ 0 := (_root_.map_ne_zero (algebraMap K F)).mpr hc
  have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
    ⟨⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ hc'),
      Subtype.ext (by simpa using inv_mul_cancel₀ hc')⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rwa [hu] at this

theorem ord_smul {c : K} (hc : c ≠ 0) (x : F) : v.ord (c • x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Algebra.smul_def, v.ord_mul ((_root_.map_ne_zero _).mpr hc) hx, ord_algebraMap' v hc, zero_add]

theorem hasValue_zero : v.HasValue (0 : F) 0 := by
  simpa using v.hasValue_algebraMap (0 : K)

theorem ord_sub_pos_of_hasValue {g : F} {a : K} (h : v.HasValue g a) (hne : g - algebraMap K F a ≠ 0) :
    0 < v.ord (g - algebraMap K F a) := by
  obtain ⟨hg, hres⟩ := h
  have hmem : g - algebraMap K F a ∈ v.toValuationSubring := sub_mem hg (v.algebraMap_mem' a)
  have hmax : (⟨_, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring)
        = ⟨g, hg⟩ - ⟨algebraMap K F a, v.algebraMap_mem' a⟩ := rfl
    rw [this, map_sub, hres, sub_eq_zero]
    rfl
  have h0 := v.ord_nonneg_of_mem hmem
  rcases h0.lt_or_eq with hpos | h0
  · exact hpos
  · exfalso
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hne hπ
    rw [← h0, zpow_zero, mul_one] at hu
    apply (IsLocalRing.mem_maximalIdeal _).mp hmax
    have : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
    rw [this]; exact Units.isUnit u

theorem ord_pos_of_hasValue_zero {g : F} (h : v.HasValue g 0) (hne : g ≠ 0) : 0 < v.ord g := by
  have := ord_sub_pos_of_hasValue v h (by simpa using hne)
  simpa using this

end PlaceHelpers

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

theorem deg_eq_one_Fb (hpM2 : ¬ p ^ 2 ∣ M) (w : Place κ Fb) : w.deg = 1 :=
  (Place.deg_eq_one_iff_surjective_algebraMap_residueField w).mpr
    ((JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
      p M H hpM hpM2 (ResidueField ↥A)).2.2 w)

theorem exists_orderDivisor (hpM2 : ¬ p ^ 2 ∣ M) (g : Fb) (hg : g ≠ 0) :
    ∃ Δ : Divisor κ Fb, (∀ v : Place κ Fb, Δ v = v.ord g) ∧ Divisor.degree Δ = 0 := by
  haveI : HasPrincipalDivisors κ Fb :=
    (JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
      p M H hpM hpM2 (ResidueField ↥A)).1
  exact HasPrincipalDivisors.exists_divisor (K := κ) g hg

theorem fixed_frob_iff (δ : Place κ Fb → Place κ Fb)
    (hcomm : ∀ v, Φ (δ v) = δ (Φ v)) (hΦ : Function.Injective Φ) (v : Place κ Fb) :
    FixedH δ (Φ v) ↔ FixedH δ v := by
  unfold JHPlaceSpecialization.Fixed
  rw [← hcomm (Φ v)]
  exact hΦ.eq_iff

theorem fixed_delta_iff (δ : Place κ Fb → Place κ Fb)
    (hcomm : ∀ v, Φ (δ v) = δ (Φ v)) (hδ : Function.Injective δ) (v : Place κ Fb) :
    FixedH δ (δ v) ↔ FixedH δ v := by
  unfold JHPlaceSpecialization.Fixed
  rw [hcomm v, hcomm (δ (Φ v))]
  exact hδ.eq_iff

theorem affine_of_ss {y : Place κ Fb} (hy : y ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) :
    AffH y := by
  obtain ⟨x, a, hx, hv, -⟩ := hy
  exact ⟨x, a, hx, hv⟩

section Frame

variable {Psp : JHPlaceSpecialization p M H hpM A} {θ : FM ≃ₐ[AlgebraicClosure ℚ] FM}
  {α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] FM}
  {hα : α.IsIntegral} {hβ : β.IsIntegral} {δ : Place κ Fb → Place κ Fb}

theorem good_apply_eq_zero_of_fixed_fst (hcomm : ∀ v, Φ (δ v) = δ (Φ v)) (hΦ : Function.Injective Φ)
    (D : Divisor (AlgebraicClosure ℚ) FM) (hgood : Psp.IsGoodDiv α β hα hβ δ D)
    (V' : Place (AlgebraicClosure ℚ) FM) (hfix : FixedH δ (Psp.reduceFst α hα V')) : D V' = 0 := by
  by_contra hne
  rcases hgood V' (Finsupp.mem_support_iff.mpr hne) with hst | hst
  · exact hst.2 hfix
  · rw [hst.1, fixed_frob_iff δ hcomm hΦ] at hfix
    exact hst.2 hfix

theorem good_apply_eq_zero_of_fixed_snd (hcomm : ∀ v, Φ (δ v) = δ (Φ v)) (hΦ : Function.Injective Φ)
    (hδi : Function.Injective δ)
    (D : Divisor (AlgebraicClosure ℚ) FM) (hgood : Psp.IsGoodDiv α β hα hβ δ D)
    (V' : Place (AlgebraicClosure ℚ) FM) (hfix : FixedH δ (Psp.reduceSnd β hβ δ V')) : D V' = 0 := by
  by_contra hne
  rcases hgood V' (Finsupp.mem_support_iff.mpr hne) with hst | hst
  · rw [← hst.1, fixed_delta_iff δ hcomm hδi, fixed_frob_iff δ hcomm hΦ] at hfix
    exact hst.2 hfix
  · exact hst.2 hfix

theorem count_fst (hpM2 : ¬ p ^ 2 ∣ M) (hcomm : ∀ v, Φ (δ v) = δ (Φ v)) (hΦ : Function.Injective Φ)
    (hssne : (ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p).Nonempty)
    (hssfix : ∀ y, y ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p → FixedH δ y)
    (SS : Finset (Place κ Fb × Place κ Fb))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)
    (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ) (hRL : Rpd.RegularityLaw α β hα hβ δ SS)
    (hcuspF : ∀ w : Place κ Fb, ¬ AffH w → ∃ C, InftySide C ∧ Psp.reduceFst α hα C = w)
    (OS1 : ∀ (f : FM) (h₁ : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
        ∀ v : Place κ Fb, ¬ FixedH δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) v = v.ord (Rpd.R₁.residue ⟨f, h₁⟩ : Fb))
    (OS2 : ∀ (f : FM) (h₁ : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
        ∀ c : Place (AlgebraicClosure ℚ) FM, InftySide c →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D.filter InftySide) (Psp.reduceFst α hα c) =
            (Psp.reduceFst α hα c).ord (Rpd.R₁.residue ⟨f, h₁⟩ : Fb))
    (D : Divisor (AlgebraicClosure ℚ) FM) (hgood : Psp.IsGoodDiv α β hα hβ δ D)
    (hdeg0 : Divisor.degree (Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D)) = 0)
    (g : FM) (h₁ : g ∈ Rpd.R₁.integers) (h₂ : g ∈ Rpd.R₂.integers)
    (hr₁ : Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0) (hr₂ : Rpd.R₂.residue ⟨g, h₂⟩ = 0) (hDg : ∀ W, D W = W.ord g) : False := by
  obtain ⟨Dg, hDg', hDg0⟩ := exists_orderDivisor hpM2 (Rpd.R₁.residue ⟨g, h₁⟩ : Fb) hr₁
  obtain ⟨P, hP⟩ : ∃ P : Divisor κ Fb, P = Dg - Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) := ⟨_, rfl⟩
  have hPdeg : Divisor.degree P = 0 := by rw [hP, map_sub, hDg0, hdeg0, sub_self]
  have hP_apply : ∀ v, P v = Dg v - Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) v := fun v => by
    rw [hP, Finsupp.sub_apply]

  have hstrict0 : ∀ v : Place κ Fb, FixedH δ v → Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) v = 0 := by
    intro v hv
    refine mapDomain_apply_eq_zero _ _ _ fun V hV => ?_
    show (D.filter (Psp.IsStrictFst α β hα hβ δ)) V = 0
    rw [Finsupp.filter_apply]
    split_ifs with hst
    · exact absurd (by rw [hV]; exact hv) hst.2
    · rfl

  have hnopole : ∀ v : Place κ Fb, FixedH δ v → ∀ V : Place (AlgebraicClosure ℚ) FM, Psp.reduceFst α hα V = v → 0 ≤ V.ord g := by
    intro v hv V hVv
    have h0 := good_apply_eq_zero_of_fixed_fst hcomm hΦ D hgood V (by rw [hVv]; exact hv)
    rw [hDg] at h0
    exact le_of_eq h0.symm

  have hPnn : ∀ v, 0 ≤ P v := by
    intro v
    rw [hP_apply]
    by_cases hv : FixedH δ v
    · rw [hstrict0 v hv, sub_zero, hDg']
      by_cases haff : AffH v
      · exact (hRL.1 g h₁ h₂ v hv haff (hnopole v hv)).1 hr₁
      · obtain ⟨C, hC, hCv⟩ := hcuspF v haff
        have key := OS2 g h₁ hr₁ D hDg C hC
        rw [hCv] at key
        have hz : Finsupp.mapDomain (Psp.reduceFst α hα) (D.filter InftySide) v = 0 :=
          mapDomain_apply_eq_zero _ _ _ fun V hV => by
            rw [Finsupp.filter_apply]
            split_ifs
            · exact good_apply_eq_zero_of_fixed_fst hcomm hΦ D hgood V (by rw [hV]; exact hv)
            · rfl
        rw [← key, hz]
    · rw [hDg', ← OS1 g h₁ hr₁ D hDg v hv, sub_self]

  obtain ⟨y, hy⟩ := hssne
  have hs : (Φ y, y) ∈ SS := (hSS _).mpr (frob_mk_mem_ssNodePairsQExp hy)
  have hfix1 : FixedH δ (Φ y) := (fixed_frob_iff δ hcomm hΦ y).mpr (hssfix y hy)
  obtain ⟨cc, hcc₁, hcc₂⟩ := hRL.2 g h₁ h₂ _ hs (hnopole _ hfix1)
  have hcc0 : cc = 0 := by
    have h' : (Φ y, y).2.HasValue ((0 : Fb)) cc := by rw [← hr₂]; exact hcc₂
    exact (h'.unique (hasValue_zero _))
  rw [hcc0] at hcc₁
  have hpos : 0 < (Φ y).ord (Rpd.R₁.residue ⟨g, h₁⟩ : Fb) := ord_pos_of_hasValue_zero _ hcc₁ hr₁
  have hPpos : 0 < P (Φ y) := by
    rw [hP_apply, hstrict0 _ hfix1, sub_zero, hDg']
    exact hpos
  have hdegpos := degree_pos_of_nonneg P (deg_eq_one_Fb hpM2) hPnn (Φ y) hPpos
  rw [hPdeg] at hdegpos
  exact lt_irrefl _ hdegpos

theorem count_snd (hpM2 : ¬ p ^ 2 ∣ M) (hcomm : ∀ v, Φ (δ v) = δ (Φ v)) (hΦ : Function.Injective Φ) (hδi : Function.Injective δ)
    (haffΦ : ∀ v : Place κ Fb, AffH v → AffH (Φ v))
    (hssne : (ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p).Nonempty)
    (hssfix : ∀ y, y ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p → FixedH δ y)
    (SS : Finset (Place κ Fb × Place κ Fb))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)
    (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ) (hRL : Rpd.RegularityLaw α β hα hβ δ SS)
    (hcuspS : ∀ w : Place κ Fb, ¬ AffH w → ∃ C, ZeroSide C ∧ Psp.reduceSnd β hβ δ C = w)
    (OS1 : ∀ (f : FM) (h₂ : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
        ∀ v : Place κ Fb, ¬ FixedH δ v →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D) v = v.ord (Rpd.R₂.residue ⟨f, h₂⟩ : Fb))
    (OS2 : ∀ (f : FM) (h₂ : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
        ∀ c : Place (AlgebraicClosure ℚ) FM, ZeroSide c →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (D.filter ZeroSide) (Psp.reduceSnd β hβ δ c) =
            (Psp.reduceSnd β hβ δ c).ord (Rpd.R₂.residue ⟨f, h₂⟩ : Fb))
    (D : Divisor (AlgebraicClosure ℚ) FM) (hgood : Psp.IsGoodDiv α β hα hβ δ D)
    (hdeg0 : Divisor.degree (Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D)) = 0)
    (g : FM) (h₁ : g ∈ Rpd.R₁.integers) (h₂ : g ∈ Rpd.R₂.integers)
    (hr₁ : Rpd.R₁.residue ⟨g, h₁⟩ = 0) (hr₂ : Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0) (hDg : ∀ W, D W = W.ord g) : False := by
  obtain ⟨Dg, hDg', hDg0⟩ := exists_orderDivisor hpM2 (Rpd.R₂.residue ⟨g, h₂⟩ : Fb) hr₂
  obtain ⟨P, hP⟩ : ∃ P : Divisor κ Fb, P = Dg - Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D) := ⟨_, rfl⟩
  have hPdeg : Divisor.degree P = 0 := by rw [hP, map_sub, hDg0, hdeg0, sub_self]
  have hP_apply : ∀ v, P v = Dg v - Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D) v := fun v => by
    rw [hP, Finsupp.sub_apply]
  have hstrict0 : ∀ v : Place κ Fb, FixedH δ v → Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D) v = 0 := by
    intro v hv
    refine mapDomain_apply_eq_zero _ _ _ fun V hV => ?_
    show (D.filter (Psp.IsStrictSnd α β hα hβ δ)) V = 0
    rw [Finsupp.filter_apply]
    split_ifs with hst
    · exact absurd (by rw [hV]; exact hv) hst.2
    · rfl

  have hnopole : ∀ v : Place κ Fb, FixedH δ v → ∀ V : Place (AlgebraicClosure ℚ) FM, Psp.reduceFst α hα V = v → 0 ≤ V.ord g := by
    intro v hv V hVv
    have h0 := good_apply_eq_zero_of_fixed_fst hcomm hΦ D hgood V (by rw [hVv]; exact hv)
    rw [hDg] at h0
    exact le_of_eq h0.symm
  have hPnn : ∀ v, 0 ≤ P v := by
    intro v
    rw [hP_apply]
    by_cases hv : FixedH δ v
    · rw [hstrict0 v hv, sub_zero, hDg']
      by_cases haff : AffH v
      · have hvfix' : FixedH δ (Φ v) := (fixed_frob_iff δ hcomm hΦ v).mpr hv
        have hvw : δ (Φ (Φ v)) = v := by
          rw [← hcomm (Φ v)]
          exact hv
        have key := (hRL.1 g h₁ h₂ (Φ v) hvfix' (haffΦ v haff) (hnopole (Φ v) hvfix')).2 hr₂
        rwa [hvw] at key
      · obtain ⟨C, hC, hCv⟩ := hcuspS v haff
        have key := OS2 g h₂ hr₂ D hDg C hC
        rw [hCv] at key
        have hz : Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (D.filter ZeroSide) v = 0 :=
          mapDomain_apply_eq_zero _ _ _ fun V hV => by
            rw [Finsupp.filter_apply]
            split_ifs
            · exact good_apply_eq_zero_of_fixed_snd hcomm hΦ hδi D hgood V (by rw [hV]; exact hv)
            · rfl
        rw [← key, hz]
    · rw [hDg', ← OS1 g h₂ hr₂ D hDg v hv, sub_self]

  obtain ⟨y, hy⟩ := hssne
  have hs : (Φ y, y) ∈ SS := (hSS _).mpr (frob_mk_mem_ssNodePairsQExp hy)
  have hfixy : FixedH δ y := hssfix y hy
  have hfix1 : FixedH δ (Φ y) := (fixed_frob_iff δ hcomm hΦ y).mpr hfixy
  obtain ⟨cc, hcc₁, hcc₂⟩ := hRL.2 g h₁ h₂ _ hs (hnopole _ hfix1)
  have hcc0 : cc = 0 := by
    have h' : (Φ y, y).1.HasValue ((0 : Fb)) cc := by rw [← hr₁]; exact hcc₁
    exact (h'.unique (hasValue_zero _))
  rw [hcc0] at hcc₂
  have hpos : 0 < y.ord (Rpd.R₂.residue ⟨g, h₂⟩ : Fb) := ord_pos_of_hasValue_zero _ hcc₂ hr₂
  have hPpos : 0 < P y := by
    rw [hP_apply, hstrict0 _ hfixy, sub_zero, hDg']
    exact hpos
  have hdegpos := degree_pos_of_nonneg P (deg_eq_one_Fb hpM2) hPnn y hPpos
  rw [hPdeg] at hdegpos
  exact lt_irrefl _ hdegpos

end Frame

end CommonGaussUnitH

open CommonGaussUnitH in
set_option maxHeartbeats 3200000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd β hβ δ C) =
            (Psp.reduceSnd β hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd β hβ δ C = w))

    (f : ↥(xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hDf : ∀ V, D V = V.ord f)
    (hgood : Psp.IsGoodDiv α β hα hβ δ D)
    (hadm : Psp.glueData α β hα hβ δ SS D ∈ GluingData.admissible SS) :
    ∃ (c : AlgebraicClosure ℚ) (_ : c ≠ 0)
      (h₁ : c • f ∈ Rpd.R₁.integers) (h₂ : c • f ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨c • f, h₁⟩ ≠ 0 ∧ Rpd.R₂.residue ⟨c • f, h₂⟩ ≠ 0 := by
  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have := Nat.div_mul_cancel hpM
    rw [hk] at this
    rw [← this]; ring
  have hcomm : ∀ v, Φ (δ v) = δ (Φ v) := by
    intro v
    rw [hδ v, hδ (Φ v)]
    exact ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN
      (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) v
  have hδi : Function.Injective δ := fun v w hvw => by
    rw [hδ v, hδ w] at hvw
    exact MulAction.injective _ hvw
  have hΦ : Function.Injective Φ :=
    (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).1
  have haffΦ := (JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
    p M H hpM A hA).1
  have hssfix : ∀ y, y ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p → FixedH δ y :=
    fun y hy => ModularCurve.JHPlaceSpecialization.fixed_of_mem_ssPlacesQExp p M H hpM hpM2 A pb hpb δ hδ y hy
  have hssne : (ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p).Nonempty :=
    ModularCurve.nonempty_ssPlacesQExp (M / p) (JHNeronObjectAtP.ΓN p M H hpM)
      (ModularCurve.Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM)) (CohCarrier.GammaH_le_Gamma0 (infSubgroup p M H hpM))
      p hpN (ResidueField ↥A)

  obtain ⟨OS1F, OS1S, OS2F, OS2S⟩ :=
    ModularCurve.JHPlaceSpecialization.ProlongationDatum.oneSidedDivisorLaw_and_oneSidedCuspLaw_of_isModel_of_unit p M H hpM hpM2 hHp A hA θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hUnit

  have hdeg0 : Divisor.degree (Psp.glueData α β hα hβ δ SS D).1 = 0 ∧ Divisor.degree (Psp.glueData α β hα hβ δ SS D).2.1 = 0 :=
    ⟨Divisor.mem_degZero.mp hadm.1, Divisor.mem_degZero.mp hadm.2.1⟩

  obtain ⟨c, hc, h₁, h₂, hor⟩ :=
    AlgebraicCurve.RegularProlongation.exists_smul_mem_integers_and_residue_ne_zero_or Rpd.R₁ Rpd.R₂ hf
  have hDc : ∀ W, D W = W.ord (c • f) := fun W => by rw [ord_smul W hc, hDf]
  refine ⟨c, hc, h₁, h₂, ?_, ?_⟩
  · rcases hor with hr₁ | hr₂
    · exact hr₁
    · by_contra hr₁
      exact count_snd hpM2 hcomm hΦ hδi haffΦ hssne hssfix SS hSS Rpd hRL (fun w hw => (hcusp w hw).2) OS1S OS2S
        D hgood hdeg0.2 (c • f) h₁ h₂ hr₁ hr₂ hDc
  · rcases hor with hr₁ | hr₂
    · by_contra hr₂
      exact count_fst hpM2 hcomm hΦ hssne hssfix SS hSS Rpd hRL (fun w hw => (hcusp w hw).1) OS1F OS2F
        D hgood hdeg0.1 (c • f) h₁ h₂ hr₁ hr₂ hDc
    · exact hr₂

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_smul_mem_integers_residue_ne_zero_of_isGoodDiv_of_admissible_of_unit_of_cusp
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_smul_mem_integers_residue_ne_zero_of_isGoodDiv_of_admissible_of_unit_of_cusp (solution)
