-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.oneSidedSnd_laws_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/08938155-102e-51b6-b4c4-d597b57f5616

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_XHDRModelAtP_oneSidedFst_laws_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
import Theorems.Thm_ModularCurve_XHDRModelAtP_reduceSnd_ofAlgAut_symm_smul_eq_reduceFst_and_isStrictSnd_iff_isStrictFst_ofAlgAut_symm_smul_prolongationDatum
import Theorems.Thm_ModularCurve_diamondActionModL_apply_eq_self_of_coe_eq_coeffMap_modularUnitSeries
import Theorems.Thm_ModularCurve_XHDRModelAtP_isZeroSide_iff_isInftySide_smul_prolongationDatum
import Theorems.Thm_ModularCurve_algEquiv_apply_eq_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_of_qExpand_of_arithmeticGalois_comm
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_and_arithmeticGalois_comm_of_comp_w_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_algEquiv_eq_of_forall_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_AlgebraicCurve_Place_smul_restrictAlong
import Theorems.Thm_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_oneSidedSnd_laws_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ValuationSubring.instIsAlgClosedResidueField ModularCurve.TwoChart.isOpenImmersion_fInf ModularCurve.TwoChart.isOpenImmersion_ιFin ModularCurve.TwoChart.isOpenImmersion_ιInf ModularCurve.TwoChart.isOpenImmersion_fFin AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec ModularCurve.TwoChart.coe_jChartFin ModularCurve.TwoChart.ιFin_modelTo ModularCurve.TwoChart.ιInf_modelTo ModularCurve.TwoChart.ιInf_modelTo_assoc ModularCurve.TwoChart.coe_jInvChartInf"
p2m_attr_erase "simp" "ModularCurve.TwoChart.ιFin_modelTo_assoc AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace UXInst

theorem finiteIndex_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

theorem exists_transcendental_finiteDimensional_xHFunctionFieldBar (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) :
    ∃ x : xHFunctionFieldBar M H, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional
        (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (xHFunctionFieldBar M H)))
        (xHFunctionFieldBar M H) := by
  haveI := finiteIndex_GammaH M H
  exact ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H)

theorem essFiniteType_of_presentation {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  classical
  haveI := hfin
  let K₀ := IntermediateField.adjoin K ({x} : Set F)
  haveI : Module.Free K₀ F := Module.Free.of_divisionRing _ _
  let b := Module.finBasis K₀ F
  rw [← IntermediateField.fg_top_iff, IntermediateField.fg_def]
  refine ⟨insert x (Set.range b), (Set.finite_range b).insert x, ?_⟩
  refine le_antisymm le_top ?_
  intro y _
  have hy := b.sum_repr y
  rw [← hy]
  refine sum_mem fun j _ => ?_
  rw [Algebra.smul_def, IntermediateField.algebraMap_apply]
  refine mul_mem ?_ (IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ ⟨j, rfl⟩))
  exact IntermediateField.adjoin.mono K _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
    (b.repr y j).2

theorem isCurveOver_xHFunctionFieldBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    IsCurveOver (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) := by
  obtain ⟨x, hx, hfin⟩ := exists_transcendental_finiteDimensional_xHFunctionFieldBar M H
  haveI := hfin
  haveI : PerfectField
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (xHFunctionFieldBar M H))) :=
    PerfectField.ofCharZero
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (xHFunctionFieldBar M H)))
      (xHFunctionFieldBar M H) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact AlgebraicCurve.isCurveOver_of_transcendental hx hfin inferInstance

end UXInst

namespace C8Glue
set_option maxHeartbeats 3200000 in

open Classical in
theorem law2a (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (u u₂ : ↥(xHFunctionFieldBar M H)) (h₁ : u ∈ Rpd.R₁.integers) (h₂ : u₂ ∈ Rpd.R₂.integers)
    (D D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hres : Rpd.R₂.residue ⟨u₂, h₂⟩ = Rpd.R₁.residue ⟨u, h₁⟩)
    (hss : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), SemilinearAut.ofAlgAut θ.symm • (SemilinearAut.ofAlgAut θ • W) = W)
    (hss' : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), SemilinearAut.ofAlgAut θ • (SemilinearAut.ofAlgAut θ.symm • W) = W)
    (gδ : SemilinearAut (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ' : ∀ v, δ v = gδ • v)
    (hFixδ : ∀ v, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (gδ⁻¹ • v) ↔
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v)
    (hfix : gδ • (Rpd.R₁.residue ⟨u, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = Rpd.R₁.residue ⟨u, h₁⟩)
    (hD₂θ : ∀ W, D₂ W = D (SemilinearAut.ofAlgAut θ.symm • W))
    (hT1 : ∀ W, Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = δ (Psp.reduceFst α hα (SemilinearAut.ofAlgAut θ.symm • W)))
    (hT3 : ∀ W, Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (SemilinearAut.ofAlgAut θ.symm • W) = Psp.reduceFst α hα W ∧
      (Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W ↔ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (SemilinearAut.ofAlgAut θ.symm • W)))
    (L1a : ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D) v = v.ord (Rpd.R₁.residue ⟨u, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) :
    ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
  have hδinj : Function.Injective δ := by
    intro a b h; rw [hδ', hδ'] at h; exact smul_left_cancel _ h
  intro v hv
  have hθinj : Function.Injective (fun W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) => SemilinearAut.ofAlgAut θ • W) :=
    MulAction.injective _
  have ha : Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂ =
      Finsupp.mapDomain (SemilinearAut.ofAlgAut θ • ·) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D) := by
    ext W
    rw [show W = SemilinearAut.ofAlgAut θ • (SemilinearAut.ofAlgAut θ.symm • W) from (hss' W).symm,
      Finsupp.mapDomain_apply hθinj]
    simp only [JHPlaceSpecialization.sndDiv, JHPlaceSpecialization.fstDiv, Finsupp.filter_apply]
    have hiff := (hT3 (SemilinearAut.ofAlgAut θ • (SemilinearAut.ofAlgAut θ.symm • W))).2
    rw [hss] at hiff
    rw [hD₂θ, hss]
    by_cases hc : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (SemilinearAut.ofAlgAut θ.symm • W)
    · rw [if_pos (hiff.mpr hc), if_pos hc]
    · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]
  have hb : (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ ∘ (SemilinearAut.ofAlgAut θ • ·)) = (δ ∘ Psp.reduceFst α hα) := by
    funext W₀
    simp only [Function.comp_apply]
    rw [hT1, hss]
  rw [ha, ← Finsupp.mapDomain_comp, hb, Finsupp.mapDomain_comp]
  have hvw : v = δ (gδ⁻¹ • v) := by rw [hδ', smul_inv_smul]
  rw [hvw, Finsupp.mapDomain_apply hδinj]
  have hw : ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (gδ⁻¹ • v) :=
    fun h => hv ((hFixδ v).mp h)
  rw [L1a (gδ⁻¹ • v) hw, ← hvw, hres]
  have hord := SemilinearAut.ord_smul gδ (gδ⁻¹ • v) (Rpd.R₁.residue ⟨u, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
  rw [smul_inv_smul, hfix] at hord
  exact hord.symm

set_option maxHeartbeats 3200000 in

open Classical in
theorem law2b (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (u u₂ : ↥(xHFunctionFieldBar M H)) (h₁ : u ∈ Rpd.R₁.integers) (h₂ : u₂ ∈ Rpd.R₂.integers)
    (D D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hres : Rpd.R₂.residue ⟨u₂, h₂⟩ = Rpd.R₁.residue ⟨u, h₁⟩)
    (hss : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), SemilinearAut.ofAlgAut θ.symm • (SemilinearAut.ofAlgAut θ • W) = W)
    (hss' : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), SemilinearAut.ofAlgAut θ • (SemilinearAut.ofAlgAut θ.symm • W) = W)
    (hD₂θ' : ∀ W, D₂ W = D (SemilinearAut.ofAlgAut θ • W))
    (hT3i : ∀ W, Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (SemilinearAut.ofAlgAut θ.symm • W) = Psp.reduceFst α hα W)
    (hT2 : ∀ W, JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) W ↔
      JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) (SemilinearAut.ofAlgAut θ • W))
    (L1b : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) :
    ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
  intro Cz hCz
  have hθinj' : Function.Injective (fun W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) => SemilinearAut.ofAlgAut θ.symm • W) :=
    MulAction.injective _
  have ha' : D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) =
      Finsupp.mapDomain (SemilinearAut.ofAlgAut θ.symm • ·) (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) := by
    ext W
    rw [show W = SemilinearAut.ofAlgAut θ.symm • (SemilinearAut.ofAlgAut θ • W) from (hss W).symm,
      Finsupp.mapDomain_apply hθinj']
    simp only [Finsupp.filter_apply, hss]
    have hiff := hT2 W
    have e := hD₂θ' W
    generalize hW' : SemilinearAut.ofAlgAut θ • W = W' at hiff e ⊢
    by_cases hc : JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W'
    · rw [if_pos (hiff.mpr hc), if_pos hc]; exact e
    · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]
  have e1 : Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ)
      (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) =
      Finsupp.mapDomain (Psp.reduceFst α hα) (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) := by
    rw [ha', ← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun W _ => hT3i W
  have hc' : Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Cz = Psp.reduceFst α hα (SemilinearAut.ofAlgAut θ • Cz) := by
    have := hT3i (SemilinearAut.ofAlgAut θ • Cz)
    rwa [hss] at this
  have e2 := DFunLike.congr_fun e1 (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Cz)
  have t6 : (Finsupp.mapDomain (Psp.reduceFst α hα)
      (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Cz) =
      (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Cz).ord (Rpd.R₁.residue ⟨u, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := by
    rw [hc']
    exact L1b (SemilinearAut.ofAlgAut θ • Cz) ((hT2 Cz).mp hCz)
  exact e2.trans (t6.trans (congrArg (fun z => (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Cz).ord z) hres.symm))

end C8Glue

open C8Glue in
set_option maxHeartbeats 3200000 in
open Classical in
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

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

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

    (u : ↥(xHFunctionFieldBar M H))
    (hu : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p))
    (u₂ : ↥(xHFunctionFieldBar M H))
    (hu₂ : u₂ = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((p : ℕ) : AlgebraicClosure ℚ) ^ 12) * u⁻¹)
    (h₂ : u₂ ∈ Rpd.R₂.integers)
    (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hD₂ : ∀ W, D₂ W = W.ord u₂) :
    (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := by
    obtain ⟨xt, -, hfin⟩ := UXInst.exists_transcendental_finiteDimensional_xHFunctionFieldBar M H
    exact UXInst.essFiniteType_of_presentation hfin
  haveI hcurve : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := UXInst.isCurveOver_xHFunctionFieldBar M H
  obtain ⟨θ₁, hwgen₁, hθgal₁⟩ := ModularCurve.XHDRModelAtP.exists_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_and_arithmeticGalois_comm_of_comp_w_eq p M H hpM hj 𝔛
  have hθeq : θ = θ₁ := ModularCurve.XHDRModelAtP.algEquiv_eq_of_forall_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq p M H hpM hj 𝔛 θ θ₁ hwgen hwgen₁
  have hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f := by
    rw [hθeq]; exact hθgal₁
  have hAL : θ u = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((p : ℕ) : AlgebraicClosure ℚ) ^ 12) * u⁻¹ :=
    ModularCurve.algEquiv_apply_eq_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_of_qExpand_of_arithmeticGalois_comm p M H hpM hpM2 hHp hj θ hθ hθgal u hu
  have hp12 : (((p : ℕ) : AlgebraicClosure ℚ) ^ 12) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hu₂θ : u₂ = θ u := by rw [hu₂, hAL]
  have hθu₂ : θ u₂ = u := by
    rw [hu₂, map_mul, AlgEquiv.commutes, map_inv₀, hAL, mul_inv, ← mul_assoc, ← map_inv₀, ← map_mul,
      mul_inv_cancel₀ hp12, map_one, one_mul, inv_inv]
  have hu₂inv : u₂ = θ.symm u := by rw [← hθu₂, AlgEquiv.symm_apply_apply]
  obtain ⟨⟨x, hx, hx1, -⟩, -, -, -⟩ := ModularCurve.exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd p M H hpM
  have hcoef : (coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p)).coeff (1 - (p : ℤ)) ≠ 0 := by
    rw [coeffEmb_coeff, ← hx, coeffMap_coeff, hx1, map_one, map_one]; exact one_ne_zero
  have hu0 : u ≠ 0 := by
    intro h0
    have h1 := congrArg (fun z : ↥(xHFunctionFieldBar M H) => ((z : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)).coeff (1 - (p : ℤ))) h0
    simp only [hu, ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h1
    exact hcoef h1

  have h₁ : u ∈ Rpd.R₁.integers := by
    have := (Rpd.mem_integers₂_iff u₂).mp h₂; rwa [hθu₂] at this
  obtain ⟨D, hD, -⟩ := (ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar M H).exists_divisor u hu0
  have hD₂θ : ∀ W, D₂ W = D (SemilinearAut.ofAlgAut θ.symm • W) := by
    intro W
    rw [hD₂ W, hD, hu₂θ, ← SemilinearAut.ord_smul (SemilinearAut.ofAlgAut θ.symm) W (θ u), SemilinearAut.ofAlgAut_smul,
      AlgEquiv.symm_apply_apply]
  have hD₂θ' : ∀ W, D₂ W = D (SemilinearAut.ofAlgAut θ • W) := by
    intro W
    rw [hD₂ W, hD, hu₂inv, ← SemilinearAut.ord_smul (SemilinearAut.ofAlgAut θ) W (θ.symm u), SemilinearAut.ofAlgAut_smul,
      AlgEquiv.apply_symm_apply]

  have hres : Rpd.R₂.residue ⟨u₂, h₂⟩ = Rpd.R₁.residue ⟨u, h₁⟩ := by
    rw [Rpd.residue₂_eq u₂ h₂]
    have hsub : (⟨θ u₂, (Rpd.mem_integers₂_iff u₂).mp h₂⟩ : ↥(Rpd.R₁.integers)) = ⟨u, h₁⟩ := Subtype.ext hθu₂
    rw [hsub]

  obtain ⟨L1a, L1b⟩ := ModularCurve.XHDRModelAtP.oneSidedFst_laws_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ α hα hβ Psp Rpd hwgen hθ hα_coe hTD hmodel hcompat hcompat' u hu h₁ D hD

  have hT1 : ∀ W, Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = δ (Psp.reduceFst α hα (SemilinearAut.ofAlgAut θ.symm • W)) := by
    intro W
    show δ (Psp.sp (W.restrictAlong (θ.toAlgHom.comp α) hβ)) = δ (Psp.sp ((SemilinearAut.ofAlgAut θ.symm • W).restrictAlong α hα))
    rw [AlgebraicCurve.SemilinearAut.ofAlgAut_smul_place,
      AlgebraicCurve.Place.smul_restrictAlong α (θ.toAlgHom.comp α) hα hβ θ.symm 1 (fun x => by simp) W, one_smul]
  have hT3 : ∀ W, Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (SemilinearAut.ofAlgAut θ.symm • W) = Psp.reduceFst α hα W ∧
      (Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W ↔ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (SemilinearAut.ofAlgAut θ.symm • W)) :=
    fun W => ModularCurve.XHDRModelAtP.reduceSnd_ofAlgAut_symm_smul_eq_reduceFst_and_isStrictSnd_iff_isStrictFst_ofAlgAut_symm_smul_prolongationDatum p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ α hα hβ Psp Rpd hwgen hθ hα_coe hTD hmodel hcompat hcompat' W
  have hT2 : ∀ W, JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) W ↔
      JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) (SemilinearAut.ofAlgAut θ • W) :=
    fun W => ModularCurve.XHDRModelAtP.isZeroSide_iff_isInftySide_smul_prolongationDatum p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcompat W

  have G2 : coeffMap A.subtype (coeffMap (Int.castRingHom ↥A) x) = ((u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hu, ← hx]
    show coeffMap A.subtype (coeffMap (Int.castRingHom ↥A) x) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (coeffMap (Int.castRingHom ℚ) x)
    rw [coeffMap_coeffMap, coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext_int _ _) x
  obtain ⟨h₁', hres₁exp'⟩ := Rpd.residue₁_coeffMap (coeffMap (Int.castRingHom ↥A) x) (by rw [G2]; exact u.2)
  have hux : (⟨coeffMap A.subtype (coeffMap (Int.castRingHom ↥A) x), by rw [G2]; exact u.2⟩ : ↥(xHFunctionFieldBar M H)) = u :=
    Subtype.ext G2
  have G3exp : ((Rpd.R₁.residue ⟨u, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
      coeffMap (Int.castRingHom (ResidueField ↥A)) x := by
    have hsub : (⟨u, h₁⟩ : ↥(Rpd.R₁.integers)) = ⟨_, h₁'⟩ := Subtype.ext hux.symm
    rw [hsub, hres₁exp', coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext_int _ _) x
  have hT5 := ModularCurve.diamondActionModL_apply_eq_self_of_coe_eq_coeffMap_modularUnitSeries p (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) x hx
    (Rpd.R₁.residue ⟨u, h₁⟩) G3exp
  have hθθ : θ.symm * θ = 1 := AlgEquiv.ext fun x => θ.symm_apply_apply x
  have hθθ' : θ * θ.symm = 1 := AlgEquiv.ext fun x => θ.apply_symm_apply x
  have hss : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      SemilinearAut.ofAlgAut θ.symm • (SemilinearAut.ofAlgAut θ • W) = W := by
    intro W; rw [← mul_smul, ← map_mul, hθθ, map_one, one_smul]
  have hss' : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      SemilinearAut.ofAlgAut θ • (SemilinearAut.ofAlgAut θ.symm • W) = W := by
    intro W; rw [← mul_smul, ← map_mul, hθθ', map_one, one_smul]
  obtain ⟨gδ, hgδ⟩ : ∃ g : SemilinearAut (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      g = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) := ⟨_, rfl⟩
  have hδ' : ∀ v, δ v = gδ • v := by intro v; rw [hδ, hgδ]
  have hδinj : Function.Injective δ := by
    intro a b h; rw [hδ', hδ'] at h; exact smul_left_cancel _ h
  have hpM' : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have := Nat.div_mul_cancel hpM
    rw [hk] at this
    rw [← this]; ring
  have hcommφ : ∀ w, qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (gδ • w) =
      gδ • qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w := by
    intro w; rw [hgδ]
    exact ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpM' (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) w
  have hcommφ' : ∀ w, qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (gδ⁻¹ • w) =
      gδ⁻¹ • qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w := by
    intro w
    apply smul_left_cancel gδ
    rw [← hcommφ, smul_inv_smul, smul_inv_smul]
  have hFixδ : ∀ v, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (gδ⁻¹ • v) ↔
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v := by
    intro v
    show qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (gδ⁻¹ • v))) = gδ⁻¹ • v ↔
      qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v)) = v
    rw [hδ', hδ', hcommφ', smul_inv_smul, hcommφ, eq_inv_smul_iff]
  have hfix : gδ • (Rpd.R₁.residue ⟨u, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = Rpd.R₁.residue ⟨u, h₁⟩ := by
    rw [hgδ, SemilinearAut.ofAlgAut_smul, hT5]
  exact ⟨law2a p M H hpM A θ α hα hβ δ Psp Rpd u u₂ h₁ h₂ D D₂ hres hss hss' gδ hδ' hFixδ hfix hD₂θ hT1 hT3 L1a,
    law2b p M H hpM A θ α hα hβ δ Psp Rpd u u₂ h₁ h₂ D D₂ hres hss hss' hD₂θ' (fun W => (hT3 W).1) hT2 L1b⟩

end S_ModularCurve_XHDRModelAtP_oneSidedSnd_laws_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_oneSidedSnd_laws_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel (solution)
