-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_unit_pair_divisor_oneSidedLaws_jump_prolongationDatum_of_isModel_of_nodeValueLaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d15ae2fb-4e4d-5eb6-bb25-24dd18e22e96

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd
import Theorems.Thm_ModularCurve_hasValue_zero_of_mem_ssPlacesQExp_of_coe_eq_coeffMap_modularUnitSeries
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residue_snd_eq_zero_of_residue_fst_hasValue_zero_of_nodeValueLaw
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_XHDRModelAtP_not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum
import Theorems.Thm_ModularCurve_XHDRModelAtP_not_isAffinePlace_frob_reduceSnd_of_isZeroSide_prolongationDatum
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
import Theorems.Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
import Theorems.Thm_ModularCurve_nonempty_ssPlacesQExp
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_and_arithmeticGalois_comm_of_comp_w_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_algEquiv_eq_of_forall_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq
import Theorems.Thm_ModularCurve_algEquiv_apply_eq_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_of_qExpand_of_arithmeticGalois_comm
import Theorems.Thm_ModularCurve_XHDRModelAtP_oneSidedFst_laws_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
import Theorems.Thm_ModularCurve_XHDRModelAtP_oneSidedSnd_laws_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_unit_pair_divisor_oneSidedLaws_jump_prolongationDatum_of_isModel_of_nodeValueLaw
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation ValuationSubring.instIsAlgClosedResidueField ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.TwoChart.isOpenImmersion_fInf ModularCurve.TwoChart.isOpenImmersion_ιFin ModularCurve.TwoChart.isOpenImmersion_ιInf ModularCurve.TwoChart.isOpenImmersion_fFin GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply"
p2m_attr_erase "simp" "ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.TwoChart.coe_jChartFin ModularCurve.TwoChart.ιFin_modelTo ModularCurve.TwoChart.ιInf_modelTo ModularCurve.TwoChart.ιInf_modelTo_assoc ModularCurve.TwoChart.coe_jInvChartInf ModularCurve.TwoChart.ιFin_modelTo_assoc ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_jqNGen ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

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

    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

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
    ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hfiM : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

  obtain ⟨⟨x, hx, hx1, hx0⟩, hmemQ, hint, hint'⟩ := ModularCurve.exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd p M H hpM
  have G1 : coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p) ∈ xHFunctionFieldBar M H :=
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmemQ
  obtain ⟨u, hu⟩ : ∃ u : ↥(xHFunctionFieldBar M H),
      ((u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p) :=
    ⟨⟨_, G1⟩, rfl⟩
  have hcoef : (coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p)).coeff (1 - (p : ℤ)) = 1 := by
    rw [coeffEmb_coeff, ← hx, coeffMap_coeff, hx1, map_one, map_one]
  have hu0 : u ≠ 0 := by
    intro h0
    have h1 := congrArg (fun z : ↥(xHFunctionFieldBar M H) => ((z : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)).coeff (1 - (p : ℤ))) h0
    simp only [hu, hcoef, ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h1
    exact one_ne_zero h1

  have G2 : coeffMap A.subtype (coeffMap (Int.castRingHom ↥A) x) = ((u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hu, ← hx]
    show coeffMap A.subtype (coeffMap (Int.castRingHom ↥A) x) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (coeffMap (Int.castRingHom ℚ) x)
    rw [coeffMap_coeffMap, coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext_int _ _) x
  obtain ⟨h₁', hres₁exp'⟩ := Rpd.residue₁_coeffMap (coeffMap (Int.castRingHom ↥A) x) (by rw [G2]; exact u.2)
  have hux : (⟨coeffMap A.subtype (coeffMap (Int.castRingHom ↥A) x), by rw [G2]; exact u.2⟩ : ↥(xHFunctionFieldBar M H)) = u :=
    Subtype.ext G2
  have h₁ : u ∈ Rpd.R₁.integers := hux ▸ h₁'
  have G3exp : ((Rpd.R₁.residue ⟨u, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
      coeffMap (Int.castRingHom (ResidueField ↥A)) x := by
    have hsub : (⟨u, h₁⟩ : ↥(Rpd.R₁.integers)) = ⟨_, h₁'⟩ := Subtype.ext hux.symm
    rw [hsub, hres₁exp', coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext_int _ _) x
  have hres₁ : Rpd.R₁.residue ⟨u, h₁⟩ ≠ 0 := by
    intro h0
    have h1 := congrArg (fun z : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) =>
      ((z : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)).coeff (1 - (p : ℤ))) h0
    simp only [G3exp, coeffMap_coeff, hx1, map_one, ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h1
    exact one_ne_zero h1
  have hinv₁ : u⁻¹ ∈ Rpd.R₁.integers := by
    obtain ⟨w, hw⟩ := Rpd.R₁.isUnit_of_residue_ne_zero hres₁
    have hwu : ((w : ↥(Rpd.R₁.integers)) : ↥(xHFunctionFieldBar M H)) = u := congrArg Subtype.val hw
    have hz : (((w⁻¹ : (↥(Rpd.R₁.integers))ˣ) : ↥(Rpd.R₁.integers)) : ↥(xHFunctionFieldBar M H)) * u = 1 := by
      rw [← hwu, ← MulMemClass.coe_mul, Units.inv_mul]; rfl
    rw [inv_eq_of_mul_eq_one_left hz]
    exact ((w⁻¹ : (↥(Rpd.R₁.integers))ˣ) : ↥(Rpd.R₁.integers)).2

  haveI hcurve : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := UXInst.isCurveOver_xHFunctionFieldBar M H
  obtain ⟨D₁, hD₁, -⟩ := (ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar M H).exists_divisor u hu0

  have hpM' : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have := Nat.div_mul_cancel hpM
    rw [hk] at this
    rw [← this]; ring
  obtain ⟨y, hy⟩ := ModularCurve.nonempty_ssPlacesQExp (M / p) (JHNeronObjectAtP.ΓN p M H hpM)
    (Gamma1_le_GammaH (M / p) _) (CohCarrier.GammaH_le_Gamma0 _) p hpM' (ResidueField ↥A)
  have hφy : qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y ∈
      ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p := by
    have himg := ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)
    exact himg ▸ ⟨y, hy, rfl⟩
  obtain ⟨s, hs1, hs2⟩ : ∃ s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      s.1 = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y ∧ s.2 = y := ⟨(_, _), rfl, rfl⟩
  have hs : s ∈ SS := by
    refine (hSS s).mpr ⟨?_, ?_⟩
    · rw [hs2]; exact hy
    · rw [hs1, hs2]
  have haff2 : JHPlaceSpecialization.IsAffinePlace p M H hpM A s.2 := by
    obtain ⟨xx, a, hxx, hva, -⟩ := (mem_ssPlacesQExp_iff y).mp hy
    exact ⟨xx, a, hxx, hs2.symm ▸ hva⟩
  have haff1 : JHPlaceSpecialization.IsAffinePlace p M H hpM A s.1 := by
    rw [hs1, ← hs2]; exact (ModularCurve.JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL p M H hpM A hA).1 s.2 haff2

  have hvan : s.1.HasValue (Rpd.R₁.residue ⟨u, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) 0 := by
    rw [hs1]
    exact ModularCurve.hasValue_zero_of_mem_ssPlacesQExp_of_coe_eq_coeffMap_modularUnitSeries p (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) x hx (Rpd.R₁.residue ⟨u, h₁⟩) G3exp _ hφy
  have G6 : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord u ≠ 0 →
      JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V :=
    fun V hV => ModularCurve.JHPlaceSpecialization.isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries p M H hpM A u hu V hV
  have hnodiv : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord u ≠ 0 →
      ¬ (Psp.reduceFst α hα V = s.1 ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = s.2) := by
    intro V hV ⟨h1, h2⟩
    rcases ModularCurve.JHPlaceSpecialization.isInftySide_or_isZeroSide_of_isCuspidal p M H hpM A hA V (G6 V hV) with hinf | hzero
    · have hni := ModularCurve.XHDRModelAtP.not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcompat V hinf
      rw [h1] at hni
      exact hni haff1
    · have hfa := (ModularCurve.JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL p M H hpM A hA).1 s.2 haff2
      have hnz := ModularCurve.XHDRModelAtP.not_isAffinePlace_frob_reduceSnd_of_isZeroSide_prolongationDatum p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcompat V hzero
      rw [h2] at hnz
      exact hnz hfa
  have hsep : ∀ h₂ : u ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u, h₂⟩ = 0 :=
    ModularCurve.JHPlaceSpecialization.ProlongationDatum.residue_snd_eq_zero_of_residue_fst_hasValue_zero_of_nodeValueLaw p M H hpM A θ α (θ.toAlgHom.comp α) hα hβ δ SS Psp Rpd hNV u h₁ hres₁ s hs hnodiv hvan
  have hjump₂ : ∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
      ∃ h₂ : f ^ m * u ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u ^ j, h₂⟩ ≠ 0 :=
    fun f hf => AlgebraicCurve.RegularProlongation.exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) Rpd.R₂ u hu0 hsep f hf

  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := by
    obtain ⟨xt, -, hfin⟩ := UXInst.exists_transcendental_finiteDimensional_xHFunctionFieldBar M H
    exact UXInst.essFiniteType_of_presentation hfin
  obtain ⟨θ₁, hwgen₁, hθgal₁⟩ := ModularCurve.XHDRModelAtP.exists_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_and_arithmeticGalois_comm_of_comp_w_eq p M H hpM hj 𝔛
  have hθeq : θ = θ₁ := ModularCurve.XHDRModelAtP.algEquiv_eq_of_forall_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq p M H hpM hj 𝔛 θ θ₁ hwgen hwgen₁
  have hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f := by
    rw [hθeq]; exact hθgal₁
  have hAL : θ u = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((p : ℕ) : AlgebraicClosure ℚ) ^ 12) * u⁻¹ :=
    ModularCurve.algEquiv_apply_eq_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_of_qExpand_of_arithmeticGalois_comm p M H hpM hpM2 hHp hj θ hθ hθgal u hu
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : ↥(xHFunctionFieldBar M H),
      u₂ = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((p : ℕ) : AlgebraicClosure ℚ) ^ 12) * u⁻¹ := ⟨_, rfl⟩
  have hp12 : (((p : ℕ) : AlgebraicClosure ℚ) ^ 12) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have G7 : θ u₂ = u := by
    rw [hu₂, map_mul, AlgEquiv.commutes, map_inv₀, hAL, mul_inv, ← mul_assoc, ← map_inv₀, ← map_mul,
      mul_inv_cancel₀ hp12, map_one, one_mul, inv_inv]
  have h₂ : u₂ ∈ Rpd.R₂.integers := by
    rw [Rpd.mem_integers₂_iff, G7]; exact h₁
  have hres₂ : Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 := by
    rw [Rpd.residue₂_eq u₂ h₂]
    have hsub : (⟨θ u₂, (Rpd.mem_integers₂_iff u₂).mp h₂⟩ : ↥(Rpd.R₁.integers)) = ⟨u, h₁⟩ := Subtype.ext G7
    rw [hsub]; exact hres₁
  have hinv₂ : u₂⁻¹ ∈ Rpd.R₂.integers := by
    rw [Rpd.mem_integers₂_iff, map_inv₀, G7]; exact hinv₁
  have hu₂0 : u₂ ≠ 0 := by
    rw [hu₂]; exact mul_ne_zero ((map_ne_zero _).mpr hp12) (inv_ne_zero hu0)
  have hsep₁ : ∀ h : u₂ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₂, h⟩ = 0 := by
    intro h
    have hpA : (((p : ℕ) : AlgebraicClosure ℚ) ^ 12) ∈ A := pow_mem (natCast_mem A p) 12
    have hc : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((p : ℕ) : AlgebraicClosure ℚ) ^ 12) ∈ Rpd.R₁.integers :=
      (Rpd.R₁.algebraMap_mem_iff _).mpr hpA
    have hmul : (⟨u₂, h⟩ : ↥(Rpd.R₁.integers)) = ⟨_, hc⟩ * ⟨u⁻¹, hinv₁⟩ :=
      Subtype.ext (by rw [MulMemClass.coe_mul]; exact hu₂)
    have hres_c : Rpd.R₁.residue ⟨_, hc⟩ = 0 := by
      have hra := Rpd.R₁.residue_algebraMap ⟨_, hpA⟩
      have hpmax : (⟨((p : ℕ) : AlgebraicClosure ℚ), natCast_mem A p⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A :=
        (ValuationSubring.coe_mem_nonunits_iff).mp hA
      have hzero : IsLocalRing.residue ↥A ⟨_, hpA⟩ = 0 := by
        have : (⟨_, hpA⟩ : ↥A) = (⟨((p : ℕ) : AlgebraicClosure ℚ), natCast_mem A p⟩ : ↥A) ^ 12 := Subtype.ext (by simp)
        rw [this, map_pow, (IsLocalRing.residue_eq_zero_iff _).mpr hpmax, zero_pow (by norm_num)]
      rw [hzero, map_zero] at hra
      exact hra
    rw [hmul, map_mul, hres_c, zero_mul]
  have hjump₁ : ∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
      ∃ h₁' : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁'⟩ ≠ 0 :=
    fun f hf => AlgebraicCurve.RegularProlongation.exists_pow_mul_zpow_mem_integers_residue_ne_zero_of_forall_residue_eq_zero A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) Rpd.R₁ u₂ hu₂0 hsep₁ f hf

  have hD₂ : ∀ W, (-D₁) W = W.ord u₂ := by
    intro W
    rw [Finsupp.neg_apply, hD₁ W, hu₂, W.ord_mul ((map_ne_zero _).mpr hp12) (inv_ne_zero hu0),
      AlgebraicCurve.ConstantReduction.ord_algebraMap W hp12, W.ord_inv, zero_add]

  have L1 := ModularCurve.XHDRModelAtP.oneSidedFst_laws_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ α hα hβ Psp Rpd hwgen hθ hα_coe hTD hmodel hcompat hcompat' u hu h₁ D₁ hD₁
  have L2 := ModularCurve.XHDRModelAtP.oneSidedSnd_laws_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ α hα hβ Psp Rpd hwgen hθ hα_coe hTD hmodel hcompat hcompat' u hu u₂ hu₂ h₂ (-D₁) hD₂

  exact ⟨u, u₂, D₁, -D₁, hD₁, hD₂, ⟨h₁, hres₁, hinv₁, L1.1, L1.2⟩, hjump₂, ⟨h₂, hres₂, hinv₂, L2.1, L2.2⟩, hjump₁⟩

end S_ModularCurve_XHDRModelAtP_exists_unit_pair_divisor_oneSidedLaws_jump_prolongationDatum_of_isModel_of_nodeValueLaw
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_unit_pair_divisor_oneSidedLaws_jump_prolongationDatum_of_isModel_of_nodeValueLaw (solution)
