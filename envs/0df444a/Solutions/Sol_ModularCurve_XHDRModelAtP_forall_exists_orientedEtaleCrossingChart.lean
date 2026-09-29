-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.forall_exists_orientedEtaleCrossingChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/7f03db0e-24c6-59c2-8250-3f90b796a782

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_xO
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing
import Theorems.Thm_ModularCurve_XHDRModelAtP_bcMap_genericPoint_specializes_crossingPt
import Theorems.Thm_ModularCurve_XHDRModelAtP_bcMap_genericPoint_specializes_or
import Theorems.Thm_ModularCurve_XHDRModelAtP_not_branchIdeal_le_branchIdeal_crossingPt
import Theorems.Thm_ModularCurve_XHDRModelAtP_residue_baseGerm_surjective_and_isClosed_crossingPt
import Theorems.Thm_ModularCurve_XHDRModelAtP_baseGerm_mem_nonZeroDivisors_and_two_le_ringKrullDim_stalk
import Theorems.Thm_ModularCurve_XHDRModelAtP_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_span_pair_baseGerm_eq_branchIdeal
import Theorems.Thm_ModularCurve_XHDRModelAtP_branchIdeal_xiInf_inf_branchIdeal_xiZero_eq_span_baseGerm
import Theorems.Thm_ModularCurve_XHDRModelAtP_range_comp_bcMap_eq_closure_and_isClosed
import Theorems.Thm_IsLocalRing_exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_crossingChart_of_crossingPresentation_stalk
import Theorems.Thm_MvPolynomial_CrossingQuotient_ringKrullDim_le
import Theorems.Thm_MvPolynomial_CrossingQuotient_isDomain_and_isIntegrallyClosed
import Theorems.Thm_AlgebraicGeometry_exists_etale_nhd_of_flat_stalkMap_of_map_maximalIdeal_eq_of_isIso_residueFieldMap
import Theorems.Thm_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_forall_exists_orientedEtaleCrossingChart
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_jqNGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply"
p2m_attr_erase "simp" "AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial IsLocalRing ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

noncomputable section

section Glue

private theorem ECL_Main.not_mem_basicOpen_of_germ_mem_branchIdeal {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x)
    (U : X.Opens) (hxU : x ∈ U) (s : Γ(X, U)) (hs : X.presheaf.germ U x hxU s ∈ Scheme.branchIdeal h)
    (y : X) (hy : y ∈ closure ({ξ} : Set X)) : y ∉ X.basicOpen s := by
  intro hy'
  have hξU : ξ ∈ U := h.mem_open U.isOpen hxU
  have hgerm : X.presheaf.germ U ξ hξU s ∈ IsLocalRing.maximalIdeal _ := by
    rw [Scheme.branchIdeal, Ideal.mem_comap, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes] at hs
    exact hs
  have hξ : ξ ∉ X.basicOpen s := fun hh =>
    (IsLocalRing.mem_maximalIdeal _ |>.mp hgerm) ((X.mem_basicOpen s ξ hξU).mp hh)
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hy (X.basicOpen s) (X.basicOpen s).isOpen hy'
  rw [Set.mem_singleton_iff] at hz2
  subst hz2
  exact hξ hz1

private theorem ECL_Main.range_subset_closure_image_genericPoint {C X : Scheme.{u}} [IsIntegral C] (i : C ⟶ X) :
    Set.range i.base ⊆ closure {i.base (genericPoint C)} := by
  rintro _ ⟨c, rfl⟩
  have hc : c ∈ closure ({genericPoint C} : Set C) := by
    rw [genericPoint_closure]; trivial
  have := image_closure_subset_closure_image i.continuous ⟨c, hc, rfl⟩
  simpa [Set.image_singleton] using this

private theorem ECL_Main.toBase_eq_closedPoint_of_mem_asIdeal {O : Type u} [CommRing O] [IsLocalRing O] (s : O)
    (hs : s ∈ IsLocalRing.maximalIdeal O)
    {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of O)) (U : X.Opens)
    (f : (U : Scheme.{u}) ⟶ CrossingQuotient.crossingScheme s)
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O s))) = U.ι ≫ πX)
    (y : ↥(U : Scheme.{u}))
    (hy : CrossingQuotient.U s ∈ (f.base y).asIdeal ∨ CrossingQuotient.V s ∈ (f.base y).asIdeal)
    (hgen : IsLocalRing.maximalIdeal O = Ideal.span {s} ∨ ∃ (ϖ : O) (e : ℕ), 1 ≤ e ∧ s = ϖ ^ e ∧ IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) :
    πX.base (U.ι.base y) = IsLocalRing.closedPoint O := by

  have hsP : algebraMap O (CrossingQuotient O s) s ∈ (f.base y).asIdeal := by
    rw [← CrossingQuotient.U_mul_V]
    rcases hy with h | h
    · exact Ideal.mul_mem_right _ _ h
    · exact Ideal.mul_mem_left _ _ h
  have h1 : πX.base (U.ι.base y) =
      (Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O s)))).base (f.base y) := by
    rw [← Scheme.Hom.comp_apply, ← hf, Scheme.Hom.comp_apply]
  rw [h1]
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap O (CrossingQuotient O s)) (f.base y).asIdeal = IsLocalRing.maximalIdeal O
  have hprime : (Ideal.comap (algebraMap O (CrossingQuotient O s)) (f.base y).asIdeal).IsPrime := Ideal.comap_isPrime _ _
  symm
  refine (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le hprime.ne_top ?_
  have hsO : s ∈ Ideal.comap (algebraMap O (CrossingQuotient O s)) (f.base y).asIdeal := hsP
  rcases hgen with hm | ⟨ϖ, e, he, rfl, hm⟩
  · rw [hm, Ideal.span_singleton_le_iff_mem]; exact hsO
  · rw [hm, Ideal.span_singleton_le_iff_mem]
    exact hprime.mem_of_pow_mem e hsO

private theorem ECL_Main.mem_range_efib_comp
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    {Y : Scheme.{0}} (g : fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ Y)
    {y : ↥Y} (hy : y ∈ Set.range g.base) : y ∈ Set.range (𝔛.efib A hA ρ hρ ≫ g).base := by
  obtain ⟨c, rfl⟩ := hy
  refine ⟨(inv (𝔛.efib A hA ρ hρ)).base c, ?_⟩
  rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (𝔛.efib A hA ρ hρ), IsIso.inv_hom_id]; rfl

end Glue

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ρO : R p →+* O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶
      pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))

    (hrat : ∀ x : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶
          pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)),
        s ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ∧
        s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) =
          (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base x) :
    ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      ∃ (e : ℕ) (_ : 1 ≤ e)
        (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).Opens)
        (_ : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n ∈ U)
        (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e)),

        f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) =
            U.ι ≫ pullback.snd _ _ ∧

        (∀ y : ↥(U : Scheme.{0}),
            (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧
              CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔
            U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n →
            (f.stalkMap y).hom.Flat ∧
            Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
            IsIso (f.residueFieldMap y)) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n →
            ∃ V : (U : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f)) ∧

        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bc).base) ∧
        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bc).base) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bc).base →
            CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ∧
        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bc).base →
            CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) := by
  intro n

  have hbc : bc = bcMap (ΓM M H) hj ρO toκ htoκ := by
    apply pullback.hom_ext
    · rw [hbc₁, bcMap, pullback.map, pullback.lift_fst, Category.comp_id]
    · rw [hbc₂, bcMap, pullback.map, pullback.lift_snd]
  subst hbc

  obtain ⟨hinf, hzero⟩ : 𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n ∧ 𝔛.ξzero A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n :=
    ModularCurve.XHDRModelAtP.bcMap_genericPoint_specializes_crossingPt p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO toκ htoκ n
  haveI : IsIntegral (XO (ΓM M H) hj ρO) := ModularCurve.XHDRModelAtP.isIntegral_xO p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O hϖ ρO
  haveI := (𝔛.Mfib A hA ρ hρ).isIntegral
  have hpO : Irreducible ((p : ℕ) : O) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hϖ

  have hPQ := ModularCurve.XHDRModelAtP.branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ n hinf hzero
  obtain ⟨hQP, hPQ'⟩ := ModularCurve.XHDRModelAtP.not_branchIdeal_le_branchIdeal_crossingPt p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ n hinf hzero
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ModularCurve.XHDRModelAtP.exists_span_pair_baseGerm_eq_branchIdeal p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ n hinf hzero
  have hIU := ModularCurve.XHDRModelAtP.branchIdeal_xiInf_inf_branchIdeal_xiZero_eq_span_baseGerm p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ n hinf hzero
  obtain ⟨t, t', htt', ht, htunit⟩ := ModularCurve.XHDRModelAtP.exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ n hinf hzero
  obtain ⟨hϖnz, hstalk2⟩ :=
    ModularCurve.XHDRModelAtP.baseGerm_mem_nonZeroDivisors_and_two_le_ringKrullDim_stalk p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ n hinf hzero
  obtain ⟨hres, hxcl⟩ :=
    ModularCurve.XHDRModelAtP.residue_baseGerm_surjective_and_isClosed_crossingPt p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ n hinf hzero (hrat n)
  have hab : a * b ∈ Ideal.span {baseGerm ρO (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) ((p : ℕ) : O)} := by
    rw [← hIU]
    refine ⟨?_, ?_⟩
    · exact Ideal.mul_mem_right _ _ (ha ▸ Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (hb ▸ Ideal.subset_span (by simp))

  obtain ⟨e, g₀, gi, he1, -, hrel, hg₀, hgi⟩ :
      ∃ (e : ℕ) (g₀ gi : (XO (ΓM M H) hj ρO).presheaf.stalk (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)), 1 ≤ e ∧ e ≤ 12 ∧
        g₀ * gi = baseGerm ρO (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) ((p : ℕ) : O) ^ e ∧
        Ideal.span {g₀, baseGerm ρO (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) ((p : ℕ) : O)} = Scheme.branchIdeal hzero ∧
        Ideal.span {gi, baseGerm ρO (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) ((p : ℕ) : O)} = Scheme.branchIdeal hinf := by
    rcases htunit with hu | hu
    ·
      have htQ : t ∉ Scheme.branchIdeal hinf := fun h =>
        (IsLocalRing.notMem_maximalIdeal.mpr hu) ((Scheme.mem_branchIdeal_iff hinf t).mp h)
      obtain ⟨e, u, v, he1, he, huv, hu', hv'⟩ :=
        IsLocalRing.exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal hϖnz hPQ' (by rwa [sup_comm]) hb ha
          (by rwa [mul_comm]) htQ ht htt'
      exact ⟨e, u, v, he1, he, huv, hu', hv'⟩
    ·
      have htQ : t ∉ Scheme.branchIdeal hzero := fun h =>
        (IsLocalRing.notMem_maximalIdeal.mpr hu) ((Scheme.mem_branchIdeal_iff hzero t).mp h)
      obtain ⟨e, u, v, he1, he, huv, hu', hv'⟩ :=
        IsLocalRing.exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal hϖnz hQP hPQ ha hb hab htQ ht htt'
      exact ⟨e, v, u, he1, he, by rw [mul_comm]; exact huv, hv', hu'⟩

  obtain ⟨hdom, hic⟩ := MvPolynomial.CrossingQuotient.isDomain_and_isIntegrallyClosed (W := O) (((p : ℕ) : O) ^ e)
      (pow_ne_zero e hpO.ne_zero)
  haveI := hdom; haveI := hic
  haveI : LocallyOfFiniteType (XO.toBase (ΓM M H) hj ρO) := by
    haveI := 𝔛.isProper
    infer_instance
  haveI : IsLocallyNoetherian (XO (ΓM M H) hj ρO) := LocallyOfFiniteType.isLocallyNoetherian (XO.toBase (ΓM M H) hj ρO)
  have hmax : IsLocalRing.maximalIdeal ((XO (ΓM M H) hj ρO).presheaf.stalk (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)) =
      Ideal.span {baseGerm ρO (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) ((p : ℕ) : O), g₀, gi} := by
    rw [← hPQ, ← hgi, ← hg₀, ← Ideal.span_union]
    congr 1
    ext z
    simp only [Set.union_insert, Set.union_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hdim : ringKrullDim (CrossingQuotient O (((p : ℕ) : O) ^ e)) ≤
      ringKrullDim ((XO (ΓM M H) hj ρO).presheaf.stalk (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)) := by
    refine (MvPolynomial.CrossingQuotient.ringKrullDim_le O 1 ?_ _ (pow_ne_zero e hpO.ne_zero)).trans ?_
    · rw [IsDiscreteValuationRing.ringKrullDim_eq_one O, Nat.cast_one]
    · refine le_trans ?_ hstalk2
      norm_num
  obtain ⟨U, hxU, gU, hU, f, hgerm_g, hgerm_h, -, hover, hfib, hflat, hdictU, hdictV⟩ :=
    AlgebraicGeometry.Scheme.exists_crossingChart_of_crossingPresentation_stalk ((p : ℕ) : O) e
      (XO.toBase (ΓM M H) hj ρO) (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) hxcl g₀ gi hrel hmax hres hdim

  have hvan_g : ∀ y : ↥(XO (ΓM M H) hj ρO), 𝔛.ξzero A hA ρ hρ ρO toκ htoκ ⤳ y → y ∉ (XO (ΓM M H) hj ρO).basicOpen gU := by
    intro y hy
    refine ECL_Main.not_mem_basicOpen_of_germ_mem_branchIdeal hzero U hxU gU ?_ y (specializes_iff_mem_closure.mp hy)
    rw [hgerm_g, ← hg₀]; exact Ideal.subset_span (by simp)
  have hvan_h : ∀ y : ↥(XO (ΓM M H) hj ρO), 𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ y → y ∉ (XO (ΓM M H) hj ρO).basicOpen hU := by
    intro y hy
    refine ECL_Main.not_mem_basicOpen_of_germ_mem_branchIdeal hinf U hxU hU ?_ y (specializes_iff_mem_closure.mp hy)
    rw [hgerm_h, ← hgi]; exact Ideal.subset_span (by simp)
  have hrange_inf : ∀ y : ↥(XO (ΓM M H) hj ρO), y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base →
      𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ y := fun y hy => specializes_iff_mem_closure.mpr
    (ECL_Main.range_subset_closure_image_genericPoint (C := (𝔛.Mfib A hA ρ hρ).C) (i := 𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ) (ECL_Main.mem_range_efib_comp 𝔛 A hA ρ hρ _ hy))
  have hrange_zero : ∀ y : ↥(XO (ΓM M H) hj ρO), y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base →
      𝔛.ξzero A hA ρ hρ ρO toκ htoκ ⤳ y := fun y hy => specializes_iff_mem_closure.mpr
    (ECL_Main.range_subset_closure_image_genericPoint (C := (𝔛.Mfib A hA ρ hρ).C) (i := 𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ) (ECL_Main.mem_range_efib_comp 𝔛 A hA ρ hρ _ hy))

  have hcover : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∨ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) →
      𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ U.ι.base y ∨ 𝔛.ξzero A hA ρ hρ ρO toκ htoκ ⤳ U.ι.base y := by
    intro y hy
    have hbase : (XO.toBase (ΓM M H) hj ρO).base (U.ι.base y) = IsLocalRing.closedPoint O := by
      refine ECL_Main.toBase_eq_closedPoint_of_mem_asIdeal (((p : ℕ) : O) ^ e) ?_ (XO.toBase (ΓM M H) hj ρO) U f hover y hy
        (Or.inr ⟨(p : O), e, he1, rfl, hϖ⟩)
      rw [hϖ]
      exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) e he1
    refine ModularCurve.XHDRModelAtP.bcMap_genericPoint_specializes_or p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ (U.ι.base y) ?_
    intro hmem
    have hmem' : (XO.toBase (ΓM M H) hj ρO).base (U.ι.base y) ∈
        (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := hmem
    rw [hbase] at hmem'
    refine (PrimeSpectrum.mem_basicOpen _ _).mp hmem' ?_
    change ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O
    rw [hϖ]; exact Ideal.mem_span_singleton_self _
  refine ⟨e, he1, U, hxU, f, hover, hfib, hflat, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro y hy
    obtain ⟨hfl, hmx, hrs⟩ := hflat y hy
    haveI := hrs
    haveI := 𝔛.lfp
    haveI : LocallyOfFinitePresentation (U.ι ≫ XO.toBase (ΓM M H) hj ρO) := inferInstance
    haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e))))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    haveI : LocallyOfFinitePresentation f :=
      AlgebraicGeometry.locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType (g := Spec.map (CommRingCat.ofHom
        (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e))))) (by rw [hover]; infer_instance) inferInstance
    exact AlgebraicGeometry.exists_etale_nhd_of_flat_stalkMap_of_map_maximalIdeal_eq_of_isIso_residueFieldMap f y hfl hmx
  ·
    intro y hV

    have hhU : U.ι.base y ∉ (XO (ΓM M H) hj ρO).basicOpen hU := (hdictV y).mp hV
    rcases hcover y (Or.inr hV) with h | h
    · rw [(ModularCurve.XHDRModelAtP.range_comp_bcMap_eq_closure_and_isClosed p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ 0).1]
      exact specializes_iff_mem_closure.mp h
    · have hUy : CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal := (hdictU y).mpr (hvan_g _ h)
      have hyx : U.ι.base y = 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n := (hfib y).mp ⟨hUy, hV⟩
      rw [hyx]
      exact ⟨(pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · intro y hUm
    rcases hcover y (Or.inl hUm) with h | h
    · have hVy : CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal := (hdictV y).mpr (hvan_h _ h)
      have hyx : U.ι.base y = 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n := (hfib y).mp ⟨hUm, hVy⟩
      rw [hyx]
      refine ⟨(pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← pullback.condition_assoc]
    · rw [(ModularCurve.XHDRModelAtP.range_comp_bcMap_eq_closure_and_isClosed p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ 1).1]
      exact specializes_iff_mem_closure.mp h
  · intro y hy
    exact (hdictV y).mpr (hvan_h _ (hrange_inf _ hy))
  · intro y hy
    exact (hdictU y).mpr (hvan_g _ (hrange_zero _ hy))

end

end S_ModularCurve_XHDRModelAtP_forall_exists_orientedEtaleCrossingChart
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_forall_exists_orientedEtaleCrossingChart (solution)
