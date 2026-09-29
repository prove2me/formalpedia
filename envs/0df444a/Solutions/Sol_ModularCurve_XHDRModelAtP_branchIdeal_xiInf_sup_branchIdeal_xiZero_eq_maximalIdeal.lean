-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/63b9e9c1-a627-5806-a96b-b4f229a0face

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_ModularCurve_XHDRModelAtP_finite_crossings
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_ModularCurve_XHDRModelAtP_xiInf_ne_xiZero
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
import Theorems.Thm_ModularCurve_XHDRModelAtP_xi_mem_preimage_smoothLocus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve IsLocalRing ModularCurve.XHDRLevel
open scoped MatrixGroups

noncomputable section

namespace ECL_FibN
open ModularCurve ModularCurve.XHDRLevel

theorem isIntegral_fibreN {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) :=
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  IsIntegral.of_isIso (𝔛.efib A hA ρ hρ)

theorem efib_genericPoint_eq {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))] :
    letI := (𝔛.Mfib A hA ρ hρ).isIntegral
    (𝔛.efib A hA ρ hρ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C) =
      genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) := by
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  refine IsGenericPoint.eq (S := ⊤) ?_ (genericPoint_spec _)
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  exact 𝔛.efib_genericPoint_specializes A hA ρ hρ y

end ECL_FibN

end

section Unit1

noncomputable section

namespace ECL_TransvPlumb

private theorem surjective_fst_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₂]
    (h : i₁.base (genericPoint C) ∈ Set.range ⇑i₂.base) :
    Function.Surjective ⇑(pullback.fst i₁ i₂).base := by
  have hsub : Set.range ⇑i₁.base ⊆ Set.range ⇑i₂.base := by
    have h1 : Set.range ⇑i₁.base = ⇑i₁.base '' closure {genericPoint C} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₁.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₂.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c c' hc'.symm
  exact ⟨z, hz⟩

private theorem surjective_snd_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₁]
    (h : i₂.base (genericPoint C) ∈ Set.range ⇑i₁.base) :
    Function.Surjective ⇑(pullback.snd i₁ i₂).base := by
  have hsub : Set.range ⇑i₂.base ⊆ Set.range ⇑i₁.base := by
    have h1 : Set.range ⇑i₂.base = ⇑i₂.base '' closure {genericPoint C} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₂.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₁.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c' c hc'
  exact ⟨z, hz⟩

section Engine
variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

private theorem not_surjective_of_crossing
    (f : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) → ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) :
    ¬ Function.Surjective f := by
  intro hf
  haveI := ECL_FibN.isIntegral_fibreN 𝔛 A hA ρ hρ
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ 𝔛.smooth0
  haveI : Infinite ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) := by
    have h := AlgebraicCurve.infinite_setOf_isClosed_singleton
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))
    exact Set.infinite_univ_iff.mp (h.mono (Set.subset_univ _))
  haveI : Infinite ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) := Infinite.of_surjective f hf
  haveI : Finite ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) := 𝔛.finite_crossings A hA ρ hρ
  exact not_finite ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))

private theorem comp0_genericPoint_notMem_range_comp1 [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))] :
    (𝔛.comp A hA ρ hρ 0).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ∉ Set.range ⇑(𝔛.comp A hA ρ hρ 1).base := fun h =>
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  not_surjective_of_crossing 𝔛 A hA ρ hρ _ (surjective_fst_of_mem_range _ _ h)

private theorem comp1_genericPoint_notMem_range_comp0 [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))] :
    (𝔛.comp A hA ρ hρ 1).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ∉ Set.range ⇑(𝔛.comp A hA ρ hρ 0).base := fun h =>
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  not_surjective_of_crossing 𝔛 A hA ρ hρ _ (surjective_snd_of_mem_range _ _ h)

theorem eq_of_specializes_comp0_genericPoint [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hz : z ⤳ (𝔛.comp A hA ρ hρ 0).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))) :
    z = (𝔛.comp A hA ρ hρ 0).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  rcases 𝔛.comp_jointly_surjective A hA ρ hρ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have hc : c ⤳ genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) :=
      (𝔛.comp A hA ρ hρ 0).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]
  · exact absurd (hz.mem_closed (𝔛.comp A hA ρ hρ 1).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (comp0_genericPoint_notMem_range_comp1 𝔛 A hA ρ hρ)

theorem eq_of_specializes_comp1_genericPoint [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hz : z ⤳ (𝔛.comp A hA ρ hρ 1).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))) :
    z = (𝔛.comp A hA ρ hρ 1).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  rcases 𝔛.comp_jointly_surjective A hA ρ hρ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact absurd (hz.mem_closed (𝔛.comp A hA ρ hρ 0).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (comp1_genericPoint_notMem_range_comp0 𝔛 A hA ρ hρ)
  · have hc : c ⤳ genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) :=
      (𝔛.comp A hA ρ hρ 1).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]

end Engine

section Local
variable {p : ℕ} (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

def fibreMapOfComp {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A) (τB : R p →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) : fibre (Γ := Γ) (hj := hj) τB ⟶ fibre (Γ := Γ) (hj := hj) τA :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h])

@[reassoc]
theorem fibreMapOfComp_fst {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A) (τB : R p →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) :
    fibreMapOfComp Γ hj τA τB φ h ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [fibreMapOfComp, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc]
theorem fibreMapOfComp_snd {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A) (τB : R p →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) :
    fibreMapOfComp Γ hj τA τB φ h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ) :=
  pullback.lift_snd _ _ _

theorem bcMap_eq_fibreMapOfComp {O : Type} [CommRing O] (ρO : R p →+* O) {κ : Type} [CommRing κ] (toκ : O →+* κ)
    {toκ' : R p →+* κ} (hto : toκ.comp ρO = toκ') :
    bcMap Γ hj ρO toκ hto = fibreMapOfComp Γ hj ρO toκ' toκ hto := by
  apply pullback.hom_ext
  · rw [fibreMapOfComp_fst, bcMap_fst]
  · rw [fibreMapOfComp_snd, bcMap_snd]

theorem fibreMapOfComp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (τA : R p →+* A) (τB : R p →+* B) (τC : R p →+* C)
    (φ : A →+* B) (hφ : φ.comp τA = τB) (ψ : B →+* C) (hψ : ψ.comp τB = τC)
    (χ : A →+* C) (hχ : χ.comp τA = τC) (e : ψ.comp φ = χ) :
    fibreMapOfComp Γ hj τB τC ψ hψ ≫ fibreMapOfComp Γ hj τA τB φ hφ =
      fibreMapOfComp Γ hj τA τC χ hχ := by
  subst e
  apply pullback.hom_ext
  · simp only [Category.assoc, fibreMapOfComp_fst]
  · simp only [Category.assoc, fibreMapOfComp_snd, fibreMapOfComp_snd_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem isPullback_fibreMapOfComp {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A) (τB : R p →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) :
    IsPullback (fibreMapOfComp Γ hj τA τB φ h)
      (pullback.snd (toBase p Γ hj) (Spec.map (CommRingCat.ofHom τB)))
      (pullback.snd (toBase p Γ hj) (Spec.map (CommRingCat.ofHom τA)))
      (Spec.map (CommRingCat.ofHom φ)) := by
  have hρι : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom τA) = Spec.map (CommRingCat.ofHom τB) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  have key : IsPullback (fibreMapOfComp Γ hj τA τB φ h ≫ pullback.fst (toBase p Γ hj) _)
      (pullback.snd (toBase p Γ hj) (Spec.map (CommRingCat.ofHom τB))) (toBase p Γ hj)
      (Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom τA)) := by
    rw [fibreMapOfComp_fst, hρι]
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right key (fibreMapOfComp_snd Γ hj τA τB φ h) (IsPullback.of_hasPullback _ _)

theorem isClosedImmersion_fibreMapOfComp {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A)
    (τB : R p →+* B) (φ : A →+* B) (h : φ.comp τA = τB) (hφ : Function.Surjective φ) :
    IsClosedImmersion (fibreMapOfComp Γ hj τA τB φ h) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) := IsClosedImmersion.spec_of_surjective _ hφ
  exact MorphismProperty.of_isPullback (isPullback_fibreMapOfComp Γ hj τA τB φ h).flip inferInstance

theorem flat_fibreMapOfComp {A B : Type} [Field A] [Field B] (τA : R p →+* A)
    (τB : R p →+* B) (φ : A →+* B) (h : φ.comp τA = τB) :
    Flat (fibreMapOfComp Γ hj τA τB φ h) := by
  haveI : Flat (Spec.map (CommRingCat.ofHom φ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := φ.toAlgebra
    show RingHom.Flat (algebraMap A B)
    rw [RingHom.Flat]
    convert (inferInstance : Module.Flat A B)
  exact MorphismProperty.of_isPullback (isPullback_fibreMapOfComp Γ hj τA τB φ h).flip inferInstance

theorem surjective_fibreMapOfComp {A B : Type} [Field A] [Field B] (τA : R p →+* A)
    (τB : R p →+* B) (φ : A →+* B) (h : φ.comp τA = τB) :
    Surjective (fibreMapOfComp Γ hj τA τB φ h) := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom φ)) := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  exact MorphismProperty.of_isPullback (isPullback_fibreMapOfComp Γ hj τA τB φ h).flip inferInstance

variable {O : Type} [CommRing O] [IsLocalRing O] (ρO : R p →+* O)
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  {κ : Type} [Field κ] [CharP κ p] (toκ : O →+* κ) {toκ' : R p →+* κ} (hto : toκ.comp ρO = toκ')

include hϖ in

theorem toκ_maximalIdeal [Fact p.Prime] (a : O) (ha : a ∈ IsLocalRing.maximalIdeal O) : toκ a = 0 := by
  rw [hϖ, Ideal.mem_span_singleton] at ha
  obtain ⟨r, rfl⟩ := ha
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

def ι [Fact p.Prime] : IsLocalRing.ResidueField O →+* κ :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) toκ (toκ_maximalIdeal hϖ toκ)

include hto in
theorem ι_comp [Fact p.Prime] : (ι hϖ toκ).comp ((IsLocalRing.residue O).comp ρO) = toκ' := by
  subst hto; exact RingHom.ext fun _ => rfl

theorem bcMap_eq_comp [Fact p.Prime] :
    bcMap Γ hj ρO toκ hto =
      fibreMapOfComp Γ hj ((IsLocalRing.residue O).comp ρO) toκ' (ι hϖ toκ) (ι_comp ρO hϖ toκ hto) ≫
        bcMap Γ hj ρO (IsLocalRing.residue O) rfl := by
  subst hto
  rw [bcMap_eq_fibreMapOfComp, bcMap_eq_fibreMapOfComp,
    fibreMapOfComp_comp (χ := toκ) (hχ := rfl) (e := RingHom.ext fun _ => rfl)]

include hϖ in

theorem exists_bcMap_residue_eq (y : ↥(XO Γ hj ρO))
    (hy : y ∉ (XO.toBase Γ hj ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    ∃ y₀, (bcMap Γ hj ρO (IsLocalRing.residue O) rfl).base y₀ = y := by
  set s := (XO.toBase Γ hj ρO).base y with hs
  have hps : ((p : ℕ) : O) ∈ s.asIdeal := by
    by_contra h
    exact hy h
  have hsm : s = IsLocalRing.closedPoint O := by
    apply PrimeSpectrum.ext
    have hle : IsLocalRing.maximalIdeal O ≤ s.asIdeal := by
      rw [hϖ, Ideal.span_singleton_le_iff_mem]
      exact hps
    exact ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le s.isPrime.ne_top hle).symm
  have hpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = s := by
    rw [hsm]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  rw [bcMap_eq_fibreMapOfComp]
  obtain ⟨y₀, hy₀, -⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_fibreMapOfComp Γ hj ρO ((IsLocalRing.residue O).comp ρO) (IsLocalRing.residue O) rfl) y
    (IsLocalRing.closedPoint _) (by rw [hpt])
  exact ⟨y₀, hy₀⟩

end Local

section Stalks
variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  {O : Type} [CommRing O] [IsLocalRing O] (ρO : R p →+* O)
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  {κ : Type} [Field κ] [CharP κ p] (toκ : O →+* κ) {toκ' : R p →+* κ} (htoκ : toκ.comp ρO = toκ')

private theorem g_comp_j : (fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) _ (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ)) ≫ (bcMap (ΓM M H) hj ρO (IsLocalRing.residue O) rfl) = bcMap (ΓM M H) hj ρO toκ htoκ := (bcMap_eq_comp (ΓM M H) hj ρO hϖ toκ htoκ).symm

private theorem flat_stalkMap_g (y : ↥(fibre (Γ := ΓM M H) (hj := hj) toκ')) : (((fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) _ (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ))).stalkMap y).hom.Flat :=
  haveI := flat_fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) _ (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ)
  Flat.stalkMap _ y

private theorem stalkMap_j_surjective (x : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue O).comp ρO))) :
    Function.Surjective (((bcMap (ΓM M H) hj ρO (IsLocalRing.residue O) rfl)).stalkMap x) := by
  haveI : IsClosedImmersion (bcMap (ΓM M H) hj ρO (IsLocalRing.residue O) rfl) := by
    rw [bcMap_eq_fibreMapOfComp]
    exact isClosedImmersion_fibreMapOfComp _ _ _ _ _ rfl Ideal.Quotient.mk_surjective
  exact ((bcMap (ΓM M H) hj ρO (IsLocalRing.residue O) rfl)).stalkMap_surjective x

private theorem stalkMap_bcMap_eq (y : ↥(fibre (Γ := ΓM M H) (hj := hj) toκ')) :
    (bcMap (ΓM M H) hj ρO toκ htoκ).stalkMap y =
      ((XO (ΓM M H) hj ρO).presheaf.stalkCongr
          (.of_eq (by rw [← Scheme.Hom.comp_apply, g_comp_j ρO hϖ toκ htoκ]))).hom ≫
        ((bcMap (ΓM M H) hj ρO (IsLocalRing.residue O) rfl)).stalkMap (((fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) _ (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ))).base y) ≫ ((fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) _ (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ))).stalkMap y := by
  rw [Scheme.Hom.stalkMap_congr_hom _ _ (g_comp_j ρO hϖ toκ htoκ).symm y, Scheme.Hom.stalkMap_comp]
  rfl

end Stalks

end ECL_TransvPlumb

end

end Unit1

section Unit2

set_option autoImplicit false

open IsLocalRing AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ECL_Transv

private theorem fromSpecStalk_comap_closedPoint_spec {X : Scheme} {x ξ : X} (h : ξ ⤳ x) :
    X.fromSpecStalk x (PrimeSpectrum.comap (X.presheaf.stalkSpecializes h).hom (closedPoint (X.presheaf.stalk ξ))) =
      ξ := by
  have e := congrArg (fun f : Spec (X.presheaf.stalk ξ) ⟶ X => f (closedPoint (X.presheaf.stalk ξ)))
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) h)
  simpa only [Scheme.Hom.comp_apply, Spec.map_apply, Scheme.fromSpecStalk_closedPoint] using e

private theorem exists_specializes_and_eq_comap_stalkSpecializes {X : Scheme} (y : X)
    (𝔮 : Ideal (X.presheaf.stalk y)) [𝔮.IsPrime] :
    ∃ (z : X) (hz : z ⤳ y),
      𝔮 = Ideal.comap (X.presheaf.stalkSpecializes hz).hom (maximalIdeal (X.presheaf.stalk z)) := by
  let p : Spec (X.presheaf.stalk y) := ⟨𝔮, inferInstance⟩
  have hz : X.fromSpecStalk y p ⤳ y := by
    have hmem : X.fromSpecStalk y p ∈ Set.range (X.fromSpecStalk y) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hmem
  refine ⟨X.fromSpecStalk y p, hz, ?_⟩
  have hinj : Function.Injective (X.fromSpecStalk y) := (X.fromSpecStalk y).isEmbedding.injective
  have h1 := hinj (fromSpecStalk_comap_closedPoint_spec hz)
  exact (congrArg PrimeSpectrum.asIdeal h1).symm

private theorem comap_stalkSpecializes_refl_maximalIdeal {X : Scheme} (y : X) :
    Ideal.comap (X.presheaf.stalkSpecializes (specializes_refl y)).hom (maximalIdeal (X.presheaf.stalk y)) =
      maximalIdeal (X.presheaf.stalk y) := by
  simp

private theorem eq_maximalIdeal_or_eq_branchIdeal_or_eq_branchIdeal {C X : Scheme} (i₁ i₂ : C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hsurj : ∀ z : X, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (η : C) (hη : ∀ c : C, c ≠ η → IsClosed ({c} : Set C)) {y : X} (h₁ : i₁.base η ⤳ y) (h₂ : i₂.base η ⤳ y)
    (𝔮 : Ideal (X.presheaf.stalk y)) [𝔮.IsPrime] :
    𝔮 = maximalIdeal (X.presheaf.stalk y) ∨ 𝔮 = Scheme.branchIdeal h₁ ∨ 𝔮 = Scheme.branchIdeal h₂ := by
  obtain ⟨z, hz, rfl⟩ := exists_specializes_and_eq_comap_stalkSpecializes y 𝔮
  rcases hsurj z with ⟨c, hc⟩ | ⟨c, hc⟩
  · by_cases hcη : c = η
    · subst hcη
      subst hc
      exact Or.inr (Or.inl rfl)
    · have hcl : IsClosed ({z} : Set X) := by
        rw [← hc, ← Set.image_singleton]
        exact i₁.isClosedEmbedding.isClosedMap _ (hη c hcη)
      have hyz : y = z := hz.mem_closed hcl (Set.mem_singleton z)
      subst hyz
      exact Or.inl (comap_stalkSpecializes_refl_maximalIdeal y)
  · by_cases hcη : c = η
    · subst hcη
      subst hc
      exact Or.inr (Or.inr rfl)
    · have hcl : IsClosed ({z} : Set X) := by
        rw [← hc, ← Set.image_singleton]
        exact i₂.isClosedEmbedding.isClosedMap _ (hη c hcη)
      have hyz : y = z := hz.mem_closed hcl (Set.mem_singleton z)
      subst hyz
      exact Or.inl (comap_stalkSpecializes_refl_maximalIdeal y)

private theorem eq_of_branchIdeal_eq {X : Scheme} {x ξ₁ ξ₂ : X} (h₁ : ξ₁ ⤳ x) (h₂ : ξ₂ ⤳ x)
    (h : Scheme.branchIdeal h₁ = Scheme.branchIdeal h₂) : ξ₁ = ξ₂ := by
  have hpt : PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₁).hom (closedPoint (X.presheaf.stalk ξ₁)) =
      PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₂).hom (closedPoint (X.presheaf.stalk ξ₂)) :=
    PrimeSpectrum.ext h
  rw [← fromSpecStalk_comap_closedPoint_spec h₁, ← fromSpecStalk_comap_closedPoint_spec h₂, hpt]

private theorem specializes_of_branchIdeal_le {X : Scheme} {y ξ₁ ξ₂ : X} (h₁ : ξ₁ ⤳ y) (h₂ : ξ₂ ⤳ y)
    (hle : Scheme.branchIdeal h₁ ≤ Scheme.branchIdeal h₂) : ξ₁ ⤳ ξ₂ := by
  have hsp : (PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₁).hom (closedPoint (X.presheaf.stalk ξ₁)) :
      Spec (X.presheaf.stalk y)) ⤳
        PrimeSpectrum.comap (X.presheaf.stalkSpecializes h₂).hom (closedPoint (X.presheaf.stalk ξ₂)) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have := hsp.map (X.fromSpecStalk y).continuous
  rwa [fromSpecStalk_comap_closedPoint_spec h₁, fromSpecStalk_comap_closedPoint_spec h₂] at this

private theorem branchIdeal_ne_maximalIdeal_and_not_le {C X : Scheme} (i₁ i₂ : C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (η : C) (hη : ∀ c : C, c ≠ η → IsClosed ({c} : Set C)) {y : X} (h₁ : i₁.base η ⤳ y) (h₂ : i₂.base η ⤳ y)
    (hne : i₁.base η ≠ i₂.base η) (hy₁ : i₁.base η ≠ y) (hy₂ : i₂.base η ≠ y) :
    Scheme.branchIdeal h₁ ≠ maximalIdeal (X.presheaf.stalk y) ∧
      Scheme.branchIdeal h₂ ≠ maximalIdeal (X.presheaf.stalk y) ∧
      ¬ Scheme.branchIdeal h₁ ≤ Scheme.branchIdeal h₂ ∧ ¬ Scheme.branchIdeal h₂ ≤ Scheme.branchIdeal h₁ := by
  refine ⟨fun h => hy₁ ?_, fun h => hy₂ ?_, fun hle => ?_, fun hle => ?_⟩
  · exact eq_of_branchIdeal_eq h₁ (specializes_refl y) (h.trans (comap_stalkSpecializes_refl_maximalIdeal y).symm)
  · exact eq_of_branchIdeal_eq h₂ (specializes_refl y) (h.trans (comap_stalkSpecializes_refl_maximalIdeal y).symm)
  ·

    have hsp := specializes_of_branchIdeal_le h₁ h₂ hle
    obtain ⟨c, hc⟩ : i₂.base η ∈ Set.range i₁.base :=
      hsp.mem_closed i₁.isClosedEmbedding.isClosed_range ⟨η, rfl⟩
    by_cases hcη : c = η
    · exact hne (by rw [← hc, hcη])
    · have hcl : IsClosed ({i₂.base η} : Set X) := by
        rw [← hc, ← Set.image_singleton]
        exact i₁.isClosedEmbedding.isClosedMap _ (hη c hcη)
      exact hy₂ (h₂.mem_closed hcl (Set.mem_singleton _)).symm
  · have hsp := specializes_of_branchIdeal_le h₂ h₁ hle
    obtain ⟨c, hc⟩ : i₁.base η ∈ Set.range i₂.base :=
      hsp.mem_closed i₂.isClosedEmbedding.isClosed_range ⟨η, rfl⟩
    by_cases hcη : c = η
    · exact hne (by rw [← hc, hcη])
    · have hcl : IsClosed ({i₁.base η} : Set X) := by
        rw [← hc, ← Set.image_singleton]
        exact i₂.isClosedEmbedding.isClosedMap _ (hη c hcη)
      exact hy₁ (h₁.mem_closed hcl (Set.mem_singleton _)).symm

private theorem eq_branchIdeal_of_isPrime_of_le {X : Scheme} {y ξ₁ ξ₂ : X} (h₁ : ξ₁ ⤳ y) (h₂ : ξ₂ ⤳ y)
    (htri : ∀ 𝔮 : Ideal (X.presheaf.stalk y), 𝔮.IsPrime →
      𝔮 = maximalIdeal (X.presheaf.stalk y) ∨ 𝔮 = Scheme.branchIdeal h₁ ∨ 𝔮 = Scheme.branchIdeal h₂)
    (hP : Scheme.branchIdeal h₁ ≠ maximalIdeal (X.presheaf.stalk y))
    (hQP : ¬ Scheme.branchIdeal h₂ ≤ Scheme.branchIdeal h₁)
    (J : Ideal (X.presheaf.stalk y)) [hJp : J.IsPrime] (hJ : J ≤ Scheme.branchIdeal h₁) :
    J = Scheme.branchIdeal h₁ := by
  rcases htri J hJp with hm | hp | hq
  · subst hm
    exact absurd (le_antisymm (le_maximalIdeal (Scheme.branchIdeal_isPrime h₁).ne_top) hJ) hP
  · exact hp
  · subst hq
    exact absurd hJ hQP

section Frame

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  (hpM2 : ¬ p ^ 2 ∣ M) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

private theorem comp0_genericPoint_specializes [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) :
    (𝔛.comp A hA ρ hρ 0).base (genericPoint (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ⤳
      (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) :=
  (genericPoint_specializes _).map (𝔛.comp A hA ρ hρ 0).continuous

private theorem comp1_snd_eq_comp0_fst (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) :
    (𝔛.comp A hA ρ hρ 1).base ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) =
      (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

private theorem comp1_genericPoint_specializes [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) :
    (𝔛.comp A hA ρ hρ 1).base (genericPoint (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ⤳
      (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) :=
  ((genericPoint_specializes _).map (𝔛.comp A hA ρ hρ 1).continuous).trans
    (specializes_of_eq (comp1_snd_eq_comp0_fst 𝔛 A hA ρ hρ n))

private theorem frame_eq_maximalIdeal_or_eq_branchIdeal_or_eq_branchIdeal [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (𝔮 : Ideal ((fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).presheaf.stalk
      ((𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)))) [𝔮.IsPrime] :
    𝔮 = maximalIdeal _ ∨ 𝔮 = Scheme.branchIdeal (comp0_genericPoint_specializes 𝔛 A hA ρ hρ n) ∨
      𝔮 = Scheme.branchIdeal (comp1_genericPoint_specializes 𝔛 A hA ρ hρ n) :=
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ 𝔛.smooth0
  eq_maximalIdeal_or_eq_branchIdeal_or_eq_branchIdeal (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) (𝔛.comp_jointly_surjective A hA ρ hρ)
    (genericPoint (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (fun c hc => AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) c hc)
    (comp0_genericPoint_specializes 𝔛 A hA ρ hρ n) (comp1_genericPoint_specializes 𝔛 A hA ρ hρ n) 𝔮

include hpM2 hHp in

private theorem frame_branchIdeal_ne_maximalIdeal_and_not_le
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : R p →+* O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ) [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (hy₁ : (𝔛.comp A hA ρ hρ 0).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ≠
      (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n))
    (hy₂ : (𝔛.comp A hA ρ hρ 1).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ≠
      (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)) :
    Scheme.branchIdeal (comp0_genericPoint_specializes 𝔛 A hA ρ hρ n) ≠ maximalIdeal _ ∧
      Scheme.branchIdeal (comp1_genericPoint_specializes 𝔛 A hA ρ hρ n) ≠ maximalIdeal _ ∧
      ¬ Scheme.branchIdeal (comp0_genericPoint_specializes 𝔛 A hA ρ hρ n) ≤
          Scheme.branchIdeal (comp1_genericPoint_specializes 𝔛 A hA ρ hρ n) ∧
      ¬ Scheme.branchIdeal (comp1_genericPoint_specializes 𝔛 A hA ρ hρ n) ≤
          Scheme.branchIdeal (comp0_genericPoint_specializes 𝔛 A hA ρ hρ n) :=
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ 𝔛.smooth0
  have hne : (𝔛.comp A hA ρ hρ 0).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ≠
      (𝔛.comp A hA ρ hρ 1).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := fun h =>
    ModularCurve.XHDRModelAtP.xiInf_ne_xiZero p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ
      (by
        show (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base _ = (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base _
        simp only [Scheme.Hom.comp_apply]
        rw [ECL_FibN.efib_genericPoint_eq 𝔛 A hA ρ hρ]
        rw [h])
  branchIdeal_ne_maximalIdeal_and_not_le (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (fun c hc => AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) c hc)
    (comp0_genericPoint_specializes 𝔛 A hA ρ hρ n) (comp1_genericPoint_specializes 𝔛 A hA ρ hρ n) hne hy₁ hy₂

omit [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] in

private theorem bcMap_comp_fst (O : Type) [CommRing O] (ρO : R p →+* O) (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ) :
    bcMap (ΓM M H) hj ρO toκ htoκ ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)) =
      pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) := by
  exact bcMap_fst _ _ _ _ _

include hpM2 hHp in

private theorem comp0_genericPoint_ne_and_comp1_genericPoint_ne (O : Type) [CommRing O] (ρO : R p →+* O) (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) :
    (𝔛.comp A hA ρ hρ 0).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ≠
        (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) ∧
      (𝔛.comp A hA ρ hρ 1).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ≠
        (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) := by
  have hy : (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) ∈
        Set.range (𝔛.comp A hA ρ hρ 0).base ∧
      (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) ∈
        Set.range (𝔛.comp A hA ρ hρ 1).base :=
    ⟨⟨_, rfl⟩, ⟨(pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n, comp1_snd_eq_comp0_fst 𝔛 A hA ρ hρ n⟩⟩
  have hsm := ModularCurve.XHDRModelAtP.xi_mem_preimage_smoothLocus p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO toκ htoκ
  have key : ∀ z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      (bcMap (ΓM M H) hj ρO toκ htoκ).base z ∈
          (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)) ⁻¹ᵁ 𝔛.smoothLocus) →
        z ∈ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) ⁻¹ᵁ 𝔛.smoothLocus) := by
    intro z hz
    rw [Scheme.Hom.mem_preimage] at hz ⊢
    rw [← bcMap_comp_fst (A := A) (ρ := ρ) O ρO toκ htoκ, Scheme.Hom.comp_apply]
    exact hz
  have h1 := key _ (by
    have := hsm.1
    rwa [show 𝔛.ξinf A hA ρ hρ ρO toκ htoκ = (bcMap (ΓM M H) hj ρO toκ htoκ).base ((𝔛.comp A hA ρ hρ 0).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))) from by
      rw [← ECL_FibN.efib_genericPoint_eq 𝔛 A hA ρ hρ]; rfl] at this)
  have h2 := key _ (by
    have := hsm.2
    rwa [show 𝔛.ξzero A hA ρ hρ ρO toκ htoκ = (bcMap (ΓM M H) hj ρO toκ htoκ).base ((𝔛.comp A hA ρ hρ 1).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))) from by
      rw [← ECL_FibN.efib_genericPoint_eq 𝔛 A hA ρ hρ]; rfl] at this)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (ModularCurve.XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter p M H hpM hpM2 hj 𝔛 A hA ρ hρ _).mp h1
      (by rw [h]; exact hy)
  · exact (ModularCurve.XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter p M H hpM hpM2 hj 𝔛 A hA ρ hρ _).mp h2
      (by rw [h]; exact hy)

end Frame

end ECL_Transv

end Unit2

section Unit3

set_option autoImplicit false

open TensorProduct

private theorem eq_bot_of_forall_isPrime_le' {T : Type*} [CommRing T] [IsReduced T] {I : Ideal T}
    (h : ∀ 𝔮 : Ideal T, 𝔮.IsPrime → I ≤ 𝔮) : I = ⊥ := by
  refine le_bot_iff.mp ?_
  calc I ≤ sInf { J : Ideal T | J.IsPrime } := le_sInf fun 𝔮 h𝔮 => h 𝔮 h𝔮
    _ = nilradical T := (nilradical_eq_sInf T).symm
    _ = ⊥ := nilradical_eq_zero T

private theorem flat_quotient_map_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (P : Ideal A) : Module.Flat (A ⧸ P) (B ⧸ P.map (algebraMap A B)) :=
  Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B P).toLinearEquiv

private theorem isSMulRegular_quotient_map_of_notMem {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] (P : Ideal A) [P.IsPrime] {a : A} (ha : a ∉ P) :
    IsSMulRegular (B ⧸ P.map (algebraMap A B)) (algebraMap A (B ⧸ P.map (algebraMap A B)) a) := by
  haveI := flat_quotient_map_of_flat (A := A) (B := B) P
  have hreg : IsSMulRegular (A ⧸ P) (Ideal.Quotient.mk P a) :=
    mul_right_injective₀ (by simpa [Ideal.Quotient.eq_zero_iff_mem] using ha)
  have h := hreg.of_flat (S := B ⧸ P.map (algebraMap A B))
  rwa [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply] at h

private theorem map_eq_of_flat_of_forall_le {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [IsReduced B] (P : Ideal A) [P.IsPrime] {𝔭' : Ideal B}
    (h1 : P.map (algebraMap A B) ≤ 𝔭')
    (h2 : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮.comap (algebraMap A B) ≤ P → 𝔭' ≤ 𝔮) :
    P.map (algebraMap A B) = 𝔭' := by
  refine le_antisymm h1 fun p hq => ?_
  let S : Submonoid B := P.primeCompl.map (algebraMap A B)

  have hbot : 𝔭'.map (algebraMap B (Localization S)) = ⊥ := by
    refine eq_bot_of_forall_isPrime_le' fun 𝔔 h𝔔 => ?_
    obtain ⟨hprime, hdisj⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint S (Localization S) 𝔔).mp h𝔔
    refine Ideal.map_le_iff_le_comap.mpr (h2 _ hprime fun a ha => ?_)
    by_contra ha'
    exact Set.disjoint_left.mp hdisj (Submonoid.mem_map_of_mem (algebraMap A B) (ha' : a ∈ P.primeCompl))
      ha
  have hq0 : algebraMap B (Localization S) p = 0 := by
    have : algebraMap B (Localization S) p ∈ 𝔭'.map (algebraMap B (Localization S)) :=
      Ideal.mem_map_of_mem _ hq
    simpa [hbot] using this
  obtain ⟨⟨s, hs⟩, hsq⟩ := (IsLocalization.map_eq_zero_iff S (Localization S) p).mp hq0
  obtain ⟨a, ha, rfl⟩ := Submonoid.mem_map.mp hs

  have hreg := isSMulRegular_quotient_map_of_notMem (B := B) P (ha : a ∉ P)
  have hzero : algebraMap A (B ⧸ P.map (algebraMap A B)) a • Ideal.Quotient.mk _ p =
      algebraMap A (B ⧸ P.map (algebraMap A B)) a • (0 : B ⧸ P.map (algebraMap A B)) := by
    rw [smul_zero, smul_eq_mul, IsScalarTower.algebraMap_apply A B (B ⧸ P.map (algebraMap A B)),
      Ideal.Quotient.algebraMap_eq, ← map_mul]
    simpa using congrArg (Ideal.Quotient.mk (P.map (algebraMap A B))) hsq
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hreg hzero)

private theorem map_eq_of_flat_of_forall_le_ringHom {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (hψ : ψ.Flat) [IsReduced B] (P : Ideal A) [P.IsPrime] {𝔭' : Ideal B} (h1 : P.map ψ ≤ 𝔭')
    (h2 : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮.comap ψ ≤ P → 𝔭' ≤ 𝔮) : P.map ψ = 𝔭' := by
  letI : Algebra A B := ψ.toAlgebra
  haveI : Module.Flat A B := hψ
  exact map_eq_of_flat_of_forall_le P h1 h2

end Unit3

section Unit4

set_option autoImplicit false

private theorem eq_under_of_le_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (𝔭' : Ideal B) [𝔭'.IsPrime]
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ 𝔭' → 𝔮 = 𝔭') {p : Ideal A} [p.IsPrime]
    (hle : p ≤ 𝔭'.under A) : p = 𝔭'.under A := by
  obtain ⟨𝔮, h𝔮le, h𝔮prime, h𝔮over⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := 𝔭'.under A) 𝔭' hle
  rw [hmin 𝔮 h𝔮prime h𝔮le] at h𝔮over
  exact h𝔮over.over

private theorem eq_comap_of_le_of_flat_ringHom {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (hψ : ψ.Flat) (𝔭' : Ideal B) [𝔭'.IsPrime]
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ 𝔭' → 𝔮 = 𝔭') {p : Ideal A} [p.IsPrime]
    (hle : p ≤ 𝔭'.comap ψ) : p = 𝔭'.comap ψ := by
  letI : Algebra A B := ψ.toAlgebra
  haveI : Module.Flat A B := hψ
  exact eq_under_of_le_of_flat 𝔭' hmin hle

private theorem not_le_comap_of_ne_of_flat_ringHom {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (hψ : ψ.Flat) (𝔭' : Ideal B) [𝔭'.IsPrime]
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ 𝔭' → 𝔮 = 𝔭') {p : Ideal A} [p.IsPrime]
    (hne : p ≠ 𝔭'.comap ψ) : ¬ p ≤ 𝔭'.comap ψ :=
  fun hle => hne (eq_comap_of_le_of_flat_ringHom ψ hψ 𝔭' hmin hle)

end Unit4

section Unit5

set_option autoImplicit false

private theorem eq_of_isRadical_of_le_of_forall_le {B : Type*} [CommRing B] {I 𝔭 : Ideal B}
    (hI : I.IsRadical) [𝔭.IsPrime] (hle : I ≤ 𝔭)
    (hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → I ≤ 𝔮 → 𝔭 ≤ 𝔮) : I = 𝔭 := by
  refine le_antisymm hle ?_
  rw [← Ideal.radical_eq_iff.mpr hI, Ideal.radical_eq_sInf]
  exact le_sInf fun 𝔮 h𝔮 => hmin 𝔮 h𝔮.2 h𝔮.1

private theorem le_of_map_le_map_of_faithfullyFlat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {I J : Ideal A}
    (h : I.map (algebraMap A B) ≤ J.map (algebraMap A B)) : I ≤ J := by
  calc I = (I.map (algebraMap A B)).comap (algebraMap A B) :=
        (Ideal.comap_map_eq_self_of_faithfullyFlat I).symm
    _ ≤ (J.map (algebraMap A B)).comap (algebraMap A B) := Ideal.comap_mono h
    _ = J := Ideal.comap_map_eq_self_of_faithfullyFlat J

private theorem le_of_map_le_map_of_flat_of_isLocalHom {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) (hf : f.Flat) [IsLocalHom f] {I J : Ideal A}
    (h : I.map f ≤ J.map f) : I ≤ J := by
  letI : Algebra A B := f.toAlgebra
  haveI : Module.Flat A B := hf
  haveI : IsLocalHom (algebraMap A B) := ‹IsLocalHom f›
  haveI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact le_of_map_le_map_of_faithfullyFlat (A := A) (B := B) h

private theorem sup_eq_maximalIdeal_of_map_maximalIdeal_le {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) (hf : f.Flat) [IsLocalHom f] {P Q : Ideal A}
    (hP : P ≠ ⊤) (hQ : Q ≠ ⊤)
    (h : (IsLocalRing.maximalIdeal A).map f ≤ (P ⊔ Q).map f) :
    P ⊔ Q = IsLocalRing.maximalIdeal A :=
  le_antisymm (sup_le (IsLocalRing.le_maximalIdeal hP) (IsLocalRing.le_maximalIdeal hQ))
    (le_of_map_le_map_of_flat_of_isLocalHom f hf h)

end Unit5

section Unit6

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace

universe u

namespace TransvChair

variable {X Y : Scheme.{u}}

private theorem comap_stalkMap_comap_stalkSpecializes (f : X ⟶ Y) {ξ x : X} (h : ξ ⤳ x) :
    ((maximalIdeal (X.presheaf.stalk ξ)).comap (X.presheaf.stalkSpecializes h).hom).comap
        (f.stalkMap x).hom =
      (maximalIdeal (Y.presheaf.stalk (f.base ξ))).comap
        (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h)).hom := by
  rw [Ideal.comap_comap, ← CommRingCat.hom_comp, ← Scheme.Hom.stalkSpecializes_stalkMap f ξ x h,
    CommRingCat.hom_comp, ← Ideal.comap_comap, maximalIdeal_comap]

private theorem ker_stalkMap_le_comap_stalkSpecializes (f : X ⟶ Y) {ξ x : X} (h : ξ ⤳ x)
    [Nontrivial (X.presheaf.stalk ξ)] :
    RingHom.ker (f.stalkMap x).hom ≤
      (maximalIdeal (Y.presheaf.stalk (f.base ξ))).comap
        (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h)).hom := by
  intro s hs
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu' := hu.map (f.stalkMap ξ).hom
  rw [Scheme.Hom.stalkSpecializes_stalkMap_apply f ξ x h, RingHom.mem_ker.mp hs, map_zero] at hu'
  exact not_isUnit_zero hu'

private theorem stalkSpecializes_surjective_of_eq {x x' : X} (e : x' = x) :
    Function.Surjective (X.presheaf.stalkSpecializes (specializes_of_eq e)).hom := by
  subst e
  intro t
  refine ⟨t, ?_⟩
  have : X.presheaf.stalkSpecializes (specializes_of_eq (rfl : x' = x')) = 𝟙 _ :=
    X.presheaf.stalkSpecializes_refl x'
  rw [this]
  rfl

private theorem isRadical_of_specLift {Z : Scheme.{u}} [IsReduced Z] (j : Z ⟶ X) (x : X)
    (K : Ideal (X.presheaf.stalk x)) [IsLocalRing ((X.presheaf.stalk x) ⧸ K)]
    [IsLocalHom (Ideal.Quotient.mk K)]
    (g : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ Z)
    (hg : g ≫ j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x)
    (hpt : (g ≫ j).base (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x)
    (hK : K ≤ RingHom.ker ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
        j.stalkMap (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K)))).hom) :
    K.IsRadical := by
  have claim : ∀ (f : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ X)
      (_ : f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x)
      (hfpt : f.base (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x) (a : X.presheaf.stalk x),
      (Scheme.stalkClosedPointTo f).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hfpt)).hom a) =
        Ideal.Quotient.mk K a := by
    intro f hf hfpt a
    subst hf
    obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
    have hqU : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x).base
        (closedPoint ((X.presheaf.stalk x) ⧸ K)) ∈ U := by
      rw [hfpt]
      exact hxU
    have e1 : (X.presheaf.stalkSpecializes (specializes_of_eq hfpt)).hom
          ((X.presheaf.germ U x hxU).hom s) =
        (X.presheaf.germ U _ hqU).hom s := by
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rw [e1, ← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk]
    rfl
  rw [Ideal.isRadical_iff_quotient_reduced]
  refine ⟨fun r ⟨m, hm⟩ => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hb : (Scheme.stalkClosedPointTo g).hom
        ((j.stalkMap (g.base (closedPoint _))).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a)) =
      Ideal.Quotient.mk K a := by
    have := claim (g ≫ j) hg hpt a
    rw [Scheme.stalkClosedPointTo_comp] at this
    first | simpa only [CommRingCat.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply] using this | exact this
  have ham : a ^ m ∈ K := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
    exact hm
  have hbm := hK ham
  rw [RingHom.mem_ker, map_pow, CommRingCat.hom_comp, RingHom.comp_apply] at hbm
  have hb0 := IsReduced.eq_zero _ ⟨m, hbm⟩
  rw [← hb]
  erw [hb0]
  exact map_zero _

private theorem isRadical_comap_ker_sup_comap_ker {C₁ C₂ : Scheme.{u}}
    (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsReduced (pullback i₁ i₂)] (z : ↥(pullback i₁ i₂)) (x : X)
    (h₁ : i₁.base ((pullback.fst i₁ i₂).base z) = x)
    (h₂ : i₂.base ((pullback.snd i₁ i₂).base z) = x) :
    ((RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom ⊔
      (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom).IsRadical := by

  let σ₁ : X.presheaf.stalk x →+* C₁.presheaf.stalk ((pullback.fst i₁ i₂).base z) :=
    (i₁.stalkMap _).hom.comp (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom
  let σ₂ : X.presheaf.stalk x →+* C₂.presheaf.stalk ((pullback.snd i₁ i₂).base z) :=
    (i₂.stalkMap _).hom.comp (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom
  have hσ₁ : Function.Surjective σ₁ :=
    (i₁.stalkMap_surjective _).comp (stalkSpecializes_surjective_of_eq h₁)
  have hσ₂ : Function.Surjective σ₂ :=
    (i₂.stalkMap_surjective _).comp (stalkSpecializes_surjective_of_eq h₂)
  have hK₁ : RingHom.ker σ₁ =
      (RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom :=
    (RingHom.comap_ker _ _).symm
  have hK₂ : RingHom.ker σ₂ =
      (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base z)).hom).comap
        (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom :=
    (RingHom.comap_ker _ _).symm
  set K := (RingHom.ker (i₁.stalkMap ((pullback.fst i₁ i₂).base z)).hom).comap
      (X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom ⊔
    (RingHom.ker (i₂.stalkMap ((pullback.snd i₁ i₂).base z)).hom).comap
      (X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom with hKdef
  have hK₁le : RingHom.ker σ₁ ≤ K := hK₁ ▸ le_sup_left
  have hK₂le : RingHom.ker σ₂ ≤ K := hK₂ ▸ le_sup_right

  have hker₁ : RingHom.ker σ₁ ≤ maximalIdeal _ := by
    intro a ha
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map σ₁
    rw [RingHom.mem_ker.mp ha] at this
    exact not_isUnit_zero this
  have hker₂ : RingHom.ker σ₂ ≤ maximalIdeal _ := by
    intro a ha
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map σ₂
    rw [RingHom.mem_ker.mp ha] at this
    exact not_isUnit_zero this
  have hKmax : K ≤ maximalIdeal _ := sup_le (hK₁ ▸ hker₁) (hK₂ ▸ hker₂)
  have hKtop : K ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top (top_le_iff.mp (h ▸ hKmax))
  haveI : Nontrivial ((X.presheaf.stalk x) ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hKtop
  haveI : IsLocalRing ((X.presheaf.stalk x) ⧸ K) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk K) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

  let α₁ : C₁.presheaf.stalk ((pullback.fst i₁ i₂).base z) →+* (X.presheaf.stalk x) ⧸ K :=
    (Ideal.Quotient.factor hK₁le).comp (RingHom.quotientKerEquivOfSurjective hσ₁).symm.toRingHom
  let α₂ : C₂.presheaf.stalk ((pullback.snd i₁ i₂).base z) →+* (X.presheaf.stalk x) ⧸ K :=
    (Ideal.Quotient.factor hK₂le).comp (RingHom.quotientKerEquivOfSurjective hσ₂).symm.toRingHom
  have hα₁ : α₁.comp σ₁ = Ideal.Quotient.mk K := by
    ext a
    simp [α₁, RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.factor_mk]
  have hα₂ : α₂.comp σ₂ = Ideal.Quotient.mk K := by
    ext a
    simp [α₂, RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.factor_mk]
  haveI : IsLocalHom α₁ := IsLocalHom.of_surjective _
    (Function.Surjective.of_comp (g := σ₁) (by rw [← RingHom.coe_comp, hα₁]; exact Ideal.Quotient.mk_surjective))
  haveI : IsLocalHom α₂ := IsLocalHom.of_surjective _
    (Function.Surjective.of_comp (g := σ₂) (by rw [← RingHom.coe_comp, hα₂]; exact Ideal.Quotient.mk_surjective))

  let p : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x
  let a₁ : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ C₁ :=
    Spec.map (CommRingCat.ofHom α₁) ≫ C₁.fromSpecStalk _
  let a₂ : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ C₂ :=
    Spec.map (CommRingCat.ofHom α₂) ≫ C₂.fromSpecStalk _
  have hring₁ : (X.presheaf.stalkSpecializes (specializes_of_eq h₁)) ≫ i₁.stalkMap _ ≫ CommRingCat.ofHom α₁ =
      CommRingCat.ofHom (Ideal.Quotient.mk K) := by
    ext a
    change α₁ (σ₁ a) = Ideal.Quotient.mk K a
    rw [← RingHom.comp_apply, hα₁]
  have hring₂ : (X.presheaf.stalkSpecializes (specializes_of_eq h₂)) ≫ i₂.stalkMap _ ≫ CommRingCat.ofHom α₂ =
      CommRingCat.ofHom (Ideal.Quotient.mk K) := by
    ext a
    change α₂ (σ₂ a) = Ideal.Quotient.mk K a
    rw [← RingHom.comp_apply, hα₂]
  have ha₁ : a₁ ≫ i₁ = p := by
    simp only [a₁, p, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (specializes_of_eq h₁)]
    simp only [← Category.assoc, ← Spec.map_comp]
    rw [← hring₁]
    rfl
  have ha₂ : a₂ ≫ i₂ = p := by
    simp only [a₂, p, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (specializes_of_eq h₂)]
    simp only [← Category.assoc, ← Spec.map_comp]
    rw [← hring₂]
    rfl
  let g : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸ K)) ⟶ pullback i₁ i₂ :=
    pullback.lift a₁ a₂ (ha₁.trans ha₂.symm)
  have hg : g ≫ (pullback.fst i₁ i₂ ≫ i₁) = p := by
    rw [← Category.assoc, pullback.lift_fst, ha₁]
  have hpt : (g ≫ (pullback.fst i₁ i₂ ≫ i₁)).base (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x := by
    rw [hg]
    change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.fromSpecStalk x)
      (closedPoint ((X.presheaf.stalk x) ⧸ K)) = x
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

  have hw₁ : (pullback.fst i₁ i₂).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) =
      (pullback.fst i₁ i₂).base z := by
    change (g ≫ pullback.fst i₁ i₂) (closedPoint ((X.presheaf.stalk x) ⧸ K)) = _
    rw [pullback.lift_fst]
    change (Spec.map (CommRingCat.ofHom α₁) ≫ C₁.fromSpecStalk _) (closedPoint _) = _
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hw₂ : (pullback.snd i₁ i₂).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) =
      (pullback.snd i₁ i₂).base z := by
    change (g ≫ pullback.snd i₁ i₂) (closedPoint ((X.presheaf.stalk x) ⧸ K)) = _
    rw [pullback.lift_snd]
    change (Spec.map (CommRingCat.ofHom α₂) ≫ C₂.fromSpecStalk _) (closedPoint _) = _
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  refine isRadical_of_specLift (pullback.fst i₁ i₂ ≫ i₁) x K g hg hpt (sup_le ?_ ?_)
  ·
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    rw [RingHom.mem_ker]
    change ((pullback.fst i₁ i₂ ≫ i₁).stalkMap _).hom
      ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a) = 0
    have e : (X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a =
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₁)) ≫ X.presheaf.stalkSpecializes
          (i₁.base.hom.map_specializes (specializes_of_eq hw₁))).hom a := by
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    rw [Scheme.Hom.stalkMap_comp]
    change ((pullback.fst i₁ i₂).stalkMap _).hom ((i₁.stalkMap _).hom
      ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a)) = 0
    rw [e]
    change ((pullback.fst i₁ i₂).stalkMap _).hom ((i₁.stalkMap _).hom
      ((X.presheaf.stalkSpecializes (i₁.base.hom.map_specializes (specializes_of_eq hw₁))).hom
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₁)).hom a))) = 0
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply i₁ _ _ (specializes_of_eq hw₁), ha, map_zero,
      map_zero]
  ·
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    rw [RingHom.mem_ker]
    change ((pullback.fst i₁ i₂ ≫ i₁).stalkMap _).hom
      ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)).hom a) = 0
    have hcond : (pullback.fst i₁ i₂ ≫ i₁).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) =
        (pullback.snd i₁ i₂ ≫ i₂).base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))) :=
      congrArg (fun k => k.base (g.base (closedPoint ((X.presheaf.stalk x) ⧸ K))))
        (pullback.condition (f := i₁) (g := i₂))
    rw [Scheme.Hom.stalkMap_congr_hom _ _ pullback.condition, Scheme.Hom.stalkMap_comp]
    change ((pullback.snd i₁ i₂).stalkMap _).hom ((i₂.stalkMap _).hom
      (((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
        (X.presheaf.stalkCongr (Inseparable.of_eq hcond)).hom).hom a)) = 0
    have e : ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
          (X.presheaf.stalkCongr (Inseparable.of_eq hcond)).hom).hom a =
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₂)) ≫
          X.presheaf.stalkSpecializes (i₂.base.hom.map_specializes (specializes_of_eq hw₂))).hom a := by
      change ((X.presheaf.stalkSpecializes (specializes_of_eq hpt)) ≫
          X.presheaf.stalkSpecializes (Inseparable.of_eq hcond).ge).hom a = _
      rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    rw [e]
    change ((pullback.snd i₁ i₂).stalkMap _).hom ((i₂.stalkMap _).hom
      ((X.presheaf.stalkSpecializes (i₂.base.hom.map_specializes (specializes_of_eq hw₂))).hom
        ((X.presheaf.stalkSpecializes (specializes_of_eq h₂)).hom a))) = 0
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply i₂ _ _ (specializes_of_eq hw₂), ha, map_zero,
      map_zero]

private theorem branchIdeal_sup_eq_transport {x x' ζ₁ ζ₁' ζ₂ ζ₂' : X}
    (ex : x = x') (e₁ : ζ₁ = ζ₁') (e₂ : ζ₂ = ζ₂')
    (g₁ : ζ₁ ⤳ x) (g₂ : ζ₂ ⤳ x) (g₁' : ζ₁' ⤳ x') (g₂' : ζ₂' ⤳ x')
    (H : Scheme.branchIdeal g₁ ⊔ Scheme.branchIdeal g₂ = maximalIdeal (X.presheaf.stalk x)) :
    Scheme.branchIdeal g₁' ⊔ Scheme.branchIdeal g₂' = maximalIdeal (X.presheaf.stalk x') := by
  subst ex e₁ e₂
  exact H

private theorem descent {A Abar B : Type*} [CommRing A] [CommRing Abar] [CommRing B]
    [IsLocalRing A] [IsLocalRing Abar] [IsLocalRing B] [IsReduced B]
    (θ : A →+* Abar) (hθ : Function.Surjective θ) (ψ : Abar →+* B) (hψ : ψ.Flat) [IsLocalHom ψ]
    {P Q : Ideal A} {P' Q' : Ideal B} [P'.IsPrime] [Q'.IsPrime]
    (hP : P'.comap (ψ.comp θ) = P) (hQ : Q'.comap (ψ.comp θ) = Q) (hPQ : P ≠ Q)
    (htri : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 = maximalIdeal B ∨ 𝔮 = P' ∨ 𝔮 = Q')
    (hPm : P' ≠ maximalIdeal B) (hQm : Q' ≠ maximalIdeal B) (hPQ' : ¬ P' ≤ Q') (hQP' : ¬ Q' ≤ P')
    (hκ : P' ⊔ Q' = maximalIdeal B) :
    P ⊔ Q = maximalIdeal A := by
  haveI : IsLocalHom θ := IsLocalHom.of_surjective θ hθ

  have hminP : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ P' → 𝔮 = P' := by
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact absurd ((maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
        hPm
    · rfl
    · exact absurd hle hQP'
  have hminQ : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → 𝔮 ≤ Q' → 𝔮 = Q' := by
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact absurd ((maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
        hQm
    · exact absurd hle hPQ'
    · rfl

  have hkerP : RingHom.ker θ ≤ P := by
    intro a ha
    rw [← hP, Ideal.mem_comap, RingHom.comp_apply, RingHom.mem_ker.mp ha, map_zero]
    exact zero_mem _
  have hkerQ : RingHom.ker θ ≤ Q := by
    intro a ha
    rw [← hQ, Ideal.mem_comap, RingHom.comp_apply, RingHom.mem_ker.mp ha, map_zero]
    exact zero_mem _
  have hcmP : (P.map θ).comap θ = P := by
    rw [Ideal.comap_map_of_surjective _ hθ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerP]
  have hcmQ : (Q.map θ).comap θ = Q := by
    rw [Ideal.comap_map_of_surjective _ hθ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerQ]

  have hPbar : P'.comap ψ = P.map θ := by
    rw [← hP, ← Ideal.comap_comap, Ideal.map_comap_of_surjective θ hθ]
  have hQbar : Q'.comap ψ = Q.map θ := by
    rw [← hQ, ← Ideal.comap_comap, Ideal.map_comap_of_surjective θ hθ]
  haveI hPbp : (P.map θ).IsPrime := hPbar ▸ Ideal.comap_isPrime ψ P'
  haveI hQbp : (Q.map θ).IsPrime := hQbar ▸ Ideal.comap_isPrime ψ Q'
  have hPQbar : P.map θ ≠ Q.map θ := fun h => hPQ (by rw [← hcmP, h, hcmQ])

  have hmapP : (P.map θ).map ψ = P' := by
    refine map_eq_of_flat_of_forall_le_ringHom ψ hψ _ (Ideal.map_le_iff_le_comap.mpr hPbar.ge) ?_
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
    · exact le_rfl
    · exfalso
      rw [hQbar] at hle
      rw [← hPbar] at hle hPQbar
      exact not_le_comap_of_ne_of_flat_ringHom ψ hψ P' hminP hPQbar.symm hle
  have hmapQ : (Q.map θ).map ψ = Q' := by
    refine map_eq_of_flat_of_forall_le_ringHom ψ hψ _ (Ideal.map_le_iff_le_comap.mpr hQbar.ge) ?_
    intro 𝔮 h𝔮 hle
    rcases htri 𝔮 h𝔮 with rfl | rfl | rfl
    · exact le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
    · exfalso
      rw [hPbar] at hle
      rw [← hQbar] at hle hPQbar
      exact not_le_comap_of_ne_of_flat_ringHom ψ hψ Q' hminQ hPQbar hle
    · exact le_rfl

  have hbar : P.map θ ⊔ Q.map θ = maximalIdeal Abar := by
    refine sup_eq_maximalIdeal_of_map_maximalIdeal_le ψ hψ (Ideal.IsPrime.ne_top hPbp)
      (Ideal.IsPrime.ne_top hQbp) ?_
    rw [Ideal.map_sup, hmapP, hmapQ, hκ]
    exact Ideal.map_le_iff_le_comap.mpr (maximalIdeal_comap ψ).ge
  calc P ⊔ Q = ((P ⊔ Q).map θ).comap θ := by
        rw [Ideal.comap_map_of_surjective _ hθ, ← RingHom.ker_eq_comap_bot, eq_comm, sup_eq_left]
        exact hkerP.trans le_sup_left
    _ = maximalIdeal A := by rw [Ideal.map_sup, hbar, maximalIdeal_comap]

end TransvChair

end Unit6

section Main

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve IsLocalRing ECL_TransvPlumb ECL_Transv

set_option maxHeartbeats 3200000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (hinf : 𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)
    (hzero : 𝔛.ξzero A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) :
    Scheme.branchIdeal hinf ⊔ Scheme.branchIdeal hzero = IsLocalRing.maximalIdeal ((XO (ΓM M H) hj ρO).presheaf.stalk (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)) := by
  classical
  haveI := (𝔛.Mfib A hA ρ hρ).isIntegral
  haveI := ECL_FibN.isIntegral_fibreN 𝔛 A hA ρ hρ
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  haveI := 𝔛.crossing_reduced A hA ρ hρ
  haveI : IsReduced (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) := 𝔛.fibre_reduced A hA ρ hρ

  have h₁ := comp0_genericPoint_specializes 𝔛 A hA ρ hρ n
  have h₂ := comp1_genericPoint_specializes 𝔛 A hA ρ hρ n
  have hy₂ := comp1_snd_eq_comp0_fst 𝔛 A hA ρ hρ n
  obtain ⟨hy₁', hy₂'⟩ := comp0_genericPoint_ne_and_comp1_genericPoint_ne (hpM2 := hpM2) (hHp := hHp) 𝔛 A hA ρ hρ O ρO toκ htoκ n

  have htri := frame_eq_maximalIdeal_or_eq_branchIdeal_or_eq_branchIdeal 𝔛 A hA ρ hρ n
  obtain ⟨hPm, hQm, hPQ', hQP'⟩ := frame_branchIdeal_ne_maximalIdeal_and_not_le (hpM2 := hpM2) (hHp := hHp) 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ n hy₁' hy₂'

  have hJ₁le : RingHom.ker ((𝔛.comp A hA ρ hρ 0).stalkMap
      ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)).hom ≤ Scheme.branchIdeal h₁ :=
    TransvChair.ker_stalkMap_le_comap_stalkSpecializes (𝔛.comp A hA ρ hρ 0) (genericPoint_specializes _)
  have hJ₂le : (RingHom.ker ((𝔛.comp A hA ρ hρ 1).stalkMap
      ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)).hom).comap
      ((fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).presheaf.stalkSpecializes (specializes_of_eq hy₂)).hom ≤
      Scheme.branchIdeal h₂ := by
    refine (Ideal.comap_mono (TransvChair.ker_stalkMap_le_comap_stalkSpecializes (𝔛.comp A hA ρ hρ 1)
      (genericPoint_specializes ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)))).trans
      (le_of_eq ?_)
    rw [Ideal.comap_comap, ← CommRingCat.hom_comp, TopCat.Presheaf.stalkSpecializes_comp]
    rfl

  haveI hJ₁p : (RingHom.ker ((𝔛.comp A hA ρ hρ 0).stalkMap
      ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)).hom).IsPrime := RingHom.ker_isPrime _
  haveI hJ₂p : (RingHom.ker ((𝔛.comp A hA ρ hρ 1).stalkMap
      ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)).hom).IsPrime := RingHom.ker_isPrime _
  haveI hJ₂p' : ((RingHom.ker ((𝔛.comp A hA ρ hρ 1).stalkMap
      ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)).hom).comap
      ((fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).presheaf.stalkSpecializes (specializes_of_eq hy₂)).hom).IsPrime :=
    Ideal.comap_isPrime _ _
  have hJ₁ : RingHom.ker ((𝔛.comp A hA ρ hρ 0).stalkMap
      ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)).hom = Scheme.branchIdeal h₁ :=
    eq_branchIdeal_of_isPrime_of_le h₁ h₂ (fun 𝔮 h𝔮 => htri 𝔮) hPm hQP' _ hJ₁le
  have hJ₂ : (RingHom.ker ((𝔛.comp A hA ρ hρ 1).stalkMap
      ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)).hom).comap
      ((fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).presheaf.stalkSpecializes (specializes_of_eq hy₂)).hom =
      Scheme.branchIdeal h₂ :=
    eq_branchIdeal_of_isPrime_of_le h₂ h₁ (fun 𝔮 h𝔮 => (htri 𝔮).imp id Or.symm) hQm hPQ' _ hJ₂le

  have hrad : (Scheme.branchIdeal h₁ ⊔ Scheme.branchIdeal h₂).IsRadical := by
    have h := TransvChair.isRadical_comap_ker_sup_comap_ker (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) n _ rfl hy₂
    have e : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).presheaf.stalkSpecializes (specializes_of_eq
        (rfl : (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) =
          (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n))) = 𝟙 _ :=
      (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).presheaf.stalkSpecializes_refl _
    rw [e, CommRingCat.hom_id, Ideal.comap_id, hJ₁, hJ₂] at h
    exact h
  have hκ : Scheme.branchIdeal h₁ ⊔ Scheme.branchIdeal h₂ = IsLocalRing.maximalIdeal _ :=
    eq_of_isRadical_of_le_of_forall_le hrad
      (sup_le (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
        (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)))
      (fun 𝔮 h𝔮 hle => by
        rcases htri 𝔮 with rfl | rfl | rfl
        · exact le_rfl
        · exact absurd (le_sup_right.trans hle) hQP'
        · exact absurd (le_sup_left.trans hle) hPQ')

  have E : (bcMap (ΓM M H) hj ρO toκ htoκ).base
        ((𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)) =
      (bcMap (ΓM M H) hj ρO (IsLocalRing.residue O) rfl).base
        ((fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) _ (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ)).base
          ((𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n))) := by
    rw [← Scheme.Hom.comp_apply (fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) _ (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ))
        (bcMap (ΓM M H) hj ρO (IsLocalRing.residue O) rfl),
      ECL_TransvPlumb.g_comp_j ρO hϖ toκ htoκ]
  have hι := (ConcreteCategory.bijective_of_isIso
    ((XO (ΓM M H) hj ρO).presheaf.stalkCongr (.of_eq E)).hom).2
  have hπ := ECL_TransvPlumb.stalkMap_j_surjective ρO
    ((fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) _ (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ)).base
      ((𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)))
  have hθ : Function.Surjective
      (((XO (ΓM M H) hj ρO).presheaf.stalkCongr (.of_eq E)).hom ≫
        (bcMap (ΓM M H) hj ρO (IsLocalRing.residue O) rfl).stalkMap
          ((fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) _ (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ)).base
            ((𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)))).hom := by
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    exact hπ.comp hι
  have hψ := ECL_TransvPlumb.flat_stalkMap_g ρO hϖ toκ htoκ
    ((𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n))
  have hfac : ((bcMap (ΓM M H) hj ρO toκ htoκ).stalkMap
        ((𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n))).hom =
      ((fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) _ (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ)).stalkMap
          ((𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n))).hom.comp
        (((XO (ΓM M H) hj ρO).presheaf.stalkCongr (.of_eq E)).hom ≫
          (bcMap (ΓM M H) hj ρO (IsLocalRing.residue O) rfl).stalkMap
            ((fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) _ (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ)).base
              ((𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)))).hom := by
    rw [ECL_TransvPlumb.stalkMap_bcMap_eq ρO hϖ toκ htoκ, CommRingCat.hom_comp,
      CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_assoc]

  have hP := TransvChair.comap_stalkMap_comap_stalkSpecializes (bcMap (ΓM M H) hj ρO toκ htoκ) h₁
  have hQ := TransvChair.comap_stalkMap_comap_stalkSpecializes (bcMap (ΓM M H) hj ρO toκ htoκ) h₂
  rw [hfac] at hP hQ
  change (Scheme.branchIdeal h₁).comap _ =
    Scheme.branchIdeal ((bcMap (ΓM M H) hj ρO toκ htoκ).base.hom.map_specializes h₁) at hP
  change (Scheme.branchIdeal h₂).comap _ =
    Scheme.branchIdeal ((bcMap (ΓM M H) hj ρO toκ htoκ).base.hom.map_specializes h₂) at hQ

  have hPQ : Scheme.branchIdeal ((bcMap (ΓM M H) hj ρO toκ htoκ).base.hom.map_specializes h₁) ≠
      Scheme.branchIdeal ((bcMap (ΓM M H) hj ρO toκ htoκ).base.hom.map_specializes h₂) :=
    fun h => ModularCurve.XHDRModelAtP.xiInf_ne_xiZero p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ
      (by
        show (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base _ = (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base _
        simp only [Scheme.Hom.comp_apply]
        rw [ECL_FibN.efib_genericPoint_eq 𝔛 A hA ρ hρ]
        exact eq_of_branchIdeal_eq _ _ h)

  have Hdesc := TransvChair.descent _ hθ _ hψ hP hQ hPQ (fun 𝔮 h𝔮 => htri 𝔮) hPm hQm hPQ' hQP' hκ

  have ey : (bcMap (ΓM M H) hj ρO toκ htoκ).base
      ((𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)) =
      𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n := by
    show _ = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫
      bcMap (ΓM M H) hj ρO toκ htoκ).base n
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  have eξ₁ : (bcMap (ΓM M H) hj ρO toκ htoκ).base
      ((𝔛.comp A hA ρ hρ 0).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))) = 𝔛.ξinf A hA ρ hρ ρO toκ htoκ := by
    rw [← ECL_FibN.efib_genericPoint_eq 𝔛 A hA ρ hρ]; rfl
  have eξ₂ : (bcMap (ΓM M H) hj ρO toκ htoκ).base
      ((𝔛.comp A hA ρ hρ 1).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))) = 𝔛.ξzero A hA ρ hρ ρO toκ htoκ := by
    rw [← ECL_FibN.efib_genericPoint_eq 𝔛 A hA ρ hρ]; rfl
  exact TransvChair.branchIdeal_sup_eq_transport ey eξ₁ eξ₂ _ _ hinf hzero Hdesc

end Main

end S_ModularCurve_XHDRModelAtP_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal (solution)
