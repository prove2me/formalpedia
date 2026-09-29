-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_isInvertible_frames
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e2cddbb7-c01c-5a8f-b358-699917898eb8

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Theorems.Thm_ModularCurve_XHDRModelAtP_readA_mem_integers_and_residue_eq_restrict_comp_of_mem
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_finite_setOf_fixed_of_eq_gammaLift
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_of_finite_subset_affineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_isInvertible_frames
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun"
p2m_attr_erase "simp" "KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in

example : True := trivial

namespace FrameReadH

section PlaceLemmas

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_toValuationSubring_of_ord_eq_zero (v : Place K F) {f : F} (hf : f ≠ 0) (h0 : v.ord f = 0) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h0, zpow_zero, mul_one] at hu
  rw [hu]
  exact (u : v.toValuationSubring).2

theorem evalAt_mul_of_mem (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  have hfg : f * g ∈ v.toValuationSubring := mul_mem hf hg
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv hfg, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

end PlaceLemmas

section Main

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

theorem exists_forall_ord_eq_zero_and_isUnit_evalAt_of_isFrameOn_of_isFrameOn
    (A : ValuationSubring L)
    {X : Scheme} [IsIntegral X] (𝓛 : X.Modules)
    (φ : ∀ U : X.Opens, Γ(𝓛, U) →+ (X.functionField : Type))
    (hφres : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : Γ(𝓛, U), φ V (𝓛.presheaf.map (homOfLE h).op m) = φ U m)
    (hφlin : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(𝓛, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (eK : X.functionField ≃+* F)

    (D : Set (Place L F)) (hD : ∀ P ∈ D, P.IsRational) (z : F) (n : ℤ)
    (x₀ : X)

    (U : X.Opens) (hxU : x₀ ∈ U) (m : Γ(𝓛, U)) (g : F) (hg : g = eK (φ U m)) (hmU : Scheme.Modules.IsFrameOn m U)
    (hg0 : g ≠ 0) (a : L) (ha : a ≠ 0)
    (hlaw : ∀ P ∈ D, P.ord g = 0 ∧ ∃ h : P.evalAt g * a * (P.evalAt z) ^ n ∈ A, IsUnit (⟨_, h⟩ : ↥A))

    (V : X.Opens) (hxV : x₀ ∈ V) (σ : Γ(𝓛, V)) (hσV : Scheme.Modules.IsFrameOn σ V) (f : F) (hf : f = eK (φ V σ))

    (htr : ∀ (W : X.Opens) [Nonempty W], x₀ ∈ W → ∀ u : Γ(X, W), IsUnit u →
      ∀ P ∈ D, P.ord (eK (algebraMap Γ(X, W) X.functionField u)) = 0 ∧
        ∃ h : P.evalAt (eK (algebraMap Γ(X, W) X.functionField u)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) :
    ∃ a' : L, a' ≠ 0 ∧ ∀ P ∈ D, P.ord f = 0 ∧ ∃ h : P.evalAt f * a' * (P.evalAt z) ^ n ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by

  haveI hW : Nonempty (Scheme.Opens.toScheme (U ⊓ V)) := ⟨⟨x₀, show x₀ ∈ U ⊓ V from ⟨hxU, hxV⟩⟩⟩

  obtain ⟨u, hu⟩ := (hmU (inf_le_left : U ⊓ V ≤ U) inf_le_left).2 (𝓛.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ)
  obtain ⟨u', hu'⟩ := (hσV (inf_le_right : U ⊓ V ≤ V) inf_le_right).2 (𝓛.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op m)
  have hunit : IsUnit u := by
    refine isUnit_iff_exists_inv.mpr ⟨u', (hσV (inf_le_right : U ⊓ V ≤ V) inf_le_right).1 ?_⟩
    show (u * u') • 𝓛.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ =
      (1 : Γ(X, U ⊓ V)) • 𝓛.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ
    rw [mul_smul, one_smul]
    simp only [] at hu hu'
    rw [hu', hu]

  have hfrg : f = eK (algebraMap Γ(X, U ⊓ V) X.functionField u) * g := by
    rw [hf, hg, ← map_mul, ← hφres V (U ⊓ V) inf_le_right hW σ, ← hφres U (U ⊓ V) inf_le_left hW m]
    simp only [] at hu
    rw [← hu, hφlin]
  refine ⟨a, ha, fun P hP => ?_⟩
  obtain ⟨hr0, hrA, hru⟩ := htr (U ⊓ V) ⟨hxU, hxV⟩ u hunit P hP
  obtain ⟨hg0', hgA, hgu⟩ := hlaw P hP
  have hrne : eK (algebraMap Γ(X, U ⊓ V) X.functionField u) ≠ 0 :=
    ((hunit.map (algebraMap Γ(X, U ⊓ V) X.functionField)).map eK).ne_zero
  refine ⟨?_, ?_⟩
  · rw [hfrg, P.ord_mul hrne hg0, hr0, hg0', add_zero]
  · have hev : P.evalAt f = P.evalAt (eK (algebraMap Γ(X, U ⊓ V) X.functionField u)) * P.evalAt g := by
      rw [hfrg]
      exact evalAt_mul_of_mem P (hD P hP) (mem_toValuationSubring_of_ord_eq_zero P hrne hr0)
        (mem_toValuationSubring_of_ord_eq_zero P hg0 hg0')
    have heq : P.evalAt f * a * (P.evalAt z) ^ n =
        P.evalAt (eK (algebraMap Γ(X, U ⊓ V) X.functionField u)) * (P.evalAt g * a * (P.evalAt z) ^ n) := by
      rw [hev]; ring
    refine ⟨heq ▸ mul_mem hrA hgA, ?_⟩
    have : (⟨_, heq ▸ mul_mem hrA hgA⟩ : ↥A) = ⟨_, hrA⟩ * ⟨_, hgA⟩ := Subtype.ext heq
    rw [this]
    exact hru.mul hgu

end Main

end FrameReadH

namespace FrameReadH

section TwoFrames

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

theorem exists_isUnit_reading_mul_of_isFrameOn
    {X : Scheme} [IsIntegral X] (𝓛 : X.Modules)
    (φ : ∀ U : X.Opens, Γ(𝓛, U) →+ (X.functionField : Type))
    (hφres : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : Γ(𝓛, U), φ V (𝓛.presheaf.map (homOfLE h).op m) = φ U m)
    (hφlin : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(𝓛, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (eK : X.functionField ≃+* F) (x₀ : X)
    (U : X.Opens) (hxU : x₀ ∈ U) (m : Γ(𝓛, U)) (g : F) (hg : g = eK (φ U m)) (hmU : Scheme.Modules.IsFrameOn m U)
    (V : X.Opens) (hxV : x₀ ∈ V) (σ : Γ(𝓛, V)) (hσV : Scheme.Modules.IsFrameOn σ V) (f : F) (hf : f = eK (φ V σ)) :
    ∃ (_ : Nonempty (Scheme.Opens.toScheme (U ⊓ V))) (u : Γ(X, U ⊓ V)), IsUnit u ∧
      f = eK (algebraMap Γ(X, U ⊓ V) X.functionField u) * g := by
  haveI hW : Nonempty (Scheme.Opens.toScheme (U ⊓ V)) := ⟨⟨x₀, show x₀ ∈ U ⊓ V from ⟨hxU, hxV⟩⟩⟩
  obtain ⟨u, hu⟩ := (hmU (inf_le_left : U ⊓ V ≤ U) inf_le_left).2 (𝓛.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ)
  obtain ⟨u', hu'⟩ := (hσV (inf_le_right : U ⊓ V ≤ V) inf_le_right).2 (𝓛.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op m)
  have hunit : IsUnit u := by
    refine isUnit_iff_exists_inv.mpr ⟨u', (hσV (inf_le_right : U ⊓ V ≤ V) inf_le_right).1 ?_⟩
    show (u * u') • 𝓛.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ =
      (1 : Γ(X, U ⊓ V)) • 𝓛.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ
    rw [mul_smul, one_smul]
    simp only [] at hu hu'
    rw [hu', hu]
  refine ⟨hW, u, hunit, ?_⟩
  rw [hf, hg, ← map_mul, ← hφres V (U ⊓ V) inf_le_right hW σ, ← hφres U (U ⊓ V) inf_le_left hW m]
  simp only [] at hu
  rw [← hu, hφlin]

end TwoFrames

end FrameReadH

namespace FrameReadH

section Transfer

variable {K : Type} [Field K] [IsAlgClosed K] {L : Type} [Field L] [Algebra K L]

omit [IsAlgClosed K] in

theorem subtype_stalkClosedPointIso_germ_eq_stalkClosedPointTo (A : ValuationSubring K)
    (V' : (Spec (CommRingCat.of ↥A)).Opens) (hV' : V' = ⊤) (t : Γ(Spec (CommRingCat.of ↥A), V'))
    (h1 : IsLocalRing.closedPoint ↥A ∈ V')
    (h2 : (Spec.map (CommRingCat.ofHom A.subtype)).base (IsLocalRing.closedPoint K) ∈ V') :
    A.subtype ((stalkClosedPointIso (CommRingCat.of ↥A)).hom.hom (((Spec (CommRingCat.of ↥A)).presheaf.germ V' _ h1).hom t)) =
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom A.subtype))).hom
        (((Spec (CommRingCat.of ↥A)).presheaf.germ V' _ h2).hom t) := by
  subst hV'
  have e1 := congrArg (fun φ => CommRingCat.Hom.hom φ t) (germ_stalkClosedPointIso_hom (CommRingCat.of ↥A))
  have e2 := congrArg (fun φ => CommRingCat.Hom.hom φ t)
    (Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom A.subtype : CommRingCat.of ↥A ⟶ CommRingCat.of K))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at e1 e2
  rw [e2, ← e1]

theorem ord_eq_zero_and_isUnit_evalAt_of_specializes (Mc : CurveModel K L) (A : ValuationSubring K)
    {X : Scheme} [IsIntegral X] (gA : Mc.C ⟶ X) (eK : X.functionField ≃+* L)
    (heK : ∀ (U : X.Opens) [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme U)] (a : Γ(X, U)),
      eK (X.germToFunctionField U a) = Mc.ffEquiv.symm (Mc.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a)))
    (x₀ : X) (W : X.Opens) [Nonempty (Scheme.Opens.toScheme W)] [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ W))] (hx₀ : x₀ ∈ W)
    (u : Γ(X, W)) (hu : IsUnit u)
    (pt : {q : Spec (CommRingCat.of K) ⟶ Mc.C // q ≫ Mc.toBase = 𝟙 _})
    (uA : Spec (CommRingCat.of ↥A) ⟶ X)
    (hgen : Spec.map (CommRingCat.ofHom A.subtype) ≫ uA = pt.1 ≫ gA)
    (hsp : uA.base (IsLocalRing.closedPoint ↥A) = x₀) :
    (Mc.pointEquivPlace pt).ord (eK (algebraMap Γ(X, W) X.functionField u)) = 0 ∧
    ∃ h : (Mc.pointEquivPlace pt).evalAt (eK (algebraMap Γ(X, W) X.functionField u)) ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by

  have htop : uA ⁻¹ᵁ W = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem uA (by rw [hsp]; exact hx₀)
  have hall : ∀ z, uA.base z ∈ W := fun z => by
    show z ∈ uA ⁻¹ᵁ W
    rw [htop]; trivial

  have hyW : gA.base (pt.1.base (IsLocalRing.closedPoint K)) ∈ W := by
    rw [← Scheme.Hom.comp_apply, ← hgen, Scheme.Hom.comp_apply]
    exact hall _

  have hr : eK (algebraMap Γ(X, W) X.functionField u) = Mc.ffEquiv.symm (Mc.C.germToFunctionField (gA ⁻¹ᵁ W) ((gA.app W).hom u)) :=
    heK W u
  refine ⟨?_, ?_⟩
  ·
    rw [hr, CurveModel.pointEquivPlace_apply]
    exact CurveModel.ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit Mc (gA ⁻¹ᵁ W)
      (pointEquivClosedPoint Mc.toBase pt) hyW _ (hu.map _)
  ·
    obtain ⟨hmem, -, hev⟩ := CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo Mc pt
      ((Mc.C.presheaf.germ (gA ⁻¹ᵁ W) (pt.1.base (IsLocalRing.closedPoint K)) hyW).hom ((gA.app W).hom u))
    have hsc : algebraMap (Mc.C.presheaf.stalk (pt.1.base (IsLocalRing.closedPoint K))) Mc.C.functionField
        ((Mc.C.presheaf.germ (gA ⁻¹ᵁ W) (pt.1.base (IsLocalRing.closedPoint K)) hyW).hom ((gA.app W).hom u)) =
        (Mc.C.germToFunctionField (gA ⁻¹ᵁ W)).hom ((gA.app W).hom u) := by
      show (Mc.C.presheaf.stalkSpecializes _).hom _ = _
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [hsc] at hev
    rw [hr]
    erw [hev]

    have e3 : (Scheme.stalkClosedPointTo pt.1).hom ((Mc.C.presheaf.germ (gA ⁻¹ᵁ W) (pt.1.base (IsLocalRing.closedPoint K)) hyW).hom ((gA.app W).hom u)) =
        (Scheme.stalkClosedPointTo (pt.1 ≫ gA)).hom ((X.presheaf.germ W ((pt.1 ≫ gA).base (IsLocalRing.closedPoint K)) hyW).hom u) := by
      rw [Scheme.stalkClosedPointTo_comp]
      show _ = (Scheme.stalkClosedPointTo pt.1).hom ((gA.stalkMap _).hom ((X.presheaf.germ W _ hyW).hom u))
      erw [Scheme.Hom.germ_stalkMap_apply gA W (pt.1.base (IsLocalRing.closedPoint K)) hyW u]

    have key : ∀ (q₁ q₂ : Spec (CommRingCat.of K) ⟶ X) (_ : q₁ = q₂) (h₁ : q₁.base (IsLocalRing.closedPoint K) ∈ W)
        (h₂ : q₂.base (IsLocalRing.closedPoint K) ∈ W),
        (Scheme.stalkClosedPointTo q₁).hom ((X.presheaf.germ W (q₁.base (IsLocalRing.closedPoint K)) h₁).hom u) =
        (Scheme.stalkClosedPointTo q₂).hom ((X.presheaf.germ W (q₂.base (IsLocalRing.closedPoint K)) h₂).hom u) := by
      rintro _ _ rfl _ _; rfl
    have e4 := key (pt.1 ≫ gA) (Spec.map (CommRingCat.ofHom A.subtype) ≫ uA) hgen.symm hyW (hall _)

    have e5 : (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom A.subtype) ≫ uA)).hom
          ((X.presheaf.germ W ((Spec.map (CommRingCat.ofHom A.subtype) ≫ uA).base (IsLocalRing.closedPoint K)) (hall _)).hom u) =
        (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom A.subtype))).hom
          (((Spec (CommRingCat.of ↥A)).presheaf.germ (uA ⁻¹ᵁ W) _ (hall _)).hom ((uA.app W).hom u)) := by
      rw [Scheme.stalkClosedPointTo_comp]
      show (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom A.subtype))).hom ((uA.stalkMap _).hom ((X.presheaf.germ W _ (hall _)).hom u)) = _
      erw [Scheme.Hom.germ_stalkMap_apply uA W ((Spec.map (CommRingCat.ofHom A.subtype)).base (IsLocalRing.closedPoint K)) (hall _) u]
    have e6 := (subtype_stalkClosedPointIso_germ_eq_stalkClosedPointTo A (uA ⁻¹ᵁ W) htop ((uA.app W).hom u)
      (hall _) (hall _)).symm

    have hunitA : IsUnit ((stalkClosedPointIso (CommRingCat.of ↥A)).hom.hom
        (((Spec (CommRingCat.of ↥A)).presheaf.germ (uA ⁻¹ᵁ W) _ (hall (IsLocalRing.closedPoint ↥A))).hom ((uA.app W).hom u))) :=
      ((hu.map _).map _).map _
    rw [e3, e4, e5, e6]
    have fin : ∀ (a : ↥A), IsUnit a → ∃ h : A.subtype a ∈ A, IsUnit (⟨A.subtype a, h⟩ : ↥A) :=
      fun a ha => by obtain ⟨v, hv⟩ := a; exact ⟨hv, ha⟩
    exact fin _ hunitA

end Transfer

end FrameReadH

namespace FrameReadH

section Tube

variable {K : Type} [Field K] [IsAlgClosed K] {L : Type} [Field L] [Algebra K L]

theorem forall_ord_eq_zero_and_isUnit_evalAt_of_tube (Mc : CurveModel K L) (A : ValuationSubring K)
    {X : Scheme} [IsIntegral X] (gA : Mc.C ⟶ X) (eK : X.functionField ≃+* L)
    (heK : ∀ (U : X.Opens) [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme U)] (a : Γ(X, U)),
      eK (X.germToFunctionField U a) = Mc.ffEquiv.symm (Mc.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a)))
    (x₀ : X) (D : Set (Place K L))
    (htube : ∀ P ∈ D, ∃ (pt : {q : Spec (CommRingCat.of K) ⟶ Mc.C // q ≫ Mc.toBase = 𝟙 _}) (uA : Spec (CommRingCat.of ↥A) ⟶ X),
      Mc.pointEquivPlace pt = P ∧ Spec.map (CommRingCat.ofHom A.subtype) ≫ uA = pt.1 ≫ gA ∧ uA.base (IsLocalRing.closedPoint ↥A) = x₀) :
    ∀ (W : X.Opens) [Nonempty W], x₀ ∈ W → ∀ u : Γ(X, W), IsUnit u →
      ∀ P ∈ D, P.ord (eK (algebraMap Γ(X, W) X.functionField u)) = 0 ∧
        ∃ h : P.evalAt (eK (algebraMap Γ(X, W) X.functionField u)) ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by
  intro W _ hxW u hu P hP
  obtain ⟨pt, uA, rfl, hgen, hsp⟩ := htube P hP
  have htop : uA ⁻¹ᵁ W = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem uA (by rw [hsp]; exact hxW)
  have hyW : gA.base (pt.1.base (IsLocalRing.closedPoint K)) ∈ W := by
    rw [← Scheme.Hom.comp_apply, ← hgen, Scheme.Hom.comp_apply]
    show _ ∈ uA ⁻¹ᵁ W
    rw [htop]; trivial
  haveI : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ W)) := ⟨⟨pt.1.base (IsLocalRing.closedPoint K), hyW⟩⟩
  exact ord_eq_zero_and_isUnit_evalAt_of_specializes Mc A gA eK heK x₀ W hxW u hu pt uA hgen hsp

end Tube

end FrameReadH

namespace FrameReadH

section SectionLift

universe u

theorem exists_lift {X : Scheme.{u}} {B : CommRingCat.{u}} (f : X ⟶ Spec B) [UniversallyClosed f]
    {K : Type u} [Field K] (O : ValuationSubring K)
    (i₁ : Spec (CommRingCat.of K) ⟶ X) (i₂ : Spec (CommRingCat.of ↥O) ⟶ Spec B)
    (hsq : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ↥O K)) ≫ i₂) :
    ∃ ℓ : Spec (CommRingCat.of ↥O) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap ↥O K)) ≫ ℓ = i₁ ∧ ℓ ≫ f = i₂ := by
  let S : ValuativeCommSq f := { R := ↥O, K := K, i₁ := i₁, i₂ := i₂, commSq := ⟨hsq⟩ }
  have hE : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  haveI : S.commSq.HasLift := hE S
  exact ⟨S.commSq.lift, S.commSq.fac_left, S.commSq.fac_right⟩

theorem exists_section_valuationSubring {X : Scheme.{u}} {R : Type u} [CommRing R] (tb : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed tb]
    {K : Type u} [Field K] [Algebra R K] (A : ValuationSubring K) (ρ : R →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap R K)
    (i₁ : Spec (CommRingCat.of K) ⟶ X) (hi₁ : i₁ ≫ tb = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ (ℓ : Spec (CommRingCat.of ↥A) ⟶ X) (uA : Spec (CommRingCat.of ↥A) ⟶ pullback tb (Spec.map (CommRingCat.ofHom ρ))),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ ℓ = i₁ ∧ ℓ ≫ tb = Spec.map (CommRingCat.ofHom ρ) ∧
      uA ≫ pullback.snd _ _ = 𝟙 _ ∧ uA ≫ pullback.fst _ _ = ℓ := by
  have halg : (algebraMap ↥A K) = A.subtype := rfl
  obtain ⟨ℓ, h1, h2⟩ := exists_lift tb A i₁ (Spec.map (CommRingCat.ofHom ρ))
    (by rw [hi₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp, halg, hρ])
  refine ⟨ℓ, pullback.lift ℓ (𝟙 _) (by rw [h2, Category.id_comp]), ?_, h2, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
  rw [← halg]; exact h1

theorem exists_specialPoint {X : Scheme.{u}} {R : Type u} [CommRing R] (tb : X ⟶ Spec (CommRingCat.of R))
    {K : Type u} [Field K] (A : ValuationSubring K) (ρ : R →+* ↥A)
    (uA : Spec (CommRingCat.of ↥A) ⟶ pullback tb (Spec.map (CommRingCat.ofHom ρ))) (huA : uA ≫ pullback.snd _ _ = 𝟙 _)
    (bc : pullback tb (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) ⟶ pullback tb (Spec.map (CommRingCat.ofHom ρ)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) :
    ∃ uκ : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ pullback tb (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))),
      uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (uA ≫ pullback.fst _ _) ∧
      uκ ≫ pullback.snd _ _ = 𝟙 _ ∧
      uκ ≫ bc = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ uA ∧
      bc.base (uκ.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A))) = uA.base (IsLocalRing.closedPoint ↥A) := by
  have hfst : uA ≫ pullback.fst _ _ ≫ tb = Spec.map (CommRingCat.ofHom ρ) := by
    rw [pullback.condition, ← Category.assoc, huA, Category.id_comp]
  let uκ : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ pullback tb (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) :=
    pullback.lift (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ uA ≫ pullback.fst _ _) (𝟙 _)
      (by rw [Category.assoc, Category.assoc, hfst, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  have hκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (uA ≫ pullback.fst _ _) := pullback.lift_fst _ _ _
  have hκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hκbc : uκ ≫ bc = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ uA := by
    apply pullback.hom_ext
    · rw [Category.assoc, hbc₁, hκ₁, Category.assoc]
    · rw [Category.assoc, hbc₂, ← Category.assoc, hκ₂, Category.id_comp, Category.assoc, huA, Category.comp_id]
  refine ⟨uκ, hκ₁, hκ₂, hκbc, ?_⟩
  haveI : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue ↥A)).hom := by
    rw [CommRingCat.hom_ofHom]; infer_instance
  rw [← Scheme.Hom.comp_apply, hκbc, Scheme.Hom.comp_apply, Spec_closedPoint]

end SectionLift

end FrameReadH

namespace FrameReadH

section Component

universe u

theorem exists_closedPoint_efib_comp_eq {Y S C : Scheme.{u}} {κ : Type u} [Field κ] (toκ : Y ⟶ Spec (CommRingCat.of κ))
    (comp : Fin 2 → (S ⟶ Y)) (hci : ∀ i, IsClosedImmersion (comp i))
    (hsurj : ∀ x : Y, x ∈ Set.range (comp 0).base ∨ x ∈ Set.range (comp 1).base)
    (efib : C ⟶ S) [IsIso efib] (uκ : Spec (CommRingCat.of κ) ⟶ Y) (huκ : uκ ≫ toκ = 𝟙 _) :
    (∃ P0 : closedPoints C, (efib ≫ comp 0).base P0.1 = uκ.base (IsLocalRing.closedPoint κ)) ∨
    (∃ P0 : closedPoints C, (efib ≫ comp 1).base P0.1 = uκ.base (IsLocalRing.closedPoint κ)) := by

  haveI : IsClosedImmersion uκ := isClosedImmersion_of_comp_eq_id _ _ huκ
  have hx : uκ.base (IsLocalRing.closedPoint κ) ∈ closedPoints Y := by
    rw [mem_closedPoints_iff]
    have h := uκ.isClosedEmbedding.isClosed_range
    have e : Set.range uκ.base = {uκ.base (IsLocalRing.closedPoint κ)} := by
      ext z
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨w, rfl⟩; rw [Subsingleton.elim w (IsLocalRing.closedPoint κ)]
      · rintro rfl; exact ⟨_, rfl⟩
    rwa [e] at h

  have key : ∀ i : Fin 2, uκ.base (IsLocalRing.closedPoint κ) ∈ Set.range (comp i).base →
      ∃ P0 : closedPoints C, (efib ≫ comp i).base P0.1 = uκ.base (IsLocalRing.closedPoint κ) := by
    rintro i ⟨q, hq⟩
    have hqcl : q ∈ closedPoints S :=
      preimage_closedPoints_subset (comp i).isClosedEmbedding.injective (comp i).continuous (show (comp i).base q ∈ _ by rwa [hq])
    refine ⟨⟨(inv efib).base q, preimage_closedPoints_subset ?_ efib.continuous ?_⟩, ?_⟩
    · exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso efib))).injective
    · show efib.base ((inv efib).base q) ∈ closedPoints S
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; exact hqcl
    · show (efib ≫ comp i).base ((inv efib).base q) = _
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc, hq]
  rcases hsurj (uκ.base (IsLocalRing.closedPoint κ)) with h0 | h1
  · exact Or.inl (key 0 h0)
  · exact Or.inr (key 1 h1)

end Component

end FrameReadH

namespace FrameReadH

section FrobInj

theorem mem_of_pow_mem {F : Type*} [Field F] (O : ValuationSubring F) {x : F} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ O) : x ∈ O := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact O.zero_mem
  rcases O.mem_or_inv_mem x with hm | hinv
  · exact hm
  have e : x = x ^ n * (x⁻¹) ^ (n - 1) := by
    rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ hx), ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
  rw [e]
  exact mul_mem h (pow_mem hinv _)

theorem qExpFrobeniusPlaceModL_injective (K : Type) [Field K] (Γ : Subgroup SL(2, ℤ)) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] :
    Function.Injective (qExpFrobeniusPlaceModL K Γ ℓ) := by
  intro w w' h
  apply Place.ext
  ext x
  obtain ⟨y, hy⟩ := exists_qExpFrobeniusModL_eq_pow K Γ ℓ x
  have hℓ : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have key : ∀ v : Place K ↥(qExpFunctionFieldC K Γ),
      x ∈ v.toValuationSubring ↔ y ∈ (qExpFrobeniusPlaceModL K Γ ℓ v).toValuationSubring := by
    intro v
    rw [mem_qExpFrobeniusPlaceModL_iff, hy]
    exact ⟨fun hx => pow_mem hx ℓ, fun hx => mem_of_pow_mem _ hℓ hx⟩
  rw [key, key, h]

end FrobInj

end FrameReadH

namespace FrameReadH

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem T1_body
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
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (k : ℕ) (hk : ∀ s : ↥SS, e s ∣ k)

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (hn₀ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (hn₁ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2) :
    ∀ P ∈ (An s).dom,
      ∃ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (uA : Spec (CommRingCat.of ↥A) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))),
        𝔛.Meta.pointEquivPlace y = P ∧
        barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧
        uA ≫ pullback.fst _ _ = u.1 ∧ uA ≫ pullback.snd _ _ = 𝟙 _ ∧
        barPt A ≫ uA = y.1 ≫ gA ∧
        uA.base (IsLocalRing.closedPoint ↥A) =
          bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) := by
  intro P hP
  haveI := 𝔛.isProper
  haveI := 𝔛.efib_iso A hA ρ hρ

  obtain ⟨y, hyP⟩ : ∃ y, 𝔛.Meta.pointEquivPlace y = P := 𝔛.Meta.pointEquivPlace.surjective P

  have hi₁ : (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, y.2,
      Category.id_comp]
  obtain ⟨ℓ, uA, hℓ₁, hℓ₂, huA₂, huA₁⟩ :=
    exists_section_valuationSubring (toBase p (ΓM M H) hj) A ρ hρ (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) hi₁

  obtain ⟨uκ, hκ₁, hκ₂, -, hz⟩ := exists_specialPoint (toBase p (ΓM M H) hj) A ρ uA huA₂ bc hbc₁ hbc₂
  rw [huA₁] at hκ₁

  have hcomp := exists_closedPoint_efib_comp_eq (pullback.snd _ _) (𝔛.comp A hA ρ hρ) (𝔛.comp_isClosedImmersion A hA ρ hρ)
    (𝔛.comp_jointly_surjective A hA ρ hρ) (𝔛.efib A hA ρ hρ) uκ hκ₂

  obtain ⟨hdom, -⟩ := hAn s
  obtain ⟨hr₁, hnF, hnS⟩ := (hdom P).1 hP
  obtain ⟨-, hs1⟩ := (mem_ssNodePairsQExp_iff _).1 ((hSS s.1).1 s.2)
  obtain ⟨⟨hcl1, hpin1⟩, ⟨hcl0, hpin0⟩⟩ := 𝔛.node_pin A hA ρ hρ n
  have hinj := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.1
  have hφ := qExpFrobeniusPlaceModL_injective (ResidueField ↥A) (ΓN p M H hpM) p

  have hzn : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) =
      (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n := by
    rcases hcomp with ⟨P0, hP0⟩ | ⟨P0, hP0⟩
    ·
      have hread := hcompat 0 y ⟨ℓ, hℓ₂⟩ hℓ₁ uκ hκ₁ hκ₂ P0 hP0
      rw [hyP, if_pos rfl] at hread
      have hpl : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, hcl0⟩ := by
        rw [hpin0, hread, hr₁, ← hn₀]
      have hP0eq : P0 = ⟨_, hcl0⟩ := hinj hpl
      rw [← hP0, hP0eq]
      show (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base ((inv (𝔛.efib A hA ρ hρ)).base _) = _
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc, Scheme.Hom.comp_apply]
    ·
      have hread := hcompat 1 y ⟨ℓ, hℓ₂⟩ hℓ₁ uκ hκ₁ hκ₂ P0 hP0
      rw [hyP, if_neg (by decide)] at hread
      have hr₂ : Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ P = s.1.2 := by
        rcases hTD P with hA' | hB'
        · apply hφ
          rw [← hA', hr₁, hs1]
        · have hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα P) := by
            by_contra hnot
            exact hnF ⟨hB', hnot⟩
          apply hφ
          unfold JHPlaceSpecialization.Fixed at hfix
          rw [hB'] at hfix
          rw [hfix, hr₁, hs1]
      have hpl : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, hcl1⟩ := by
        rw [hpin1, hread, hr₂, ← hn₁]
      have hP0eq : P0 = ⟨_, hcl1⟩ := hinj hpl
      rw [← hP0, hP0eq]
      show (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base ((inv (𝔛.efib A hA ρ hρ)).base _) = _
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (pullback.fst _ _),
        pullback.condition, Scheme.Hom.comp_apply]
  refine ⟨y, ⟨ℓ, hℓ₂⟩, uA, hyP, hℓ₁, huA₁, huA₂, ?_, ?_⟩
  ·
    apply pullback.hom_ext
    · rw [Category.assoc, huA₁, hℓ₁, Category.assoc, hgA₁]
    · rw [Category.assoc, huA₂, Category.comp_id, Category.assoc, hgA₂, ← Category.assoc, y.2, Category.id_comp]
  · rw [← hz, hzn]

end FrameReadH

namespace FrameReadH

set_option synthInstance.maxHeartbeats 400000 in

theorem vslope_clause_at_node
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
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (k : ℕ) (hk : ∀ s : ↥SS, e s ∣ k)

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    [IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]
    (eK : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(xHFunctionFieldBar M H))
    (heK : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme U)] (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
      eK ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a)))
    (𝓛 : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules)
    (φ : ∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Γ(𝓛, U) →+ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField : Type))
    (hφres : ∀ (U V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(𝓛, U), φ V (𝓛.presheaf.map (homOfLE h).op m) = φ U m)
    (hφlin : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty U] (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)) (m : Γ(𝓛, U)),
          φ U (a • m) = algebraMap Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField a * φ U m)
    (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (hn₀ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (hn₁ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2)

    (hnode : ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧ g ≠ 0 ∧ (∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord (g) = 0 ∧
            ∃ h : P.evalAt (g) * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hxV : bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ V)
    (σ : Γ(𝓛, V)) (hσV : Scheme.Modules.IsFrameOn σ V) (f : ↥(xHFunctionFieldBar M H)) (hf : f = eK (φ V σ)) :
    ∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord f = 0 ∧
      ∃ h : P.evalAt f * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by
  obtain ⟨U, hxU, _, m, g, hg, hmU, hg0, a, ha, hlaw⟩ := hnode
  have htube := T1_body p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat'
    e he An hAn k hk gA hgA₁ hgA₂ bc hbc₁ hbc₂ s n hn₀ hn₁
  exact exists_forall_ord_eq_zero_and_isUnit_evalAt_of_isFrameOn_of_isFrameOn A 𝓛 φ hφres hφlin eK
    (An s).dom (fun P hP => ((An s).mem_dom P hP).1) (An s).param _ _ U hxU m g hg hmU hg0 a ha hlaw V hxV σ hσV f hf
    (forall_ord_eq_zero_and_isUnit_evalAt_of_tube 𝔛.Meta A gA eK heK _ (An s).dom
      (fun P hP => by obtain ⟨y, -, uA, hy, -, -, -, hgen, hcp⟩ := htube P hP; exact ⟨y, uA, hy, hgen, hcp⟩))

end FrameReadH

namespace FrameReadH

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ord_eq_zero_of_fixed_reduceFst
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
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (k : ℕ) (hk : ∀ s : ↥SS, e s ∣ k)

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    [IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]
    (eK : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(xHFunctionFieldBar M H))
    (heK : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme U)] (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
      eK ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a)))
    (𝓛 : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules)
    (φ : ∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Γ(𝓛, U) →+ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField : Type))
    (hφres : ∀ (U V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(𝓛, U), φ V (𝓛.presheaf.map (homOfLE h).op m) = φ U m)
    (hφlin : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty U] (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)) (m : Γ(𝓛, U)),
          φ U (a • m) = algebraMap Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField a * φ U m)

    (hfixed : (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
          JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
          (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q → V.ord g = 0) ∧
            (∃ (c : AlgebraicClosure ℚ) (hc : c • g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • g, hc⟩ ≠ 0 ∧
              ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q).ord (Rpd.R₁.residue ⟨c • g, hc⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0)))
    (hfixed' : (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
          JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q)) →
          (∀ s ∈ SS, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ≠ s.1) →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
              Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q → V.ord g = 0)))

    (V₀ : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (hV₀ : ∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
      (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) → bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ V₀)
    (hV₀' : ∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q)) →
      (∀ s ∈ SS, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ≠ s.1) →
      bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ V₀)
    (σ : Γ(𝓛, V₀)) (hσ : Scheme.Modules.IsFrameOn σ V₀) (f : ↥(xHFunctionFieldBar M H)) (hf : f = eK (φ V₀ σ)) :
    ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) →
      (∀ s ∈ SS, Psp.reduceFst α hα V ≠ s.1) → V.ord f = 0 := by
  intro V hfixV hnn
  haveI := 𝔛.isProper
  haveI := 𝔛.efib_iso A hA ρ hρ
  obtain ⟨y, hyV⟩ : ∃ y, 𝔛.Meta.pointEquivPlace y = V := 𝔛.Meta.pointEquivPlace.surjective V

  have hi₁ : (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, y.2,
      Category.id_comp]
  obtain ⟨ℓ, uA, hℓ₁, hℓ₂, huA₂, huA₁⟩ :=
    exists_section_valuationSubring (toBase p (ΓM M H) hj) A ρ hρ (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) hi₁
  have hgen : barPt A ≫ uA = y.1 ≫ gA := by
    apply pullback.hom_ext
    · rw [Category.assoc, huA₁, hℓ₁, Category.assoc, hgA₁]
    · rw [Category.assoc, huA₂, Category.comp_id, Category.assoc, hgA₂, ← Category.assoc, y.2, Category.id_comp]

  obtain ⟨uκ, hκ₁, hκ₂, -, hz⟩ := exists_specialPoint (toBase p (ΓM M H) hj) A ρ uA huA₂ bc hbc₁ hbc₂
  rw [huA₁] at hκ₁
  have hcomp := exists_closedPoint_efib_comp_eq (pullback.snd _ _) (𝔛.comp A hA ρ hρ) (𝔛.comp_isClosedImmersion A hA ρ hρ)
    (𝔛.comp_jointly_surjective A hA ρ hρ) (𝔛.efib A hA ρ hρ) uκ hκ₂

  obtain ⟨U, hzU, m, g, hg, hmU, hordg⟩ : ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : uA.base (IsLocalRing.closedPoint ↥A) ∈ U) (m : Γ(𝓛, U))
      (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)), Scheme.Modules.IsFrameOn m U ∧ V.ord g = 0 := by
    rcases hcomp with ⟨P0, hP0⟩ | ⟨P0, hP0⟩
    · have hread := hcompat 0 y ⟨ℓ, hℓ₂⟩ hℓ₁ uκ hκ₁ hκ₂ P0 hP0
      rw [hyV, if_pos rfl] at hread
      obtain ⟨U, hxU, _, m, g, hg, hmU, hordg, -⟩ := hfixed P0 (by rw [hread]; exact hfixV) (by rw [hread]; exact hnn)
      refine ⟨U, ?_, m, g, hg, hmU, hordg V hread.symm⟩
      rw [← hz, ← hP0]; exact hxU
    · have hread := hcompat 1 y ⟨ℓ, hℓ₂⟩ hℓ₁ uκ hκ₁ hκ₂ P0 hP0
      have hread' := hcompat' 1 y ⟨ℓ, hℓ₂⟩ hℓ₁ uκ hκ₁ hκ₂ P0 hP0
      rw [hyV, if_neg (by decide)] at hread hread'
      obtain ⟨U, hxU, _, m, g, hg, hmU, hordg⟩ := hfixed' P0 (by rw [← hread']; exact hfixV) (by rw [← hread']; exact hnn)
      refine ⟨U, ?_, m, g, hg, hmU, hordg V hread' hread.symm⟩
      rw [← hz, ← hP0]; exact hxU

  have hzV₀ : uA.base (IsLocalRing.closedPoint ↥A) ∈ V₀ := by
    rcases hcomp with ⟨P0, hP0⟩ | ⟨P0, hP0⟩
    · have hread := hcompat 0 y ⟨ℓ, hℓ₂⟩ hℓ₁ uκ hκ₁ hκ₂ P0 hP0
      rw [hyV, if_pos rfl] at hread
      rw [← hz, ← hP0]; exact hV₀ P0 (by rw [hread]; exact hfixV) (by rw [hread]; exact hnn)
    · have hread' := hcompat' 1 y ⟨ℓ, hℓ₂⟩ hℓ₁ uκ hκ₁ hκ₂ P0 hP0
      rw [hyV, if_neg (by decide)] at hread'
      rw [← hz, ← hP0]; exact hV₀' P0 (by rw [← hread']; exact hfixV) (by rw [← hread']; exact hnn)

  obtain ⟨_, u, hu, hfrg⟩ := exists_isUnit_reading_mul_of_isFrameOn 𝓛 φ hφres hφlin eK _ U hzU m g hg hmU V₀ hzV₀ σ hσ f hf

  have htr := forall_ord_eq_zero_and_isUnit_evalAt_of_tube 𝔛.Meta A gA eK heK (uA.base (IsLocalRing.closedPoint ↥A)) {V}
    (fun P hP => ⟨y, uA, hyV.trans (Set.mem_singleton_iff.mp hP).symm, hgen, rfl⟩)
  obtain ⟨hr0, -⟩ := htr (U ⊓ V₀) ⟨hzU, hzV₀⟩ u hu V rfl
  rcases eq_or_ne g 0 with hg0 | hg0
  · rw [hfrg, hg0, mul_zero, Place.ord_zero]
  · rw [hfrg, V.ord_mul ((hu.map _).map eK).ne_zero hg0, hr0, hordg, add_zero]

end FrameReadH

namespace FrameReadH

section ResidueAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_algebraMap_eq_zero (v : Place K F) {a : K} (ha : a ≠ 0) : v.ord (algebraMap K F a) = 0 := by
  let u : (v.toValuationSubring)ˣ :=
    ⟨⟨algebraMap K F a, v.algebraMap_mem' a⟩, ⟨algebraMap K F (a⁻¹), v.algebraMap_mem' (a⁻¹)⟩,
      Subtype.ext (by show algebraMap K F a * algebraMap K F (a⁻¹) = 1; rw [← map_mul, mul_inv_cancel₀ ha, map_one]),
      Subtype.ext (by show algebraMap K F (a⁻¹) * algebraMap K F a = 1; rw [← map_mul, inv_mul_cancel₀ ha, map_one])⟩
  exact v.ord_coe_unit u

variable {L : Type*} [Field L] {FM : Type*} [Field FM] [Algebra L FM] {Fb : Type*} [Field Fb]
  (A : ValuationSubring L) [Algebra (IsLocalRing.ResidueField ↥A) Fb]

theorem ord_residue_smul_eq_zero (R : RegularProlongation A FM Fb) (v : Place (IsLocalRing.ResidueField ↥A) Fb)
    {f r g : FM} {c cQ : L} (hfrg : f = r * g)
    (hr : r ∈ R.integers) (hru : R.residue ⟨r, hr⟩ ≠ 0) (hordr : v.ord (R.residue ⟨r, hr⟩) = 0)
    (hcQ : cQ • g ∈ R.integers) (hcQu : R.residue ⟨cQ • g, hcQ⟩ ≠ 0) (hordQ : v.ord (R.residue ⟨cQ • g, hcQ⟩) = 0)
    (hc : c • f ∈ R.integers) (hcu : R.residue ⟨c • f, hc⟩ ≠ 0) :
    v.ord (R.residue ⟨c • f, hc⟩) = 0 := by
  have ur := R.isUnit_of_residue_ne_zero hru
  have uQ := R.isUnit_of_residue_ne_zero hcQu
  have ucf := R.isUnit_of_residue_ne_zero hcu
  have hcQ0 : cQ ≠ 0 := by
    rintro rfl
    apply hcQu
    have e : (⟨(0 : L) • g, hcQ⟩ : R.integers) = 0 := Subtype.ext (zero_smul L g)
    rw [e, map_zero]

  let w : R.integers := ⟨c • f, hc⟩ * ↑(ur.unit⁻¹) * ↑(uQ.unit⁻¹)
  have hw_unit : IsUnit w := (ucf.mul (Units.isUnit _)).mul (Units.isUnit _)
  have hw0 : R.residue w ≠ 0 := R.residue_ne_zero_of_isUnit hw_unit
  have hcf_eq : (⟨c • f, hc⟩ : R.integers) = w * ⟨r, hr⟩ * ⟨cQ • g, hcQ⟩ := by
    show (⟨c • f, hc⟩ : R.integers) = (⟨c • f, hc⟩ * ↑(ur.unit⁻¹) * ↑(uQ.unit⁻¹)) * ⟨r, hr⟩ * ⟨cQ • g, hcQ⟩
    rw [show ((⟨c • f, hc⟩ : R.integers) * ↑(ur.unit⁻¹) * ↑(uQ.unit⁻¹)) * ⟨r, hr⟩ * ⟨cQ • g, hcQ⟩ =
        ⟨c • f, hc⟩ * (↑(ur.unit⁻¹) * ⟨r, hr⟩) * (↑(uQ.unit⁻¹) * ⟨cQ • g, hcQ⟩) by ring,
      ur.val_inv_mul, uQ.val_inv_mul, mul_one, mul_one]
  have e1 : (((↑(ur.unit⁻¹) : R.integers)) : FM) * r = 1 := by
    have h := congrArg (fun z : R.integers => (z : FM)) ur.val_inv_mul
    simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using h
  have e2 : (((↑(uQ.unit⁻¹) : R.integers)) : FM) * (cQ • g) = 1 := by
    have h := congrArg (fun z : R.integers => (z : FM)) uQ.val_inv_mul
    simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using h
  have hw_val : (w : FM) = algebraMap L FM (c / cQ) := by
    show ((⟨c • f, hc⟩ : R.integers) : FM) * ((↑(ur.unit⁻¹) : R.integers) : FM) * ((↑(uQ.unit⁻¹) : R.integers) : FM) = _
    rw [eq_inv_of_mul_eq_one_left e1, eq_inv_of_mul_eq_one_left e2]
    show c • f * r⁻¹ * (cQ • g)⁻¹ = _
    have hr0 : r ≠ 0 := by rintro rfl; rw [mul_zero] at e1; exact zero_ne_one e1
    have hg0 : cQ • g ≠ 0 := by
      intro h; apply hcQu
      have e : (⟨cQ • g, hcQ⟩ : R.integers) = 0 := Subtype.ext h
      rw [e, map_zero]
    have hg0' : g ≠ 0 := by rintro rfl; exact hg0 (smul_zero cQ)
    have hcQ0' : algebraMap L FM cQ ≠ 0 := (map_ne_zero _).mpr hcQ0
    rw [hfrg, Algebra.smul_def, Algebra.smul_def, map_div₀]
    field_simp

  have hmemA : c / cQ ∈ A := (R.algebraMap_mem_iff (c / cQ)).mp (hw_val ▸ w.2)
  have hres_w : R.residue w = algebraMap (IsLocalRing.ResidueField ↥A) Fb (IsLocalRing.residue ↥A ⟨c / cQ, hmemA⟩) := by
    rw [← R.residue_algebraMap ⟨c / cQ, hmemA⟩]
    congr 1
    exact Subtype.ext hw_val
  have hres_w0 : IsLocalRing.residue ↥A ⟨c / cQ, hmemA⟩ ≠ 0 := by
    intro h0
    apply hw0
    rw [hres_w, h0, map_zero]

  rw [hcf_eq, map_mul, map_mul, v.ord_mul (mul_ne_zero hw0 hru) hcQu, v.ord_mul hw0 hru, hres_w,
    ord_algebraMap_eq_zero v hres_w0, hordr, hordQ, add_zero, add_zero]

end ResidueAlgebra

end FrameReadH

namespace FrameReadH

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem ord_residue_eq_zero_of_fixed
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
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (k : ℕ) (hk : ∀ s : ↥SS, e s ∣ k)

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    [IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]
    (eK : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(xHFunctionFieldBar M H))
    (heK : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme U)] (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
      eK ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a)))
    (𝓛 : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules)
    (φ : ∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Γ(𝓛, U) →+ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField : Type))
    (hφres : ∀ (U V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(𝓛, U), φ V (𝓛.presheaf.map (homOfLE h).op m) = φ U m)
    (hφlin : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty U] (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)) (m : Γ(𝓛, U)),
          φ U (a • m) = algebraMap Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField a * φ U m)

    (hfixed : (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
          JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
          (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q → V.ord g = 0) ∧
            (∃ (c : AlgebraicClosure ℚ) (hc : c • g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • g, hc⟩ ≠ 0 ∧
              ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q).ord (Rpd.R₁.residue ⟨c • g, hc⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0)))

    (V₀ : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (hV₀ : ∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
      (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) → bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ V₀)
    (σ : Γ(𝓛, V₀)) (hσ : Scheme.Modules.IsFrameOn σ V₀) (f : ↥(xHFunctionFieldBar M H)) (hf : f = eK (φ V₀ σ))
    (c : AlgebraicClosure ℚ) (hc : c • f ∈ Rpd.R₁.integers) (hres : Rpd.R₁.residue ⟨c • f, hc⟩ ≠ 0)

    (hdense : ∀ (W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (x : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))),
      bc.base x ∈ W → genericPoint 𝔛.Meta.C ∈ gA ⁻¹ᵁ W) :
    ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
      v.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0 := by
  intro v hfix hnn
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  haveI := 𝔛.efib_iso A hA ρ hρ

  have hbc : bc = bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl :=
    pullback.hom_ext (by rw [hbc₁, bcMap_fst]) (by rw [hbc₂, bcMap_snd])
  have hgAeq : gA = 𝔛.eeta ≫ (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) : pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) := by
    apply pullback.hom_ext
    · rw [hgA₁, Category.assoc, pullback.lift_fst, Category.comp_id]
    · rw [hgA₂, Category.assoc, pullback.lift_snd, ← Category.assoc, 𝔛.heeta]
  subst hbc
  subst hgAeq

  obtain ⟨Q, hQv⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.2 v
  obtain ⟨U, hzU, _, m, g, hg, hmU, -, cQ, hcQ, hcQu, hordQ⟩ :=
    hfixed Q (by rw [hQv]; exact hfix) (by rw [hQv]; exact hnn)
  rw [hQv] at hordQ
  have hzV₀ := hV₀ Q (by rw [hQv]; exact hfix) (by rw [hQv]; exact hnn)

  obtain ⟨hneW, u, hu, hfrg⟩ := exists_isUnit_reading_mul_of_isFrameOn 𝓛 φ hφres hφlin eK _ U hzU m g hg hmU V₀ hzV₀ σ hσ f hf

  have hgenW := hdense (U ⊓ V₀) _ ⟨hzU, hzV₀⟩
  haveI : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) : pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ)) ⁻¹ᵁ (U ⊓ V₀))) := ⟨⟨_, hgenW⟩⟩
  have hξ : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ U ⊓ V₀ :=
    ((genericPoint_specializes Q.1).map (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).continuous).mem_open
      (U ⊓ V₀).isOpen ⟨hzU, hzV₀⟩
  obtain ⟨h₁, ⟨hg₀, hres_eq⟩, hunit⟩ :=
    (ModularCurve.XHDRModelAtP.readA_mem_integers_and_residue_eq_restrict_comp_of_mem p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ Psp Rpd hwgen
      (U ⊓ V₀) hgenW u).1 hξ

  have hRA := heK (U ⊓ V₀) u

  haveI : Nonempty (Scheme.Opens.toScheme ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) ⁻¹ᵁ (U ⊓ V₀))) :=
    ⟨⟨Q.1, ⟨hzU, hzV₀⟩⟩⟩
  have hK4 := CurveModel.ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit (𝔛.Mfib A hA ρ hρ)
    ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) ⁻¹ᵁ (U ⊓ V₀)) Q ⟨hzU, hzV₀⟩
    (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).app (U ⊓ V₀)).hom u) (hu.map _)
  rw [hQv] at hK4
  have hordr : v.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 0 := by rw [hres_eq]; exact hK4
  have hru : Rpd.R₁.residue ⟨_, h₁⟩ ≠ 0 := hunit ((hu.map _))

  have hfrg' : f = _ * g := hfrg.trans (congrArg (· * g) hRA)
  exact ord_residue_smul_eq_zero A Rpd.R₁ v hfrg' h₁ hru hordr hcQ hcQu hordQ hc hres

end FrameReadH

namespace FrameReadH

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem ne_zero_and_residue_smul_ne_zero_of_basePoint
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
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (k : ℕ) (hk : ∀ s : ↥SS, e s ∣ k)

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    [IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]
    (eK : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(xHFunctionFieldBar M H))
    (heK : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme U)] (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
      eK ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a)))
    (𝓛 : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules)
    (φ : ∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Γ(𝓛, U) →+ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField : Type))
    (hφres : ∀ (U V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(𝓛, U), φ V (𝓛.presheaf.map (homOfLE h).op m) = φ U m)
    (hφlin : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty U] (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)) (m : Γ(𝓛, U)),
          φ U (a • m) = algebraMap Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField a * φ U m)

    (Q₀ : closedPoints (𝔛.Mfib A hA ρ hρ).C) (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hzU : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q₀.1) ∈ U)
    (m : Γ(𝓛, U)) (g : ↥(xHFunctionFieldBar M H)) (hg : g = eK (φ U m)) (hmU : Scheme.Modules.IsFrameOn m U)
    (c : AlgebraicClosure ℚ) (hcg : c • g ∈ Rpd.R₁.integers) (hresg : Rpd.R₁.residue ⟨c • g, hcg⟩ ≠ 0)

    (V₀ : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hzV₀ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q₀.1) ∈ V₀)
    (σ : Γ(𝓛, V₀)) (hσ : Scheme.Modules.IsFrameOn σ V₀) (f : ↥(xHFunctionFieldBar M H)) (hf : f = eK (φ V₀ σ))

    (hdense : ∀ (W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (x : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))),
      bc.base x ∈ W → genericPoint 𝔛.Meta.C ∈ gA ⁻¹ᵁ W) :
    f ≠ 0 ∧ ∃ hc : c • f ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨c • f, hc⟩ ≠ 0 := by
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral

  have hbc : bc = bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl :=
    pullback.hom_ext (by rw [hbc₁, bcMap_fst]) (by rw [hbc₂, bcMap_snd])
  have hgAeq : gA = 𝔛.eeta ≫ (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) : pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) := by
    apply pullback.hom_ext
    · rw [hgA₁, Category.assoc, pullback.lift_fst, Category.comp_id]
    · rw [hgA₂, Category.assoc, pullback.lift_snd, ← Category.assoc, 𝔛.heeta]
  subst hbc
  subst hgAeq

  obtain ⟨hneW, u, hu, hfrg⟩ := exists_isUnit_reading_mul_of_isFrameOn 𝓛 φ hφres hφlin eK _ U hzU m g hg hmU V₀ hzV₀ σ hσ f hf

  have hgenW := hdense (U ⊓ V₀) _ ⟨hzU, hzV₀⟩
  haveI : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) : pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ)) ⁻¹ᵁ (U ⊓ V₀))) := ⟨⟨_, hgenW⟩⟩
  have hξ : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ U ⊓ V₀ :=
    ((genericPoint_specializes Q₀.1).map (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).continuous).mem_open
      (U ⊓ V₀).isOpen ⟨hzU, hzV₀⟩
  obtain ⟨h₁, -, hunit⟩ :=
    (ModularCurve.XHDRModelAtP.readA_mem_integers_and_residue_eq_restrict_comp_of_mem p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ Psp Rpd hwgen
      (U ⊓ V₀) hgenW u).1 hξ
  have hRA := heK (U ⊓ V₀) u
  have hru : Rpd.R₁.residue ⟨_, h₁⟩ ≠ 0 := hunit (hu.map _)
  have hfrg' : f = _ * g := hfrg.trans (congrArg (· * g) hRA)

  have hcf : c • f = _ * (c • g) := (congrArg (c • ·) hfrg').trans (mul_smul_comm c _ g).symm
  have hmem : c • f ∈ Rpd.R₁.integers := by rw [hcf]; exact mul_mem h₁ hcg
  have hprod : (⟨c • f, hmem⟩ : Rpd.R₁.integers) = ⟨_, h₁⟩ * ⟨c • g, hcg⟩ := Subtype.ext hcf
  refine ⟨?_, hmem, ?_⟩
  ·
    have hg0 : g ≠ 0 := by
      rintro rfl
      apply hresg
      have e : (⟨c • (0 : ↥(xHFunctionFieldBar M H)), hcg⟩ : Rpd.R₁.integers) = 0 := Subtype.ext (smul_zero c)
      rw [e, map_zero]
    have hr0 : eK (algebraMap _ _ u) ≠ 0 := ((hu.map _).map eK).ne_zero
    rw [hfrg]
    exact mul_ne_zero hr0 hg0
  · rw [hprod, map_mul]
    exact mul_ne_zero hru hresg

end FrameReadH

namespace FrameReadH

set_option synthInstance.maxHeartbeats 400000 in

theorem isGoodDiv_of_ord_eq_zero
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
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (k : ℕ) (hk : ∀ s : ↥SS, e s ∣ k)

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (f : ↥(xHFunctionFieldBar M H))
    (hann : ∀ (s : ↥SS), ∀ P ∈ (An s).dom, P.ord f = 0)
    (hfixord : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) →
      (∀ s ∈ SS, Psp.reduceFst α hα V ≠ s.1) → V.ord f = 0)
    (hδφ : ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ
        (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v)) :
    ∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) →
      Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G := by
  intro G hG W hW
  rw [Finsupp.mem_support_iff, hG] at hW
  by_contra hns
  have hn1 : ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W := fun h => hns (Or.inl h)
  have hn2 : ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W := fun h => hns (Or.inr h)

  have hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα W) := by
    rcases hTD W with hA' | hB'
    · have h2 : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W) := by
        by_contra hnf
        exact hn2 ⟨hA', hnf⟩
      rw [hA']
      exact hδφ _ h2
    · by_contra hnf
      exact hn1 ⟨hB', hnf⟩

  apply hW
  by_cases hnode : ∃ s ∈ SS, Psp.reduceFst α hα W = s.1
  · obtain ⟨s, hs, hs1⟩ := hnode
    exact hann ⟨s, hs⟩ W (((hAn ⟨s, hs⟩).1 W).2 ⟨hs1, hn1, hn2⟩)
  · push Not at hnode
    exact hfixord W hfix hnode

end FrameReadH

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
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
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (k : ℕ) (hk : ∀ s : ↥SS, e s ∣ k)

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))

    [IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]
    (eK : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(xHFunctionFieldBar M H))
    (heK : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme U)] (a : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)),
      eK ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a)))

    (hTW : ∃ (𝓛 : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules) (_ : Scheme.Modules.IsInvertible 𝓛)
        (φ : ∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Γ(𝓛, U) →+ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField : Type)),

        (∀ (U V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(𝓛, U), φ V (𝓛.presheaf.map (homOfLE h).op m) = φ U m) ∧
        (∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty U] (a : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)) (m : Γ(𝓛, U)),
          φ U (a • m) = algebraMap Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField a * φ U m) ∧
        (∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Nonempty U → Function.Injective (φ U)) ∧

        (∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
      (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2),
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧ g ≠ 0 ∧ (∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord (g) = 0 ∧
            ∃ h : P.evalAt (g) * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A))) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
          JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
          (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q → V.ord g = 0) ∧
            (∃ (c : AlgebraicClosure ℚ) (hc : c • g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • g, hc⟩ ≠ 0 ∧
              ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q).ord (Rpd.R₁.residue ⟨c • g, hc⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
          JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q)) →
          (∀ s ∈ SS, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ≠ s.1) →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
              Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q → V.ord g = 0)) ∧

        (∃ Uaff : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, IsAffineOpen Uaff ∧
          (∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2), bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ Uaff) ∧
          (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
            JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
          (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) → bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ Uaff) ∧
          (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
            JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q)) →
          (∀ s ∈ SS, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ≠ s.1) → bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ Uaff) ∧
          (∃ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ Uaff)
            (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U)) (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
              (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) ∧ Scheme.Modules.IsFrameOn m U ∧
              ∃ (c : AlgebraicClosure ℚ) (hc : c • g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • g, hc⟩ ≠ 0)) ∧

        (∀ (x : closedPoints 𝔛.Meta.C) (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens), gA.base x.1 ∈ U → ∀ (m : Γ(𝓛, U)) (g : ↥(xHFunctionFieldBar M H)), g = eK (φ U m) →
          Scheme.Modules.IsFrameOn m U → (𝔛.Meta.placeOfPoint x).ord g ≠ 0 →
          Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (𝔛.Meta.placeOfPoint x) ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ (𝔛.Meta.placeOfPoint x)))
    :
    ∃ (f : ↥(xHFunctionFieldBar M H)) (c : AlgebraicClosure ℚ) (hc : c • f ∈ Rpd.R₁.integers),
          f ≠ 0 ∧ Rpd.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
          (∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) → Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G) ∧
          (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) →
            (∀ s ∈ SS, Psp.reduceFst α hα V ≠ s.1) → V.ord f = 0) ∧
          (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
            v.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0) ∧
          (∀ s : ↥SS, ∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord f = 0 ∧
            ∃ h : P.evalAt f * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) := by
  classical
  haveI := 𝔛.isProper
  haveI := 𝔛.efib_iso A hA ρ hρ
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  obtain ⟨𝓛, hLinv, φ, hφres, hφlin, hφinj, hnode, hfixed, hfixed', haff, hgen⟩ := hTW
  obtain ⟨Uaff, hUaff, hcrossU, hfixU, hfixU', Q₀, U₀, hz₀U₀, hz₀aff, _, m₀, g₀, hg₀, hnn₀, hm₀U₀, c, hcg₀, hresg₀⟩ := haff

  have hIG := ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
    p M hpM H A hA hj 𝔛 ρ hρ gA hgA₁ hgA₂
  have hdense : ∀ (W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (x : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))),
      bc.base x ∈ W → genericPoint 𝔛.Meta.C ∈ gA ⁻¹ᵁ W := by
    intro W x hx
    have hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ W)) := hIG.2.1 W ⟨⟨_, hx⟩⟩
    exact ((genericPoint_spec 𝔛.Meta.C).mem_open_set_iff (gA ⁻¹ᵁ W).isOpen).mpr (by simpa using hne)

  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    obtain ⟨k', hk'⟩ := h
    refine ⟨k', ?_⟩
    have := Nat.div_mul_cancel hpM
    rw [hk'] at this
    rw [← this]; ring
  have hcomm : ∀ v, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (δ v) =
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v) := by
    intro v
    rw [hδ v, hδ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v)]
    exact ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN
      (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) v
  have hδφ : ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ
        (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v) := by
    intro v hv
    unfold JHPlaceSpecialization.Fixed at hv ⊢
    rw [← hcomm, hv]

  have hbc : bc = bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl :=
    pullback.hom_ext (by rw [hbc₁, bcMap_fst]) (by rw [hbc₂, bcMap_snd])
  haveI hbcCI : IsClosedImmersion bc := by
    rw [hbc]
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) (inferInstance : IsClosedImmersion (𝟙 _))
      (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (IsLocalRing.residue ↥A)) Ideal.Quotient.mk_surjective)
      (Category.id_comp _).symm (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])
  have hclosed : ∀ (i : Fin 2) (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      IsClosed ({bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base Q.1)} : Set ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))) := by
    intro i Q
    haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ i
    have h := ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i) ≫ bc).isClosedEmbedding.isClosedMap _ Q.2
    rwa [Set.image_singleton] at h

  have hssfin : (ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p).Finite :=
    (SS.finite_toSet.image Prod.snd).subset fun y hy => ⟨(qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y, y),
      (hSS _).2 (frob_mk_mem_ssNodePairsQExp hy), rfl⟩
  haveI : Finite ↥(ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p) := hssfin.to_subtype
  haveI : Finite ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) := Finite.of_equiv _ (𝔛.nodeEquiv A hA ρ hρ).symm
  have hFixFin := ModularCurve.JHPlaceSpecialization.finite_setOf_fixed_of_eq_gammaLift p M H hpM hpM2 A hA pb hpb δ hδ
  have hinjP := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.1
  have hφinjP := FrameReadH.qExpFrobeniusPlaceModL_injective (ResidueField ↥A) (ΓN p M H hpM) p

  let T : Set ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) :=
    ((Set.range (fun n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) =>
        bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n)) ∪
      (fun Q : closedPoints (𝔛.Mfib A hA ρ hρ).C => bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1)) ''
        {Q | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ∧
          ∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1}) ∪
      (fun Q : closedPoints (𝔛.Mfib A hA ρ hρ).C => bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1)) ''
        {Q | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ
            (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q)) ∧
          ∀ s ∈ SS, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ≠ s.1}) ∪
      {bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q₀.1)}
  have hTfin : T.Finite := by
    refine (((Set.finite_range _).union (Set.Finite.image _ ?_)).union (Set.Finite.image _ ?_)).union (Set.finite_singleton _)
    · exact (hFixFin.preimage (fun _ _ _ _ h => hinjP h)).subset fun Q hQ => hQ.1
    · exact (hFixFin.preimage (f := fun Q : closedPoints (𝔛.Mfib A hA ρ hρ).C =>
          qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q))
        (fun _ _ _ _ h => hinjP (hφinjP h))).subset fun Q hQ => hQ.1
  have hTU : T ⊆ (Uaff : Set ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))) := by
    rintro x (((⟨n, rfl⟩ | ⟨Q, ⟨hQf, hQn⟩, rfl⟩) | ⟨Q, ⟨hQf, hQn⟩, rfl⟩) | hx)
    · exact hcrossU ⟨_, (hSS _).2 (𝔛.nodePair_mem A hA ρ hρ n)⟩ n rfl rfl
    · exact hfixU Q hQf hQn
    · exact hfixU' Q hQf hQn
    · rw [Set.mem_singleton_iff.mp hx]; exact hz₀aff
  have hTcl : ∀ t ∈ T, IsClosed ({t} : Set ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))) := by
    rintro t (((⟨n, rfl⟩ | ⟨Q, -, rfl⟩) | ⟨Q, -, rfl⟩) | ht)
    · obtain ⟨-, ⟨hcl0, -⟩⟩ := 𝔛.node_pin A hA ρ hρ n
      have h := hclosed 0 ⟨_, hcl0⟩
      rwa [show (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base ((inv (𝔛.efib A hA ρ hρ)).base
          ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)) =
          (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n by
        rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc, Scheme.Hom.comp_apply]] at h
    · exact hclosed 0 Q
    · exact hclosed 1 Q
    · rw [Set.mem_singleton_iff.mp ht]; exact hclosed 0 Q₀

  obtain ⟨V₀, -, σ, hTV₀, hσ⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn_of_finite_subset_affineOpen
    𝓛 hLinv Uaff hUaff T hTfin hTU hTcl
  have hxV₀ : ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ V₀ :=
    fun n => hTV₀ (Or.inl (Or.inl (Or.inl ⟨n, rfl⟩)))
  have hV₀ : ∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
      (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) → bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ V₀ :=
    fun Q hf hn => hTV₀ (Or.inl (Or.inl (Or.inr ⟨Q, ⟨hf, hn⟩, rfl⟩)))
  have hV₀' : ∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q)) →
      (∀ s ∈ SS, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ≠ s.1) →
      bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ V₀ :=
    fun Q hf hn => hTV₀ (Or.inl (Or.inr ⟨Q, ⟨hf, hn⟩, rfl⟩))
  have hz₀V₀ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q₀.1) ∈ V₀ := hTV₀ (Or.inr rfl)

  obtain ⟨hf0, hc, hres⟩ := FrameReadH.ne_zero_and_residue_smul_ne_zero_of_basePoint p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ
    Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' e he An hAn k hk gA hgA₁ hgA₂ bc hbc₁ hbc₂ eK heK 𝓛 φ hφres hφlin
    Q₀ U₀ hz₀U₀ m₀ g₀ hg₀ hm₀U₀ c hcg₀ hresg₀ V₀ hz₀V₀ σ hσ _ rfl hdense
  have hfixord := FrameReadH.ord_eq_zero_of_fixed_reduceFst p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ
    Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' e he An hAn k hk gA hgA₁ hgA₂ bc hbc₁ hbc₂ eK heK 𝓛 φ hφres hφlin
    hfixed hfixed' V₀ hV₀ hV₀' σ hσ _ rfl
  have hfixres := FrameReadH.ord_residue_eq_zero_of_fixed p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ
    Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' e he An hAn k hk gA hgA₁ hgA₂ bc hbc₁ hbc₂ eK heK 𝓛 φ hφres hφlin
    hfixed V₀ hV₀ σ hσ _ rfl c hc hres hdense
  have hann : ∀ s : ↥SS, ∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord (eK (φ V₀ σ)) = 0 ∧
      ∃ h : P.evalAt (eK (φ V₀ σ)) * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A) := by
    intro s
    obtain ⟨hs2, hs1⟩ := (mem_ssNodePairsQExp_iff _).1 ((hSS s.1).1 s.2)
    let n := (𝔛.nodeEquiv A hA ρ hρ).symm ⟨s.1.2, hs2⟩
    have hn₁ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2 := congrArg Subtype.val ((𝔛.nodeEquiv A hA ρ hρ).apply_symm_apply ⟨s.1.2, hs2⟩)
    have hn₀ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1 := by
      show qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (𝔛.placeOn1 A hA ρ hρ n) = _
      rw [hn₁, hs1]
    exact FrameReadH.vslope_clause_at_node p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ
      Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' e he An hAn k hk gA hgA₁ hgA₂ bc hbc₁ hbc₂ eK heK 𝓛 φ hφres hφlin
      s n hn₀ hn₁ (hnode s n hn₀ hn₁) V₀ (hxV₀ n) σ hσ _ rfl
  have hgood := FrameReadH.isGoodDiv_of_ord_eq_zero p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ
    Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' e he An hAn k hk gA hgA₁ hgA₂ bc hbc₁ hbc₂ (eK (φ V₀ σ))
    (fun s P hP => by obtain ⟨a, -, hP'⟩ := hann s; exact (hP' P hP).1) hfixord hδφ
  exact ⟨eK (φ V₀ σ), c, hc, hf0, hres, hgood, hfixord, hfixres, hann⟩

end S_ModularCurve_XHDRModelAtP_exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_isInvertible_frames
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_isInvertible_frames (solution)
