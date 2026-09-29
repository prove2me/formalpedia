-- Prove2me | solution 1 for ModularCurve.FullLevel.forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e5c11892-cdc2-5036-83f8-27efae69478e

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0
import Theorems.Thm_ModularCurve_FullLevel_exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_iff_map_mem_of_forall_place_eq_of_testFamily
import Theorems.Thm_ModularCurve_FullLevel_exists_rational_integral_cuspRegular_evalAt_ne_of_isRational_of_ne
import Theorems.Thm_ModularCurve_FullLevel_inclusion_mem_chartAlgFin_of_mem_integers_of_cuspRegular_descent_of_eq_three
import Theorems.Thm_ModularCurve_exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jqModC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_qExpand_jqModC_mem_intFormRatiosC_gammaH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms"
p2m_attr_erase "instance" "CuspForm.GammaH_finiteIndex AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation DrinfeldCurve.instAlgebraCoordRing DrinfeldCurve.instCommRingCoordRing"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.RegularProlongation.coe_integersEquiv AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq"
p2m_attr_erase "simp" "MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false

p2m_open "AlgebraicCurve~isAlgebraic_adjoin_of_transcendental ModularCurve~coeffMap_qExpand~coeffEmb_qExpand P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.levelH FullLevel.fieldBar xHFunctionFieldC qExpFunctionFieldC intFormRatiosC_subset modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand constantCoeff_jNum jq jq_mem divisorExpansions modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jqModC jqNModC jqModC_rat map_jqModC modularFunctionFieldC jqModC_mem IsSupersingularPlace ssPlaces jGeomGen transcendental_jqModC exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull qTwist qTwist_coeff qTwist_one_apply exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable finiteDimensional_adjoin_jqModC qExpand_jqModC_mem_intFormRatiosC_gammaH"
p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_qExpand"

namespace S3bEmbFrac

p2m_open "HahnSeries IntermediateField AlgebraicCurve~isAlgebraic_adjoin_of_transcendental IsLocalRing"

section Coeff

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem coeffMap_subtype_injective : Function.Injective (coeffMap A.subtype) := by
  intro x y h
  ext k
  have hk := congrArg (fun z : LaurentSeries L => z.coeff k) h
  simp only [coeffMap_coeff] at hk
  exact hk

theorem coeffMap_subtype_ne_zero {x : LaurentSeries A}
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0) : coeffMap A.subtype x ≠ 0 := by
  intro h
  apply hx
  have hx0 : x = 0 := coeffMap_subtype_injective A (by rw [h, map_zero])
  rw [hx0, map_zero]

theorem ne_zero_of_residue_ne_zero {x : LaurentSeries A}
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0) : x ≠ 0 := by
  rintro rfl
  exact hx (map_zero _)

theorem residue_mul_ne_zero {x y : LaurentSeries A}
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0) (hy : coeffMap (IsLocalRing.residue A) y ≠ 0) :
    coeffMap (IsLocalRing.residue A) (x * y) ≠ 0 := by
  rw [map_mul]
  exact mul_ne_zero hx hy

theorem coeffMap_C {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    coeffMap f (HahnSeries.C r) = HahnSeries.C (f r) :=
  HahnSeries.map_C r f

theorem coeffMap_subtype_C (a : A) : coeffMap A.subtype (HahnSeries.C a) = HahnSeries.C (a : L) :=
  coeffMap_C _ _

theorem algebraMap_eq_C (c : L) : algebraMap L (LaurentSeries L) c = HahnSeries.C c := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) : coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

end Coeff

section ConstantAction

variable (L : Type*) [Field L]

theorem coe_smul_eq_C_mul (F : IntermediateField L (LaurentSeries L)) (c : L) (x : F) :
    ((c • x : F) : LaurentSeries L) = HahnSeries.C c * (x : LaurentSeries L) := by
  rw [@Algebra.smul_def L F _ _ (SubalgebraClass.toAlgebra F), MulMemClass.coe_mul,
    SubalgebraClass.coe_algebraMap, algebraMap_eq_C]

theorem coe_algebraMap_eq_C (F : IntermediateField L (LaurentSeries L)) (c : L) :
    ((algebraMap L F c : F) : LaurentSeries L) = HahnSeries.C c := by
  rw [SubalgebraClass.coe_algebraMap, algebraMap_eq_C]

theorem C_mem (F : IntermediateField L (LaurentSeries L)) (c : L) : HahnSeries.C c ∈ F := by
  rw [← algebraMap_eq_C]
  exact F.algebraMap_mem c

end ConstantAction

section Frac

variable {L : Type*} [Field L] (A : ValuationSubring L) (F₀ : IntermediateField L (LaurentSeries L))

def IsFrac (f : LaurentSeries L) : Prop :=
  ∃ (c : L) (x y : LaurentSeries A),
    coeffMap (IsLocalRing.residue A) x ≠ 0 ∧ coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
    coeffMap A.subtype x ∈ F₀ ∧ coeffMap A.subtype y ∈ F₀ ∧
    f * coeffMap A.subtype y = HahnSeries.C c * coeffMap A.subtype x

def Rescales : Prop :=
  ∀ w : LaurentSeries A, coeffMap A.subtype w ∈ F₀ → w ≠ 0 →
    ∃ (c : L) (w₁ : LaurentSeries A), c ≠ 0 ∧ coeffMap (IsLocalRing.residue A) w₁ ≠ 0 ∧
      HahnSeries.C c * coeffMap A.subtype w = coeffMap A.subtype w₁

variable {A F₀}

theorem isFrac_C (c : L) : IsFrac A F₀ (HahnSeries.C c) :=
  ⟨c, 1, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one]; exact one_ne_zero,
    by rw [map_one]; exact one_mem _, by rw [map_one]; exact one_mem _, rfl⟩

theorem isFrac_zero : IsFrac A F₀ 0 := by
  have h := isFrac_C (A := A) (F₀ := F₀) 0
  rwa [map_zero] at h

theorem isFrac_one : IsFrac A F₀ 1 := by
  have h := isFrac_C (A := A) (F₀ := F₀) 1
  rwa [map_one] at h

theorem IsFrac.eq_zero_of_const_eq_zero {f : LaurentSeries L} {x y : LaurentSeries A}
    (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (h : f * coeffMap A.subtype y = HahnSeries.C (0 : L) * coeffMap A.subtype x) : f = 0 := by
  rw [map_zero, zero_mul] at h
  exact (mul_eq_zero.mp h).resolve_right (coeffMap_subtype_ne_zero A hy)

theorem isFrac_mul {f g : LaurentSeries L} (hf : IsFrac A F₀ f) (hg : IsFrac A F₀ g) :
    IsFrac A F₀ (f * g) := by
  obtain ⟨c, x, y, hx, hy, hxF, hyF, hf⟩ := hf
  obtain ⟨c', x', y', hx', hy', hxF', hyF', hg⟩ := hg
  refine ⟨c * c', x * x', y * y', residue_mul_ne_zero A hx hx', residue_mul_ne_zero A hy hy', ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_mem hxF hxF'
  · rw [map_mul]; exact mul_mem hyF hyF'
  · rw [map_mul, map_mul, map_mul]
    calc f * g * (coeffMap A.subtype y * coeffMap A.subtype y')
        = (f * coeffMap A.subtype y) * (g * coeffMap A.subtype y') := by ring
      _ = (HahnSeries.C c * coeffMap A.subtype x) * (HahnSeries.C c' * coeffMap A.subtype x') := by
          rw [hf, hg]
      _ = HahnSeries.C c * HahnSeries.C c' * (coeffMap A.subtype x * coeffMap A.subtype x') := by ring

theorem isFrac_neg {f : LaurentSeries L} (hf : IsFrac A F₀ f) : IsFrac A F₀ (-f) := by
  obtain ⟨c, x, y, hx, hy, hxF, hyF, hf⟩ := hf
  refine ⟨-c, x, y, hx, hy, hxF, hyF, ?_⟩
  rw [neg_mul, hf, map_neg, neg_mul]

theorem isFrac_inv {f : LaurentSeries L} (hf : IsFrac A F₀ f) : IsFrac A F₀ f⁻¹ := by
  obtain ⟨c, x, y, hx, hy, hxF, hyF, hf⟩ := hf
  rcases eq_or_ne c 0 with rfl | hc
  · rw [IsFrac.eq_zero_of_const_eq_zero hy hf, inv_zero]
    exact isFrac_zero
  have hCc : (HahnSeries.C c : LaurentSeries L) ≠ 0 := HahnSeries.C_ne_zero hc
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hf
    exact mul_ne_zero hCc (coeffMap_subtype_ne_zero A hx) hf.symm
  refine ⟨c⁻¹, y, x, hy, hx, hyF, hxF, ?_⟩
  refine mul_left_cancel₀ (mul_ne_zero hf0 hCc) ?_
  calc f * HahnSeries.C c * (f⁻¹ * coeffMap A.subtype x)
      = f * f⁻¹ * (HahnSeries.C c * coeffMap A.subtype x) := by ring
    _ = f * coeffMap A.subtype y := by rw [mul_inv_cancel₀ hf0, one_mul, hf]
    _ = f * (HahnSeries.C c * HahnSeries.C c⁻¹) * coeffMap A.subtype y := by
        rw [← map_mul, mul_inv_cancel₀ hc, map_one, mul_one]
    _ = f * HahnSeries.C c * (HahnSeries.C c⁻¹ * coeffMap A.subtype y) := by ring

theorem isFrac_add_of_mul (hR : Rescales A F₀) {f g : LaurentSeries L} {c : L} {a : A}
    {x y x' y' : LaurentSeries A}
    (hy : coeffMap (IsLocalRing.residue A) y ≠ 0) (hy' : coeffMap (IsLocalRing.residue A) y' ≠ 0)
    (hxF : coeffMap A.subtype x ∈ F₀) (hyF : coeffMap A.subtype y ∈ F₀)
    (hxF' : coeffMap A.subtype x' ∈ F₀) (hyF' : coeffMap A.subtype y' ∈ F₀)
    (hf : f * coeffMap A.subtype y = HahnSeries.C c * coeffMap A.subtype x)
    (hg : g * coeffMap A.subtype y' = HahnSeries.C (c * a) * coeffMap A.subtype x') :
    IsFrac A F₀ (f + g) := by

  set w : LaurentSeries A := x * y' + HahnSeries.C a * x' * y with hw_def
  have hwF : coeffMap A.subtype w ∈ F₀ := by
    rw [hw_def, map_add, map_mul, map_mul, map_mul, coeffMap_subtype_C]
    exact add_mem (mul_mem hxF hyF') (mul_mem (mul_mem (C_mem L F₀ _) hxF') hyF)
  have hsum : (f + g) * coeffMap A.subtype (y * y') = HahnSeries.C c * coeffMap A.subtype w := by
    simp only [hw_def, map_add, map_mul, coeffMap_subtype_C]
    calc (f + g) * (coeffMap A.subtype y * coeffMap A.subtype y')
        = (f * coeffMap A.subtype y) * coeffMap A.subtype y'
            + (g * coeffMap A.subtype y') * coeffMap A.subtype y := by ring
      _ = HahnSeries.C c * coeffMap A.subtype x * coeffMap A.subtype y'
            + HahnSeries.C c * HahnSeries.C (a : L) * coeffMap A.subtype x' * coeffMap A.subtype y := by
          rw [hf, hg, map_mul]
      _ = HahnSeries.C c * (coeffMap A.subtype x * coeffMap A.subtype y'
            + HahnSeries.C (a : L) * coeffMap A.subtype x' * coeffMap A.subtype y) := by ring
  rcases eq_or_ne w 0 with hw0 | hw0
  ·
    have hzero : f + g = 0 := by
      rw [hw0, map_zero, mul_zero] at hsum
      exact (mul_eq_zero.mp hsum).resolve_right
        (coeffMap_subtype_ne_zero A (residue_mul_ne_zero A hy hy'))
    rw [hzero]
    exact isFrac_zero
  · obtain ⟨c₁, w₁, hc₁, hw₁, hresc⟩ := hR w hwF hw0
    refine ⟨c / c₁, w₁, y * y', hw₁, residue_mul_ne_zero A hy hy', ?_, ?_, ?_⟩
    · rw [← hresc]
      exact mul_mem (C_mem L F₀ _) hwF
    · rw [map_mul]; exact mul_mem hyF hyF'
    · rw [hsum, ← hresc, ← mul_assoc, ← map_mul, div_mul_cancel₀ c hc₁]

theorem isFrac_add (hR : Rescales A F₀) {f g : LaurentSeries L} (hf : IsFrac A F₀ f)
    (hg : IsFrac A F₀ g) : IsFrac A F₀ (f + g) := by
  obtain ⟨c, x, y, hx, hy, hxF, hyF, hf⟩ := hf
  obtain ⟨c', x', y', hx', hy', hxF', hyF', hg⟩ := hg
  rcases eq_or_ne c 0 with rfl | hc
  · rw [IsFrac.eq_zero_of_const_eq_zero hy hf, zero_add]
    exact ⟨c', x', y', hx', hy', hxF', hyF', hg⟩
  rcases eq_or_ne c' 0 with rfl | hc'
  · rw [IsFrac.eq_zero_of_const_eq_zero hy' hg, add_zero]
    exact ⟨c, x, y, hx, hy, hxF, hyF, hf⟩

  rcases A.mem_or_inv_mem (c' / c) with hmem | hmem
  · have hc'eq : c' = c * (⟨c' / c, hmem⟩ : A) := by
      show c' = c * (c' / c)
      rw [mul_div_cancel₀ c' hc]
    rw [hc'eq] at hg
    exact isFrac_add_of_mul hR hy hy' hxF hyF hxF' hyF' hf hg
  · have hceq : c = c' * (⟨(c' / c)⁻¹, hmem⟩ : A) := by
      show c = c' * (c' / c)⁻¹
      rw [inv_div, mul_div_cancel₀ c hc']
    rw [hceq] at hf
    rw [add_comm]
    exact isFrac_add_of_mul hR hy' hy hxF' hyF' hxF hyF hg hf

theorem isFrac_of_mem_closure (hR : Rescales A F₀) {S : Set (LaurentSeries L)}
    (hS : ∀ s ∈ S, IsFrac A F₀ s) {f : LaurentSeries L}
    (hf : f ∈ Subfield.closure (Set.range (algebraMap L (LaurentSeries L)) ∪ S)) : IsFrac A F₀ f := by
  induction hf using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hyS
      · rw [algebraMap_eq_C]
        exact isFrac_C a
      · exact hS y hyS
  | one => exact isFrac_one
  | add x y _ _ hx hy => exact isFrac_add hR hx hy
  | neg x _ hx => exact isFrac_neg hx
  | inv x _ hx => exact isFrac_inv hx
  | mul x y _ _ hx hy => exact isFrac_mul hx hy

end Frac

section Read

variable {L : Type*} [Field L] (A : ValuationSubring L) (F₀ : IntermediateField L (LaurentSeries L))

theorem mem_iff_const_mem (V : ValuationSubring F₀)
    (hVconst : ∀ c : L, algebraMap L F₀ c ∈ V ↔ c ∈ A)
    (hVunit : ∀ (x : LaurentSeries A) (hx : coeffMap A.subtype x ∈ F₀),
      coeffMap (IsLocalRing.residue A) x ≠ 0 →
        (⟨coeffMap A.subtype x, hx⟩ : F₀) ∈ V ∧ (⟨coeffMap A.subtype x, hx⟩ : F₀)⁻¹ ∈ V)
    (f : F₀) {c : L} {x y : LaurentSeries A}
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0) (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (hxF : coeffMap A.subtype x ∈ F₀) (hyF : coeffMap A.subtype y ∈ F₀)
    (hf : (f : LaurentSeries L) * coeffMap A.subtype y = HahnSeries.C c * coeffMap A.subtype x) :
    f ∈ V ↔ c ∈ A := by
  set X : F₀ := ⟨coeffMap A.subtype x, hxF⟩ with hX
  set Y : F₀ := ⟨coeffMap A.subtype y, hyF⟩ with hY
  have hX0 : X ≠ 0 := fun h => coeffMap_subtype_ne_zero A hx (congrArg Subtype.val h)
  have hY0 : Y ≠ 0 := fun h => coeffMap_subtype_ne_zero A hy (congrArg Subtype.val h)
  have hfXY : f * Y = algebraMap L F₀ c * X := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, coe_algebraMap_eq_C]
    exact hf
  obtain ⟨hXV, hXinv⟩ := hVunit x hxF hx
  obtain ⟨hYV, hYinv⟩ := hVunit y hyF hy
  rw [← hVconst c]
  constructor
  · intro hfV
    have h : algebraMap L F₀ c = f * Y * X⁻¹ := by
      rw [hfXY, mul_inv_cancel_right₀ hX0]
    rw [h]
    exact mul_mem (mul_mem hfV hYV) hXinv
  · intro hcV
    have h : f = algebraMap L F₀ c * X * Y⁻¹ := by
      rw [← hfXY, mul_inv_cancel_right₀ hY0]
    rw [h]
    exact mul_mem (mul_mem hcV hXV) hYinv

theorem gauss_iff_const_mem (f : LaurentSeries L) {c : L} (hc : c ≠ 0) {x y : LaurentSeries A}
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0) (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (hf : f * coeffMap A.subtype y = HahnSeries.C c * coeffMap A.subtype x) :
    (∃ x' y' : LaurentSeries A, coeffMap (IsLocalRing.residue A) y' ≠ 0 ∧
        f * coeffMap A.subtype y' = coeffMap A.subtype x') ↔ c ∈ A := by
  constructor
  · rintro ⟨x', y', hy', hf'⟩
    by_contra hcA

    have hnu : c⁻¹ ∈ A.nonunits := (ValuationSubring.inv_mem_nonunits_iff A).mpr (Or.inr hcA)
    obtain ⟨hcinv, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hnu
    have hres : IsLocalRing.residue A ⟨c⁻¹, hcinv⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmax

    have hkey : coeffMap A.subtype (x * y') = coeffMap A.subtype (HahnSeries.C ⟨c⁻¹, hcinv⟩ * x' * y) := by
      rw [map_mul, map_mul, map_mul, coeffMap_subtype_C]
      have h1 : HahnSeries.C c * (coeffMap A.subtype x * coeffMap A.subtype y') =
          coeffMap A.subtype x' * coeffMap A.subtype y := by
        calc HahnSeries.C c * (coeffMap A.subtype x * coeffMap A.subtype y')
            = (HahnSeries.C c * coeffMap A.subtype x) * coeffMap A.subtype y' := by ring
          _ = f * coeffMap A.subtype y * coeffMap A.subtype y' := by rw [hf]
          _ = (f * coeffMap A.subtype y') * coeffMap A.subtype y := by ring
          _ = coeffMap A.subtype x' * coeffMap A.subtype y := by rw [hf']
      calc coeffMap A.subtype x * coeffMap A.subtype y'
          = HahnSeries.C (c⁻¹ * c) * (coeffMap A.subtype x * coeffMap A.subtype y') := by
            rw [inv_mul_cancel₀ hc, map_one, one_mul]
        _ = HahnSeries.C (c⁻¹ : L) * (HahnSeries.C c * (coeffMap A.subtype x * coeffMap A.subtype y')) := by
            rw [map_mul, mul_assoc]
        _ = HahnSeries.C (c⁻¹ : L) * coeffMap A.subtype x' * coeffMap A.subtype y := by
            rw [h1, mul_assoc]
    have hkey' := congrArg (coeffMap (IsLocalRing.residue A)) (coeffMap_subtype_injective A hkey)
    rw [map_mul, map_mul, map_mul, coeffMap_C, hres, map_zero, zero_mul, zero_mul] at hkey'
    exact mul_ne_zero hx hy' hkey'
  · intro hcA
    refine ⟨HahnSeries.C ⟨c, hcA⟩ * x, y, hy, ?_⟩
    rw [map_mul, coeffMap_subtype_C]
    exact hf

end Read

section Modular

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (M' : ℕ)

theorem coeffEmb_qExpand (N : ℕ) [NeZero N] (x : LaurentSeries ℚ) :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N x) = qExpand (AlgebraicClosure ℚ) N (coeffEmb (AlgebraicClosure ℚ) x) :=
  coeffMap_qExpand _ N x

theorem coeffEmb_jq_eq : coeffEmb (AlgebraicClosure ℚ) jq = coeffMap A.subtype (jqModC A) := by
  show (jq).map (algebraMap ℚ (AlgebraicClosure ℚ)) = (jqModC A).map A.subtype
  rw [← jqModC_rat, map_jqModC, map_jqModC]

theorem coeffMap_residue_jqModC_ne_zero : coeffMap (IsLocalRing.residue A) (jqModC A) ≠ 0 := by
  have h : coeffMap (IsLocalRing.residue A) (jqModC A) = jqModC (ResidueField A) := map_jqModC _
  rw [h]
  intro h0
  have h1 := congrArg (fun z : LaurentSeries (ResidueField A) => z.coeff (0 + (-1))) h0
  simp only [jqModC, HahnSeries.coeff_single_mul_add, one_mul, HahnSeries.coeff_zero] at h1
  rw [show ((0 : ℤ)) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one] at h1
  exact one_ne_zero h1

theorem isFrac_coeffEmb_divisorExpansions {s : LaurentSeries ℚ} (hs : s ∈ divisorExpansions M') :
    IsFrac A (modularFunctionFieldBar M') (coeffEmb (AlgebraicClosure ℚ) s) := by
  obtain ⟨d, hd, hdM, rfl⟩ := hs
  refine ⟨1, qExpand A d (jqModC A), 1, ?_, by rw [map_one]; exact one_ne_zero, ?_,
    by rw [map_one]; exact one_mem _, ?_⟩
  · rw [coeffMap_qExpand]
    intro h0
    exact coeffMap_residue_jqModC_ne_zero A
      (qExpand_injective (R := ResidueField A) d (by rw [h0, map_zero]))
  · rw [coeffMap_qExpand, ← coeffEmb_jq_eq, ← coeffEmb_qExpand]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full M' hdM)
  · rw [map_one, mul_one, map_one, one_mul, coeffMap_qExpand, ← coeffEmb_jq_eq, ← coeffEmb_qExpand]

theorem isFrac_coeffEmb_of_mem (hR : Rescales A (modularFunctionFieldBar M')) {g : LaurentSeries ℚ}
    (hg : g ∈ modularFunctionFieldFull M') :
    IsFrac A (modularFunctionFieldBar M') (coeffEmb (AlgebraicClosure ℚ) g) := by
  have hg' : g ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions M') := by
    rw [← IntermediateField.adjoin_toSubfield]
    exact hg
  clear hg
  induction hg' using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hyS
      · rw [algebraMap_eq_C, coeffEmb, coeffMap_C]
        exact isFrac_C _
      · exact isFrac_coeffEmb_divisorExpansions A M' hyS
  | one => rw [map_one]; exact isFrac_one
  | add x y _ _ hx hy => rw [map_add]; exact isFrac_add hR hx hy
  | neg x _ hx => rw [map_neg]; exact isFrac_neg hx
  | inv x _ hx => rw [map_inv₀]; exact isFrac_inv hx
  | mul x y _ _ hx hy => rw [map_mul]; exact isFrac_mul hx hy

theorem isFrac_of_mem_modularFunctionFieldBar (hR : Rescales A (modularFunctionFieldBar M'))
    {f : LaurentSeries (AlgebraicClosure ℚ)} (hf : f ∈ modularFunctionFieldBar M') :
    IsFrac A (modularFunctionFieldBar M') f := by
  rw [mem_laurentBaseChange_iff] at hf
  refine isFrac_of_mem_closure hR ?_ hf
  rintro s ⟨g, hg, rfl⟩
  exact isFrac_coeffEmb_of_mem A M' hR hg

theorem rescales_modularFunctionFieldBar [NeZero M'] (q : ℕ) [Fact q.Prime] (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldBar M' ≤ FullLevel.fieldBar q M') :
    Rescales A (modularFunctionFieldBar M') := by
  intro w hw hw0
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  set g : ↥(FullLevel.fieldBar q M') := ⟨coeffMap A.subtype w, hle hw⟩ with hg_def
  have hg0 : g ≠ 0 := by
    intro h
    apply hw0
    apply coeffMap_subtype_injective A
    rw [map_zero]
    exact congrArg Subtype.val h
  have h₀ : ((((1 : AlgebraicClosure ℚ) • g : ↥(FullLevel.fieldBar q M'))) :
      LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype w := by
    rw [coe_smul_eq_C_mul, map_one, one_mul]
  obtain ⟨c, hc, y, hy, hyres⟩ :=
    ModularCurve.exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar
      q (q ^ 2 * M') (FullLevel.levelH q M') A hA g hg0 1 one_ne_zero w h₀
  refine ⟨c, y, hc, hyres, ?_⟩
  rw [← hy, coe_smul_eq_C_mul]

end Modular

end S3bEmbFrac

end ModularCurve

end

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.levelH FullLevel.fieldBar xHFunctionFieldC qExpFunctionFieldC intFormRatiosC_subset modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand constantCoeff_jNum jq jq_mem divisorExpansions modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jqModC jqNModC jqModC_rat map_jqModC modularFunctionFieldC jqModC_mem IsSupersingularPlace ssPlaces jGeomGen transcendental_jqModC exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull qTwist qTwist_coeff qTwist_one_apply exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable finiteDimensional_adjoin_jqModC qExpand_jqModC_mem_intFormRatiosC_gammaH"
p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_qExpand"

namespace S3bEmbAux

p2m_open "HahnSeries IntermediateField AlgebraicCurve~isAlgebraic_adjoin_of_transcendental IsLocalRing"

theorem coeffMap_qTwist {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : Rˣ)
    (x : LaurentSeries R) :
    coeffMap f (qTwist u x) = qTwist (Units.map (f : R →* S) u) (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff, qTwist_coeff, qTwist_coeff, coeffMap_coeff, map_mul, ← map_zpow, Units.coe_map]
  rfl

theorem residue_eq_one_of_pow_char_eq_one {A : Type*} [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField A) p] (u : A) (hu : u ^ p = 1) : residue A u = 1 := by
  have h1 : (residue A u) ^ p = 1 := by rw [← map_pow, hu, map_one]
  have h2 : (residue A u - 1) ^ p = 0 := by
    rw [sub_pow_char (residue A u) 1, h1, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp h2)

theorem isAlgebraic_of_forall_mem {κ E : Type*} [Field κ] [Field E] [Algebra κ E]
    (K₁ : IntermediateField κ E) (S : Subfield E) (h : ∀ x : E, x ∈ K₁ → x ∈ S)
    [Algebra.IsAlgebraic K₁ E] : Algebra.IsAlgebraic S E := by
  let φ : K₁ →+* S :=
    { toFun := fun x => ⟨(x : E), h x x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra K₁ S := φ.toAlgebra
  haveI : IsScalarTower K₁ S E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine Algebra.IsAlgebraic.extendScalars (R := K₁) (S := S) (A := E) ?_
  intro a b hab
  exact Subtype.ext (congrArg Subtype.val hab :)

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem isAlgebraic_adjoin_of_transcendental {κ : Type*} {E : Type} [Field κ] [Field E] [Algebra κ E]
    (t : E) [FiniteDimensional ↥(IntermediateField.adjoin κ ({t} : Set E)) E]
    (y : E) (hy : Transcendental κ y) :
    Algebra.IsAlgebraic ↥(IntermediateField.adjoin κ ({y} : Set E)) E := by
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin κ ({t} : Set E)) E :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic ↥(Algebra.adjoin κ ({t} : Set E)) E :=
    Algebra.IsAlgebraic.trans (R := ↥(Algebra.adjoin κ ({t} : Set E)))
      (S := ↥(IntermediateField.adjoin κ ({t} : Set E))) (A := E)
  have h1 : Algebra.trdeg κ E ≤ 1 := by
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk κ ({t} : Set E)
    rwa [Cardinal.mk_singleton] at h
  have hind : AlgebraicIndependent κ ![y] := algebraicIndependent_iff_transcendental.mpr hy
  have hb : IsTranscendenceBasis κ ![y] :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [Cardinal.mk_fin, Nat.cast_one]; exact h1)
  have halg := hb.isAlgebraic_field
  have hr : Set.range ![y] = ({y} : Set E) := by
    ext z
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      rfl
    · rintro rfl
      exact ⟨0, rfl⟩
  rw [hr] at halg
  exact halg

def toAlgHomOfC {κ : Type*} [Field κ] (T : LaurentSeries κ →+* LaurentSeries κ)
    (hT : ∀ r : κ, T (algebraMap κ (LaurentSeries κ) r) = algebraMap κ (LaurentSeries κ) r) :
    LaurentSeries κ →ₐ[κ] LaurentSeries κ :=
  { toRingHom := T, commutes' := hT }

@[scoped simp] theorem toAlgHomOfC_apply {κ : Type*} [Field κ] (T : LaurentSeries κ →+* LaurentSeries κ)
    (hT : ∀ r : κ, T (algebraMap κ (LaurentSeries κ) r) = algebraMap κ (LaurentSeries κ) r) (x : LaurentSeries κ) :
    toAlgHomOfC T hT x = T x := rfl

end S3bEmbAux
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve.S3bEmbAux"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve.S3bEmbAux P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve.S3bEmbAux P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.levelH FullLevel.fieldBar xHFunctionFieldC qExpFunctionFieldC intFormRatiosC_subset modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand constantCoeff_jNum jq jq_mem divisorExpansions modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jqModC jqNModC jqModC_rat map_jqModC modularFunctionFieldC jqModC_mem IsSupersingularPlace ssPlaces jGeomGen transcendental_jqModC exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull qTwist qTwist_coeff qTwist_one_apply exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable finiteDimensional_adjoin_jqModC qExpand_jqModC_mem_intFormRatiosC_gammaH"
p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_qExpand"

namespace S3bEmbAux

p2m_open "HahnSeries IntermediateField AlgebraicCurve~isAlgebraic_adjoin_of_transcendental IsLocalRing ModularCurve.FullLevel CongruenceSubgroup"
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem reading_package (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (ζ : Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    ∃ (TA : LaurentSeries ↥A →+* LaurentSeries ↥A)
      (Tκ : LaurentSeries (ResidueField ↥A) →+* LaurentSeries (ResidueField ↥A)),
      (Tκ = RingHom.id _ ∨ Tκ = qExpand (ResidueField ↥A) (q ^ 2)) ∧
      (∀ (z : LaurentSeries ↥A), coeffMap A.subtype z ∈ modularFunctionFieldBar M' →
        ∀ (x : ↥(fieldBar q M')), (x : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype z →
          ((levelAutBar q M' ζ γ x : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffMap A.subtype (TA z)) ∧
      (∀ z : LaurentSeries ↥A, coeffMap (residue ↥A) (TA z) = Tκ (coeffMap (residue ↥A) z)) ∧
      (∀ r : ResidueField ↥A, Tκ (algebraMap _ _ r) = algebraMap _ _ r) ∧
      Function.Injective Tκ := by
  classical
  have hmem : ∀ (z : LaurentSeries ↥A), coeffMap A.subtype z ∈ modularFunctionFieldBar M' →
      coeffMap A.subtype z ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) := by
    intro z hz
    rw [qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact hz
  by_cases ha : (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  ·
    refine ⟨qExpand ↥A (q ^ 2), qExpand (ResidueField ↥A) (q ^ 2), Or.inr rfl, ?_, ?_, ?_, qExpand_injective _⟩
    · intro z hz x hx
      rw [S3bEmbFrac.coeffMap_qExpand]
      exact coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0 q M' hqM' ζ γ hγ ha
        (coeffMap A.subtype z) (hmem z hz) x hx
    · intro z
      exact S3bEmbFrac.coeffMap_qExpand _ _ z
    · intro r
      rw [S3bEmbFrac.algebraMap_eq_C, qExpand_C]
  ·
    have hqne : q ≠ 0 := (Fact.out : q.Prime).ne_zero
    have hζq : ζ.val ^ q = 1 := (Idx.isPrimitiveRoot ζ).pow_eq_one
    have hζinv : ζ.val ^ (q - 1) = ζ.val⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul hqne, hζq])
    have hζA : ζ.val ∈ A := by
      rcases ValuationSubring.mem_or_inv_mem A ζ.val with h | h
      · exact h
      · have : ζ.val = (ζ.val⁻¹) ^ (q - 1) := by rw [inv_pow, hζinv, inv_inv]
        rw [this]
        exact pow_mem h _
    let uA : (↥A)ˣ := Units.mkOfMulEqOne (⟨ζ.val, hζA⟩ : ↥A) ((⟨ζ.val, hζA⟩ : ↥A) ^ (q - 1))
      (Subtype.ext (by
        rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one]
        exact (mul_pow_sub_one hqne ζ.val).trans hζq))
    have huA : ((uA : ↥A) : AlgebraicClosure ℚ) = ζ.val := rfl
    have huA' : ((Units.map (A.subtype : ↥A →* AlgebraicClosure ℚ) uA : (AlgebraicClosure ℚ)ˣ) :
        AlgebraicClosure ℚ) = ζ.val := by
      rw [Units.coe_map]; exact huA
    obtain ⟨k, hk⟩ := exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0
      q M' hqM' ζ γ hγ ha (Units.map (A.subtype : ↥A →* AlgebraicClosure ℚ) uA) huA'

    have hAq : ((q : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      have : (((q : ℕ) : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by push_cast; rfl
      rw [this]; exact hA
    haveI : CharP (ResidueField ↥A) q := IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal (↥A) q hAq
    have hres1 : residue ↥A (uA : ↥A) = 1 := by
      apply residue_eq_one_of_pow_char_eq_one q
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact hζq
    have hunit : Units.map (residue ↥A : ↥A →* ResidueField ↥A) uA = 1 := by
      apply Units.ext
      rw [Units.coe_map, Units.val_one]
      exact hres1
    refine ⟨qTwist (uA ^ k), RingHom.id _, Or.inl rfl, ?_, ?_, fun r => rfl, fun a b h => h⟩
    · intro z hz x hx
      rw [hk (coeffMap A.subtype z) (hmem z hz) x hx, coeffMap_qTwist, map_zpow]
    · intro z
      rw [coeffMap_qTwist, map_zpow, hunit, one_zpow, qTwist_one_apply, RingHom.id_apply]

end S3bEmbAux
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve.S3bEmbAux P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve.S3bEmbAux P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve.S3bEmbAux P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.levelH FullLevel.fieldBar xHFunctionFieldC qExpFunctionFieldC intFormRatiosC_subset modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_C qExpand_injective qExpand_one_apply qExpand_qExpand constantCoeff_jNum jq jq_mem divisorExpansions modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jqModC jqNModC jqModC_rat map_jqModC modularFunctionFieldC jqModC_mem IsSupersingularPlace ssPlaces jGeomGen transcendental_jqModC exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull qTwist qTwist_coeff qTwist_one_apply exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable finiteDimensional_adjoin_jqModC qExpand_jqModC_mem_intFormRatiosC_gammaH"
p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_qExpand"

namespace S3bReadAux

p2m_open "HahnSeries IntermediateField AlgebraicCurve~isAlgebraic_adjoin_of_transcendental IsLocalRing ModularCurve.FullLevel CongruenceSubgroup"
open scoped MatrixGroups

theorem residue_algebraMap_place {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    IsLocalRing.residue ↥v.toValuationSubring (algebraMap K ↥v.toValuationSubring c) =
      algebraMap K v.ResidueField c :=
  Ideal.Quotient.mk_algebraMap K _ c

theorem mem_and_evalAt_eq_of_sub_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {x : F} {c : K} (h : x - algebraMap K F c ∈ v.toValuationSubring.nonunits) :
    x ∈ v.toValuationSubring ∧ v.evalAt x = c := by
  have hmem : x - algebraMap K F c ∈ v.toValuationSubring := v.toValuationSubring.nonunits_subset h
  have hx : x ∈ v.toValuationSubring := by
    have := add_mem hmem (v.algebraMap_mem' c)
    rwa [sub_add_cancel] at this
  refine ⟨hx, ?_⟩
  rw [v.evalAt_of_mem hx]
  have hmax : (⟨x - algebraMap K F c, hmem⟩ : ↥v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    ValuationSubring.coe_mem_nonunits_iff.mp h
  have h1 : (⟨x, hx⟩ : ↥v.toValuationSubring) =
      ⟨x - algebraMap K F c, hmem⟩ + algebraMap K ↥v.toValuationSubring c := by
    apply Subtype.ext
    rw [AddMemClass.coe_add, Place.coe_algebraMap, sub_add_cancel]
  rw [h1, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, zero_add, residue_algebraMap_place,
    v.residueInv_algebraMap]

theorem sub_algebraMap_evalAt_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {x : F} (hx : x ∈ v.toValuationSubring) :
    x - algebraMap K F (v.evalAt x) ∈ v.toValuationSubring.nonunits := by
  have hmem : x - algebraMap K F (v.evalAt x) ∈ v.toValuationSubring := sub_mem hx (v.algebraMap_mem' _)
  have h1 : (⟨_, hmem⟩ : ↥v.toValuationSubring) = ⟨x, hx⟩ - algebraMap K ↥v.toValuationSubring (v.evalAt x) := by
    apply Subtype.ext
    rw [AddSubgroupClass.coe_sub, Place.coe_algebraMap]
  have : ((⟨_, hmem⟩ : ↥v.toValuationSubring) : F) ∈ v.toValuationSubring.nonunits := by
    rw [ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, h1, map_sub,
      residue_algebraMap_place, v.algebraMap_evalAt hv hx, sub_self]
  exact this

theorem const_mem_of_mem_integers (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers)
    {c : AlgebraicClosure ℚ} {x y : LaurentSeries ↥A}
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0) (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (hxF : coeffMap A.subtype x ∈ modularFunctionFieldBar M') (hyF : coeffMap A.subtype y ∈ modularFunctionFieldBar M')
    (hfrac : (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = HahnSeries.C c * coeffMap A.subtype x) :
    c ∈ A := by
  classical
  rcases eq_or_ne c 0 with rfl | hc
  · exact zero_mem A
  · refine (S3bEmbFrac.mem_iff_const_mem A (modularFunctionFieldBar M') R₀.integers
      R₀.algebraMap_mem_iff ?_ f hx hy hxF hyF hfrac).mp hf
    intro z hz hzred
    obtain ⟨hzV, hzres⟩ := hR₀ z hz
    have hres_ne : R₀.residue ⟨_, hzV⟩ ≠ 0 := by
      intro h0
      apply hzred
      rw [← hzres, h0]
      rfl
    have hunit : IsUnit (⟨_, hzV⟩ : R₀.integers) := by
      rw [← IsLocalRing.notMem_maximalIdeal, ← R₀.ker_residue, RingHom.mem_ker]
      exact hres_ne
    have hval : R₀.integers.valuation (⟨coeffMap A.subtype z, hz⟩ : ↥(modularFunctionFieldBar M')) = 1 :=
      (ValuationSubring.valuation_eq_one_iff R₀.integers ⟨_, hzV⟩).mp hunit
    refine ⟨hzV, ValuationSubring.mem_of_valuation_le_one _ _ ?_⟩
    rw [map_inv₀, hval, inv_one]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem levelAut_inclusion_mem_of_mem_integers (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')
    (O : ValuationSubring ↥(fieldBar q M'))
    (hO : ∀ f : ↥(fieldBar q M'), f ∈ O ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers) :
    levelAutBar q M' ζ γ (IntermediateField.inclusion hle f) ∈ O := by
  classical
  obtain ⟨TA, Tκ, -, hTexp, hTres, -, hTinj⟩ := S3bEmbAux.reading_package q M' hqM' A hA ζ γ hγ
  have hResc := S3bEmbFrac.rescales_modularFunctionFieldBar A M' q hA hle
  obtain ⟨c, x, y, hx, hy, hxF, hyF, hfrac⟩ :=
    S3bEmbFrac.isFrac_of_mem_modularFunctionFieldBar A M' hResc f.2
  have hcA : c ∈ A := const_mem_of_mem_integers M' A R₀ hR₀ f hf hx hy hxF hyF hfrac
  have hX := hTexp x hxF (IntermediateField.inclusion hle ⟨_, hxF⟩) (IntermediateField.coe_inclusion hle _)
  have hY := hTexp y hyF (IntermediateField.inclusion hle ⟨_, hyF⟩) (IntermediateField.coe_inclusion hle _)
  have h1 : IntermediateField.inclusion hle f *
      IntermediateField.inclusion hle (⟨coeffMap A.subtype y, hyF⟩ : ↥(modularFunctionFieldBar M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c *
        IntermediateField.inclusion hle (⟨coeffMap A.subtype x, hxF⟩ : ↥(modularFunctionFieldBar M')) := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, IntermediateField.coe_inclusion, IntermediateField.coe_inclusion,
      IntermediateField.coe_inclusion, S3bEmbFrac.coe_algebraMap_eq_C]
    exact hfrac
  have h2 := congrArg (levelAutBar q M' ζ γ) h1
  rw [map_mul, map_mul, AlgEquiv.commutes] at h2
  have h3 := congrArg Subtype.val h2
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul, hX, hY, S3bEmbFrac.coe_algebraMap_eq_C] at h3
  rw [hO]
  refine ⟨HahnSeries.C (⟨c, hcA⟩ : ↥A) * TA x, TA y, ?_, ?_⟩
  · rw [hTres]
    intro h0
    exact hy (hTinj (by rw [h0, map_zero]))
  · rw [map_mul, S3bEmbFrac.coeffMap_subtype_C]
    exact h3

theorem exists_algHom_of_reading (κ : Type*) [Field κ] (q M' : ℕ) [Fact q.Prime] [NeZero M']
    (τ : LaurentSeries κ →+* LaurentSeries κ) (hτ : τ = RingHom.id _ ∨ τ = qExpand κ (q ^ 2)) :
    ∃ φ : ↥(modularFunctionFieldC κ M') →ₐ[κ] ↥(xHFunctionFieldC κ (q ^ 2 * M') (levelH q M')),
      ∀ g : ↥(modularFunctionFieldC κ M'),
        ((φ g : ↥(xHFunctionFieldC κ (q ^ 2 * M') (levelH q M'))) : LaurentSeries κ) = τ (g : LaurentSeries κ) := by
  classical
  haveI hq2 : NeZero (q ^ 2) := ⟨pow_ne_zero _ (Fact.out : q.Prime).ne_zero⟩
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne M')⟩
  have hmem : ∀ (d : ℕ) [NeZero d], d ∣ q ^ 2 * M' →
      qExpand κ d (jqModC κ) ∈ xHFunctionFieldC κ (q ^ 2 * M') (levelH q M') :=
    fun d _ hd => intFormRatiosC_subset κ _ (qExpand_jqModC_mem_intFormRatiosC_gammaH κ (q ^ 2 * M') d hd (levelH q M'))
  obtain ⟨T, hT, hgen1, hgen2⟩ : ∃ T : LaurentSeries κ →ₐ[κ] LaurentSeries κ, (∀ x, T x = τ x) ∧
      T (jqModC κ) ∈ xHFunctionFieldC κ (q ^ 2 * M') (levelH q M') ∧
      T (jqNModC κ M') ∈ xHFunctionFieldC κ (q ^ 2 * M') (levelH q M') := by
    rcases hτ with rfl | rfl
    · refine ⟨AlgHom.id κ _, fun _ => rfl, ?_, ?_⟩
      · have h := hmem 1 (one_dvd _)
        rwa [qExpand_one_apply] at h
      · exact hmem M' (Dvd.intro_left _ rfl)
    · refine ⟨S3bEmbAux.toAlgHomOfC (qExpand κ (q ^ 2))
        (fun r => by rw [S3bEmbFrac.algebraMap_eq_C, qExpand_C]), fun _ => rfl, ?_, ?_⟩
      · exact hmem (q ^ 2) (Dvd.intro _ rfl)
      · show qExpand κ (q ^ 2) (qExpand κ M' (jqModC κ)) ∈ _
        rw [qExpand_qExpand]
        exact hmem (q ^ 2 * M') dvd_rfl
  have hsub : ∀ g : ↥(modularFunctionFieldC κ M'),
      T (g : LaurentSeries κ) ∈ xHFunctionFieldC κ (q ^ 2 * M') (levelH q M') := by
    intro g
    have hle : (modularFunctionFieldC κ M').map T ≤ xHFunctionFieldC κ (q ^ 2 * M') (levelH q M') := by
      rw [modularFunctionFieldC, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, hx, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hgen1
      · exact hgen2
    have hg : T (g : LaurentSeries κ) ∈ ((modularFunctionFieldC κ M').map T : Set (LaurentSeries κ)) := by
      rw [IntermediateField.coe_map]
      exact Set.mem_image_of_mem _ g.2
    exact hle hg
  refine ⟨{ toFun := fun g => ⟨T g, hsub g⟩
            map_one' := Subtype.ext (by simp)
            map_mul' := fun a b => Subtype.ext (by simp)
            map_zero' := Subtype.ext (by simp)
            map_add' := fun a b => Subtype.ext (by simp)
            commutes' := fun r => Subtype.ext (by
              show T ((algebraMap κ ↥(modularFunctionFieldC κ M') r : ↥(modularFunctionFieldC κ M')) : LaurentSeries κ) =
                ((algebraMap κ ↥(xHFunctionFieldC κ (q ^ 2 * M') (levelH q M')) r : ↥(xHFunctionFieldC κ (q ^ 2 * M') (levelH q M'))) : LaurentSeries κ)
              rw [SubalgebraClass.coe_algebraMap, SubalgebraClass.coe_algebraMap, AlgHom.commutes]) }, fun g => hT g⟩

end S3bReadAux
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve.S3bEmbAux P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve.S3bEmbAux P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve.S3bEmbAux P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve"

p2m_open "AlgebraicCurve~isAlgebraic_adjoin_of_transcendental ModularCurve~coeffMap_qExpand~coeffEmb_qExpand P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three.ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))

    (K₀ : Subfield (AlgebraicClosure ℚ)) [Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ)] (hπK₀ : π ∈ K₀)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
      (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)))
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π)

    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀)

    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)

    [Algebra A₀ ↥F₀]
    (hj₀ : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ))
    [Fact ((⟨_, hjF₀⟩ : ↥F₀) ≠ 0)]
    (s : ↥W) (ℓ : CuspidalType.ProjLine q)
    (ρ : IsLocalRing.ResidueField ↥((OIg ℓ).comap F₀.subtype) →+* ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (τ : LaurentSeries (ResidueField A) →+* LaurentSeries (ResidueField A)) (hτ : τ = RingHom.id _ ∨ τ = qExpand (ResidueField A) (q ^ 2))
    (hρA : ∀ (a : A₀) (ha : ((algebraMap A₀ ↥F₀ a : ↥F₀)) ∈ (OIg ℓ).comap F₀.subtype),
        ρ (IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨algebraMap A₀ ↥F₀ a, ha⟩) =
          algebraMap (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) (IsLocalRing.residue ↥A (ι a)))
    (hρf : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers) (a : A₀)
        (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (hg : (g : ↥F₀) ∈ (OIg ℓ).comap F₀.subtype),
        ((g : ↥F₀) : ↥(fieldBar q M')) =
            (IntermediateField.inclusion hle f : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) →
        ((ρ (IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨(g : ↥F₀), hg⟩) : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
          τ ((R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A))
            - algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue ↥A (ι a)))
    (w : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (hwC : ∀ (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (hg : (g : ↥F₀) ∈ (OIg ℓ).comap F₀.subtype),
      ρ (IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨(g : ↥F₀), hg⟩) ∈ w.toValuationSubring)
    (hread : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
          (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A₀, residue A (ι a) =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∀ (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (hg : (g : ↥F₀) ∈ (OIg ℓ).comap F₀.subtype), ((g : ↥F₀) : ↥(fieldBar q M')) =
                (IntermediateField.inclusion hle f : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) →
              ρ (IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨(g : ↥F₀), hg⟩) ∈ w.toValuationSubring.nonunits)
    (g : ↥(modularFunctionFieldC (ResidueField A) M')) (g' : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (hgg' : (g' : LaurentSeries (ResidueField A)) = τ (g : LaurentSeries (ResidueField A))) :
    g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔ g' ∈ w.toValuationSubring := by
  classical
  haveI : NeZero (q ^ 2) := ⟨pow_ne_zero _ (Fact.out : q.Prime).ne_zero⟩
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne M')⟩

  have hAq : ((q : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    have : (((q : ℕ) : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by push_cast; rfl
    rw [this]; exact hA
  haveI : CharP (ResidueField ↥A) q := IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal (↥A) q hAq
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  have hM'κ : ((M' : ℕ) : ResidueField ↥A) ≠ 0 := fun h => hqM' ((CharP.cast_eq_zero_iff (ResidueField ↥A) q M').mp h)
  have hrat : ∀ v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'), v.IsRational := by
    obtain ⟨inst, hst, -, hfin, -⟩ :=
      exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable (ResidueField ↥A) M' hM'κ
    letI := inst
    haveI := hst
    haveI := hfin
    intro v
    exact Place.isRational_of_isAlgClosed v

  have hss : IsSupersingularPlace q M' (ResidueField A)
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) := (hW _).mp s.2
  have hsrat := hss.1
  have hjs : jGeomGen (ResidueField A) M' ∈
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring := hss.2.1.1

  obtain ⟨γ, hγ, -, hOIgℓ⟩ := hIg ℓ
  have hVmem : ∀ x : ↥F₀, x ∈ (OIg ℓ).comap F₀.subtype ↔ (x : ↥(fieldBar q M')) ∈ OIg ℓ :=
    fun x => ValuationSubring.mem_comap
  have hmemℓ : ∀ x : ↥(fieldBar q M'), x ∈ OIg ℓ ↔ levelAutBar q M' ζ γ x ∈ OIg (lineInfty q) := by
    intro x; rw [hOIgℓ]; rfl
  have hconstV : ∀ a : A₀, (algebraMap A₀ ↥F₀ a : ↥F₀) ∈ (OIg ℓ).comap F₀.subtype := by
    intro a
    rw [hVmem, hmemℓ, hj₀, AlgEquiv.commutes, hIg_inf]
    refine ⟨HahnSeries.C (ι a), 1, by rw [map_one]; exact one_ne_zero, ?_⟩
    rw [map_one, mul_one, S3bEmbFrac.coe_algebraMap_eq_C, S3bEmbFrac.coeffMap_subtype_C]

  have hlift : ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
      (hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))),
      ∃ hF : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) g,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀,
        (⟨_, hF⟩ : ↥F₀) ∈ TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) ∧
        (⟨_, hF⟩ : ↥F₀) ∈ (OIg ℓ).comap F₀.subtype := by
    intro g hg hgi hcusp
    have hF : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) g,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀ := by
      rw [hF₀]
      intro n
      rw [IntermediateField.coe_inclusion]
      show (coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) g).coeff n ∈ K₀
      rw [coeffMap_coeff, eq_ratCast]
      exact SubfieldClass.ratCast_mem K₀ _
    refine ⟨hF, ?_, ?_⟩
    · exact inclusion_mem_chartAlgFin_of_mem_integers_of_cuspRegular_descent_of_eq_three q hq3 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ
        OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀
        hjF₀ hj₀ g hg hgi hcusp hF
    · rw [hVmem, hmemℓ]
      exact S3bReadAux.levelAut_inclusion_mem_of_mem_integers q M' hqM' A hA hle R₀ hR₀ ζ γ hγ (OIg (lineInfty q))
        hIg_inf _ hgi

  obtain ⟨φ, hφ⟩ := S3bReadAux.exists_algHom_of_reading (ResidueField ↥A) q M' τ hτ

  have hTread : ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
      (hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')))
      (a : A₀),
      ∃ (gC : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)))
        (hgV : (gC : ↥F₀) ∈ (OIg ℓ).comap F₀.subtype),
        ((gC : ↥F₀) : ↥(fieldBar q M')) =
          (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) g,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) -
            algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) ∧
        ρ (IsLocalRing.residue ↥((OIg ℓ).comap F₀.subtype) ⟨(gC : ↥F₀), hgV⟩) =
          φ (R₀.residue ⟨_, hgi⟩) -
            algebraMap (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))
              (IsLocalRing.residue ↥A (ι a)) := by
    intro g hg hgi hcusp a
    obtain ⟨hF, hC, hVf⟩ := hlift g hg hgi hcusp
    let gC : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) :=
      ⟨(⟨_, hF⟩ : ↥F₀) - algebraMap A₀ ↥F₀ a, sub_mem hC (Subalgebra.algebraMap_mem _ a)⟩
    have hgV : (gC : ↥F₀) ∈ (OIg ℓ).comap F₀.subtype := sub_mem hVf (hconstV a)
    have hgeq : ((gC : ↥F₀) : ↥(fieldBar q M')) =
        (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) g,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) -
          algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) := by
      rw [← hj₀]; rfl
    refine ⟨gC, hgV, hgeq, ?_⟩
    apply Subtype.ext
    rw [hρf _ hgi a gC hgV hgeq]
    show _ = ((φ (R₀.residue ⟨_, hgi⟩) : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) :
        LaurentSeries (ResidueField A)) -
      ((algebraMap (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))
        (IsLocalRing.residue ↥A (ι a)) : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) :
        LaurentSeries (ResidueField A))
    rw [hφ, S3bEmbFrac.coe_algebraMap_eq_C, S3bEmbFrac.algebraMap_eq_C]

  let T : Set ↥(modularFunctionFieldC (ResidueField A) M') :=
    {t | t ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ∧
      ∃ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) ∧
        t = R₀.residue ⟨_, hgi⟩}

  have hjA : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [← S3bEmbFrac.coeffEmb_jq_eq]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
  obtain ⟨hjint, hjres⟩ := hR₀ (jqModC ↥A) hjA
  have hjeq : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
      ↥(modularFunctionFieldBar M')) = ⟨coeffMap A.subtype (jqModC ↥A), hjA⟩ := Subtype.ext (S3bEmbFrac.coeffEmb_jq_eq A)
  have hjint' : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
      ↥(modularFunctionFieldBar M')) ∈ R₀.integers := by
    rw [hjeq]; exact hjint
  have hjbar : R₀.residue ⟨_, hjint'⟩ = jGeomGen (ResidueField A) M' := by
    apply Subtype.ext
    have : (⟨_, hjint'⟩ : ↥R₀.integers) = ⟨_, hjint⟩ := Subtype.ext hjeq
    rw [this, hjres]
    exact map_jqModC _
  have hjT : jGeomGen (ResidueField A) M' ∈ T :=
    ⟨hjs, jq, modularFunctionField_le_full M' (jq_mem M'), hjint', fun P h => h, hjbar.symm⟩

  have hT_T : ∀ t ∈ T, φ t ∈ w.toValuationSubring := by
    rintro t ⟨-, g, hg, hgi, hcusp, rfl⟩
    obtain ⟨gC, hgV, -, hρeq⟩ := hTread g hg hgi hcusp 0
    have h := hwC gC hgV
    rw [hρeq, map_zero, map_zero, map_zero, sub_zero] at h
    exact h

  have hvan : ∀ t ∈ T, ∀ c : ResidueField A,
      t - algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') c ∈
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring.nonunits →
      φ t - algebraMap (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) c ∈
        w.toValuationSubring.nonunits := by
    rintro t ⟨hts, g, hg, hgi, hcusp, rfl⟩ c hc
    obtain ⟨a, ha⟩ := hres c
    have heval := (S3bReadAux.mem_and_evalAt_eq_of_sub_mem_nonunits _ hc).2
    obtain ⟨gC, hgV, hgeq, hρeq⟩ := hTread g hg hgi hcusp a
    have hval : IsLocalRing.residue ↥A (ι a) =
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) := by
      rw [heval]; exact ha
    have h := hread _ hgi hcusp hts a hval gC hgV hgeq
    rw [hρeq] at h
    have hc' : IsLocalRing.residue ↥A (ι a) = c := ha
    rwa [hc'] at h

  have hO : ∃ t ∈ T, ∃ c : ResidueField A,
      t - algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') c ∈
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring.nonunits ∧
      t ≠ algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') c := by
    refine ⟨_, hjT, (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
      (jGeomGen (ResidueField A) M'), S3bReadAux.sub_algebraMap_evalAt_mem_nonunits _ hsrat hjs, ?_⟩
    intro h
    apply transcendental_jqModC (ResidueField ↥A)
    have h' := congrArg Subtype.val h
    rw [SubalgebraClass.coe_algebraMap] at h'
    change jqModC (ResidueField ↥A) = _ at h'
    rw [h']
    exact isAlgebraic_algebraMap _

  have hsep : ∀ s' : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'),
      (∀ t ∈ T, t ∈ s'.toValuationSubring) →
      (∀ t ∈ T, ∀ c : ResidueField A,
        t - algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') c ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring.nonunits →
        t - algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') c ∈ s'.toValuationSubring.nonunits) →
      s' = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) := by
    intro s' hT' hvan'
    by_contra hne
    have hjs' := hT' _ hjT
    obtain ⟨g, hg, hgi, hcusp, hgs, -, hne'⟩ :=
      exists_rational_integral_cuspRegular_evalAt_ne_of_isRational_of_ne q M' hqM' A hA R₀ hR₀
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) s' hsrat (hrat s') hjs hjs' (Ne.symm hne)
    have ht : R₀.residue ⟨_, hgi⟩ ∈ T := ⟨hgs, g, hg, hgi, hcusp, rfl⟩
    have h1 := hvan' _ ht _ (S3bReadAux.sub_algebraMap_evalAt_mem_nonunits _ hsrat hgs)
    exact hne' (S3bReadAux.mem_and_evalAt_eq_of_sub_mem_nonunits _ h1).2.symm

  haveI := finiteDimensional_adjoin_jqModC (N := M') A
  have key := AlgebraicCurve.Place.mem_toValuationSubring_iff_map_mem_of_forall_place_eq_of_testFamily
    ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) M'⟩ : ↥(modularFunctionFieldC (ResidueField A) M')))
    φ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) w T hT_T hvan hO hsep g
  have hg' : g' = φ g := Subtype.ext (by rw [hgg', hφ])
  rw [hg']
  exact key

end S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_of_place_reads_ssPlace_igusaRing_descent_of_eq_three (solution)
