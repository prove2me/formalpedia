-- Prove2me | solution 1 for ModularCurve.DRLevel.range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/176494db-a924-5349-a1f3-dcedc9195317

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_IgusaScheme_exists_ringHom_laurentSeries_pair_chartAlgFin_mul_frobenius_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_chartAlgFin_mul_eq_atkinLehnerInvolutionFull
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_map_le_ker_retraction_iff_mem_of_mem_minimalPrimes_of_not_dvd
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd
import Theorems.Thm_ModularCurve_DRLevel_exists_retraction_chart_comp_zero_eq
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegral_pullback_igusaTo_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id
p2m_attr_erase "instance" "ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableNonsingular instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeRingHom AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero"
p2m_attr_erase "simp" "compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one"
p2m_attr_erase "simp" "TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open scoped TensorProduct
open ModularCurve ModularCurve.IgusaScheme

namespace IgusaFrobRing

variable {p : ℕ} [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)

theorem ringHom_ext_zp {P : Type*} [Semiring P] (f g : ℤp →+* P) : f = g := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp Fact.out
  haveI : IsLocalization.AtPrime ℤp (Ideal.span {(p : ℤ)}) := GaloisRep.isLocalization_ratLocalizedAt Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

def algHomOfRingHom {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤp A] [Algebra ℤp B] (f : A →+* B) :
    A →ₐ[ℤp] B :=
  { f with
    commutes' := fun c => RingHom.congr_fun (ringHom_ext_zp (p := p) (f.comp (algebraMap ℤp A)) (algebraMap ℤp B)) c }

theorem algHomOfRingHom_apply {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤp A] [Algebra ℤp B]
    (f : A →+* B) (a : A) : algHomOfRingHom (p := p) f a = f a := rfl

def tensorAddHom {A M L : Type*} [CommRing A] [Algebra ℤp A] [CommRing M] [Algebra ℤp M] [CommRing L]
    (F : A →+* L) (G : M →+* L) : A ⊗[ℤp] M →+ L :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun b => F x * G b) (fun b b' => by simp only [map_add, mul_add]))
      (fun x x' => by ext b; simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_mul]))
    (fun r x b => by
      have key := RingHom.congr_fun (ringHom_ext_zp (p := p) (F.comp (algebraMap ℤp A)) (G.comp (algebraMap ℤp M))) r
      simp only [RingHom.coe_comp, Function.comp_apply] at key
      show F (r • x) * G b = F x * G (r • b)
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, key]
      ring)

theorem tensorAddHom_tmul {A M L : Type*} [CommRing A] [Algebra ℤp A] [CommRing M] [Algebra ℤp M] [CommRing L]
    (F : A →+* L) (G : M →+* L) (x : A) (b : M) :
    tensorAddHom (p := p) F G (x ⊗ₜ[ℤp] b) = F x * G b := by
  unfold tensorAddHom
  rw [TensorProduct.liftAddHom_tmul]
  rfl

def tensorRingHom {A M L : Type*} [CommRing A] [Algebra ℤp A] [CommRing M] [Algebra ℤp M] [CommRing L]
    (F : A →+* L) (G : M →+* L) : A ⊗[ℤp] M →+* L :=
  { tensorAddHom (p := p) F G with
    map_one' := by
      show tensorAddHom (p := p) F G 1 = 1
      rw [Algebra.TensorProduct.one_def, tensorAddHom_tmul, map_one, map_one, one_mul]
    map_mul' := fun s t => by
      show tensorAddHom (p := p) F G (s * t) = tensorAddHom (p := p) F G s * tensorAddHom (p := p) F G t
      induction s using TensorProduct.induction_on with
      | zero => rw [zero_mul, map_zero, zero_mul]
      | tmul x b =>
        induction t using TensorProduct.induction_on with
        | zero => rw [mul_zero, map_zero, mul_zero]
        | tmul x' b' =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, tensorAddHom_tmul, tensorAddHom_tmul, tensorAddHom_tmul, map_mul,
            map_mul]
          ring
        | add t₁ t₂ h₁ h₂ => rw [mul_add, map_add, map_add, mul_add, h₁, h₂]
      | add s₁ s₂ h₁ h₂ => rw [add_mul, map_add, map_add, add_mul, h₁, h₂] }

theorem tensorRingHom_tmul {A M L : Type*} [CommRing A] [Algebra ℤp A] [CommRing M] [Algebra ℤp M] [CommRing L]
    (F : A →+* L) (G : M →+* L) (x : A) (b : M) :
    tensorRingHom (p := p) F G (x ⊗ₜ[ℤp] b) = F x * G b :=
  tensorAddHom_tmul (p := p) F G x b

section Main

variable (N : ℕ) [NeZero N]
  (κ : Type) [Field κ] [CharP κ p] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]

theorem one_tmul_natCast_mul {M : Type*} [CommRing M] [Algebra ℤp M] (c : M) :
    (1 : κ) ⊗ₜ[ℤp] (((p : ℕ) : M) * c) = 0 := by
  rw [show ((p : ℕ) : M) * c = ((p : ℕ) : ℤp) • c by rw [Algebra.smul_def, map_natCast],
    ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, map_natCast, CharP.cast_eq_zero, TensorProduct.zero_tmul]

theorem isDomain_tensor_chartAlgFin (hpN : ¬ p ∣ N) : IsDomain (κ ⊗[ℤp] ↥(chartAlgFin N p)) := by
  let K := AlgebraicClosure κ
  haveI : IsDomain (K ⊗[ℤp] ↥(chartAlgFin N p)) :=
    (isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed N p hpN K).1

  let j : κ ⊗[ℤp] ↥(chartAlgFin N p) →ₐ[ℤp] K ⊗[ℤp] ↥(chartAlgFin N p) :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℤp κ K) (AlgHom.id ℤp ↥(chartAlgFin N p))
  have hinj : Function.Injective j := by
    let f : κ →ₗ[κ] K := Algebra.linearMap κ K
    have hf : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr (algebraMap κ K).injective
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hf
    let f' : κ →ₗ[ℤp] K := f.restrictScalars ℤp
    let g' : K →ₗ[ℤp] κ := g.restrictScalars ℤp
    have hgf : g'.comp f' = LinearMap.id := by
      ext x; exact LinearMap.congr_fun hg x
    have hj : ∀ z, j z = f'.rTensor ↥(chartAlgFin N p) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x b => rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    intro z₁ z₂ h
    have := congrArg (g'.rTensor ↥(chartAlgFin N p)) (show f'.rTensor _ z₁ = f'.rTensor _ z₂ by rw [← hj, ← hj, h])
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hgf, LinearMap.rTensor_id,
      LinearMap.id_apply, LinearMap.id_apply] at this
  exact Function.Injective.isDomain j.toRingHom hinj

theorem false_of_one_tmul_j_eq_pow
    (K : Type) [Field K] [Algebra κ K] (g₀ : ↥(chartAlgFin N p) →+* LaurentSeries K)
    (hg₀ : g₀ (jChartFin N p) = jqModC K)
    (s : κ ⊗[ℤp] ↥(chartAlgFin N p)) (hs : (1 : κ) ⊗ₜ[ℤp] jChartFin N p = s ^ p) : False := by

  let χ : κ ⊗[ℤp] ↥(chartAlgFin N p) →+* LaurentSeries K :=
    tensorRingHom (p := p) ((algebraMap K (LaurentSeries K)).comp (algebraMap κ K)) g₀
  have hχj : χ ((1 : κ) ⊗ₜ[ℤp] jChartFin N p) = jqModC K := by
    show tensorRingHom (p := p) _ _ _ = _
    rw [tensorRingHom_tmul, map_one, one_mul]
    exact hg₀
  have hpow : (χ s) ^ p = jqModC K := by rw [← map_pow, ← hs, hχj]
  set x := χ s with hx
  have hx0 : x ≠ 0 := by
    intro h0'
    rw [h0', zero_pow (Fact.out : p.Prime).ne_zero] at hpow
    have := congrArg HahnSeries.order hpow
    rw [HahnSeries.order_zero, order_jqModC_def] at this
    norm_num at this
  have hord : ∀ n : ℕ, (x ^ n).order = n * x.order := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, HahnSeries.order_mul (pow_ne_zero n hx0) hx0, ih]; push_cast; ring
  have h := congrArg HahnSeries.order hpow
  rw [hord, order_jqModC_def] at h
  have hdvd : (p : ℤ) ∣ 1 := ⟨-x.order, by linarith⟩
  have hp1 : p = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hdvd
  exact (Fact.out : p.Prime).one_lt.ne' hp1

theorem map_ker_mul_map_ker_le
    {L : Type*} [CommRing L] (θ : Fin 2 → (↥(chartAlgFin (N * p) p) →+* L))
    (hmin : (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes = {RingHom.ker (θ 0), RingHom.ker (θ 1)})
    (P : Ideal (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))) [hP : P.IsPrime] :
    Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))
        (RingHom.ker (θ 0)) *
      Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))
        (RingHom.ker (θ 1)) ≤ P := by
  have hrad : (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).radical ≤
      P.comap (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) := by
    intro z hz
    obtain ⟨n, hn⟩ := hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hn
    have hc' : z ^ n = ((p : ℕ) : ↥(chartAlgFin (N * p) p)) * c := by rw [← hc]; exact mul_comm c _
    rw [Ideal.mem_comap]
    refine hP.mem_of_pow_mem n ?_
    rw [← map_pow, hc', Algebra.TensorProduct.includeRight_apply, one_tmul_natCast_mul κ]
    exact Ideal.zero_mem _
  rw [← Ideal.map_mul]
  refine (Ideal.map_mono ?_).trans (Ideal.map_le_iff_le_comap.mpr hrad)
  rw [← Ideal.sInf_minimalPrimes, hmin, sInf_pair]
  exact Ideal.mul_le_inf

theorem case_zero
    (ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    {L : Type*} [CommRing L] (θ₀ : ↥(chartAlgFin (N * p) p) →+* L)
    (hfrob : ∀ b : ↥(chartAlgFin N p), θ₀ (w (ι b)) = θ₀ (ι b) ^ p)
    (σ : Fin 2 → (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p)))
    (h0 : ∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (h1 : ∀ z, σ 1 z = σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom z))
    (hI0 : Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))
        (RingHom.ker θ₀) ≤ RingHom.ker (σ 0).toRingHom)
    (b : ↥(chartAlgFin N p)) :
    σ 1 ((1 : κ) ⊗ₜ[ℤp] ι b) = ((1 : κ) ⊗ₜ[ℤp] b) ^ p := by
  have hu : (1 : κ) ⊗ₜ[ℤp] (w (ι b) - (ι b) ^ p) ∈ RingHom.ker (σ 0).toRingHom :=
    hI0 (Ideal.mem_map_of_mem _ (by rw [RingHom.mem_ker, map_sub, map_pow, hfrob b, sub_self]))
  have hu' : σ 0 ((1 : κ) ⊗ₜ[ℤp] w (ι b)) = σ 0 ((1 : κ) ⊗ₜ[ℤp] ((ι b) ^ p)) := by
    rw [← sub_eq_zero, ← map_sub, ← TensorProduct.tmul_sub]
    exact hu
  calc σ 1 ((1 : κ) ⊗ₜ[ℤp] ι b)
      = σ 0 ((1 : κ) ⊗ₜ[ℤp] w (ι b)) := by
        rw [h1, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_apply]
    _ = σ 0 ((1 : κ) ⊗ₜ[ℤp] ((ι b) ^ p)) := hu'
    _ = σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι (((1 : κ) ⊗ₜ[ℤp] b) ^ p)) := by
        rw [map_pow (Algebra.TensorProduct.map (AlgHom.id κ κ) ι), Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Algebra.TensorProduct.tmul_pow, one_pow]
    _ = ((1 : κ) ⊗ₜ[ℤp] b) ^ p := h0 _

theorem one_tmul_j_eq_pow_of_case_one
    (ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p)) (hιj : ι (jChartFin N p) = jChartFin (N * p) p)
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    {L : Type*} [CommRing L] (θ : Fin 2 → (↥(chartAlgFin (N * p) p) →+* L))
    (hθ1 : ∀ c, θ 1 c = θ 0 (w c))
    (hfrob : ∀ b : ↥(chartAlgFin N p), θ 0 (w (ι b)) = θ 0 (ι b) ^ p)
    (σ : Fin 2 → (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p)))
    (h0 : ∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (hI1 : Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))
        (RingHom.ker (θ 1)) ≤ RingHom.ker (σ 0).toRingHom) :
    (1 : κ) ⊗ₜ[ℤp] jChartFin N p = (σ 0 ((1 : κ) ⊗ₜ[ℤp] w.symm (jChartFin (N * p) p))) ^ p := by
  have hv : (1 : κ) ⊗ₜ[ℤp] (jChartFin (N * p) p - (w.symm (jChartFin (N * p) p)) ^ p) ∈
      RingHom.ker (σ 0).toRingHom := by
    refine hI1 (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, hθ1, map_sub, map_pow, AlgEquiv.apply_symm_apply, ← hιj, map_sub, map_pow, hfrob, sub_self]
  have h : σ 0 ((1 : κ) ⊗ₜ[ℤp] (jChartFin (N * p) p - (w.symm (jChartFin (N * p) p)) ^ p)) = 0 :=
    RingHom.mem_ker.mp hv
  rw [TensorProduct.tmul_sub, map_sub, sub_eq_zero] at h
  have hl : σ 0 ((1 : κ) ⊗ₜ[ℤp] jChartFin (N * p) p) = (1 : κ) ⊗ₜ[ℤp] jChartFin N p := by
    rw [← hιj, ← h0 ((1 : κ) ⊗ₜ[ℤp] jChartFin N p), Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [← hl, h, ← map_pow (σ 0), Algebra.TensorProduct.tmul_pow, one_pow]

theorem case_one_false
    (ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hι : ∀ b, (((ι b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (σ : Fin 2 → (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p)))
    (h0 : ∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (K : Type) [Field K] [Algebra κ K] (θ : Fin 2 → (↥(chartAlgFin (N * p) p) →+* LaurentSeries K))
    (hθ1 : ∀ c, θ 1 c = θ 0 (w c))
    (hpin : ∀ (c : ↥(chartAlgFin (N * p) p)) (y : LaurentSeries ℤ),
      ((c : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) = coeffMap (Int.castRingHom ℚ) y →
      θ 0 c = coeffMap (Int.castRingHom K) y)
    (hfrob : ∀ b : ↥(chartAlgFin N p), θ 0 (w (ι b)) = θ 0 (ι b) ^ p)
    (hI1 : Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))
        (RingHom.ker (θ 1)) ≤ RingHom.ker (σ 0).toRingHom) : False := by

  have hj1 : (((ι (jChartFin N p) : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) :
      LaurentSeries ℚ) = jq := by rw [hι]; rfl
  have hj2 : (((jChartFin (N * p) p : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) :
      LaurentSeries ℚ) = jq := rfl
  have hιj : ι (jChartFin N p) = jChartFin (N * p) p := Subtype.ext (Subtype.ext (hj1.trans hj2.symm))
  have hs := one_tmul_j_eq_pow_of_case_one N κ ι hιj w θ hθ1 hfrob σ h0 hI1
  refine false_of_one_tmul_j_eq_pow N κ K ((θ 0).comp ι.toRingHom) ?_ _ hs
  show θ 0 (ι (jChartFin N p)) = jqModC K
  rw [hιj, hpin (jChartFin (N * p) p) (jqModC ℤ)]
  · exact coeffMap_jqModC (Int.castRingHom K)
  · show jq = _
    rw [coeffMap_jqModC, jqModC_rat]

private theorem _root_.IgusaFrobRing.main (hpN : ¬ p ∣ N)
    (ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hι : ∀ b, (((ι b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hw : ∀ b, ((w b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
      atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p))))
    (σ : Fin 2 → (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p)))
    (h0 : ∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (h1 : ∀ z, σ 1 z = σ 0 (Algebra.TensorProduct.map (AlgHom.id κ κ) w.toAlgHom z))
    (b : ↥(chartAlgFin N p)) :
    σ 1 ((1 : κ) ⊗ₜ[ℤp] ι b) = ((1 : κ) ⊗ₜ[ℤp] b) ^ p := by
  haveI : IsDomain (κ ⊗[ℤp] ↥(chartAlgFin N p)) := isDomain_tensor_chartAlgFin N κ hpN
  haveI : CharP (AlgebraicClosure κ) p :=
    charP_of_injective_algebraMap (algebraMap κ (AlgebraicClosure κ)).injective p
  obtain ⟨θ, hθ1, hpin, -, hmin, hfrob, -⟩ :=
    exists_ringHom_laurentSeries_pair_chartAlgFin_mul_frobenius_of_not_dvd N p hpN ι hι w hw (AlgebraicClosure κ)
  haveI hP : (RingHom.ker (σ 0).toRingHom).IsPrime := RingHom.ker_isPrime _
  rcases hP.mul_le.mp (map_ker_mul_map_ker_le N κ θ hmin (RingHom.ker (σ 0).toRingHom)) with hI0 | hI1
  · exact case_zero N κ ι w (θ 0) hfrob σ h0 h1 hI0 b
  · exact (case_one_false N κ ι hι w σ h0 (AlgebraicClosure κ) θ hθ1 hpin hfrob hI1).elim

p2m_export "IgusaFrobRing" "main"
end Main

section KerRetr

variable (N : ℕ) [NeZero N]
  (κ : Type) [Field κ] [CharP κ p] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]

theorem jqModC_sub_pow_ne_zero (K : Type) [Field K] : jqModC K - jqModC K ^ (p * p) ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  have h0 : jqModC K ≠ 0 := by
    intro h0
    have := order_jqModC_def K
    rw [h0, HahnSeries.order_zero] at this
    norm_num at this
  have hord : ∀ n : ℕ, (jqModC K ^ n).order = n * (jqModC K).order := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, HahnSeries.order_mul (pow_ne_zero n h0) h0, ih]; push_cast; ring
  have := congrArg HahnSeries.order h
  rw [hord, order_jqModC_def] at this
  have hp : (1 : ℤ) < p * p := by
    have h1 : (1 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    nlinarith
  push_cast at this
  linarith

theorem kerRetr (hpN : ¬ p ∣ N)
    (ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hι : ∀ b, (((ι b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (w : ↥(chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(chartAlgFin (N * p) p))
    (hw : ∀ b, ((w b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
      atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p))))
    (σ₀ : κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z)
    (𝔭 : Ideal ↥(chartAlgFin (N * p) p))
    (h𝔭 : 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes) :
    Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) 𝔭
        ≤ RingHom.ker σ₀.toRingHom ↔
      w (ι (jChartFin N p)) - ι (jChartFin N p) ^ p ∈ 𝔭 := by
  haveI : IsDomain (κ ⊗[ℤp] ↥(chartAlgFin N p)) := isDomain_tensor_chartAlgFin N κ hpN
  haveI : CharP (AlgebraicClosure κ) p :=
    charP_of_injective_algebraMap (algebraMap κ (AlgebraicClosure κ)).injective p
  obtain ⟨θ, hθ1, hpin, hne, hmin, hfrob, -⟩ :=
    exists_ringHom_laurentSeries_pair_chartAlgFin_mul_frobenius_of_not_dvd N p hpN ι hι w hw (AlgebraicClosure κ)

  let σ : Fin 2 → (κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[κ] κ ⊗[ℤp] ↥(chartAlgFin N p)) := fun _ => σ₀
  haveI hP : (RingHom.ker (σ 0).toRingHom).IsPrime := RingHom.ker_isPrime _

  have hj1 : (((ι (jChartFin N p) : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) :
      LaurentSeries ℚ) = jq := by rw [hι]; rfl
  have hj2 : (((jChartFin (N * p) p : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) :
      LaurentSeries ℚ) = jq := rfl
  have hιj : ι (jChartFin N p) = jChartFin (N * p) p := Subtype.ext (Subtype.ext (hj1.trans hj2.symm))

  have hww : ∀ c, w (w c) = c := by
    obtain ⟨w', hw', hww'⟩ := exists_algEquiv_chartAlgFin_mul_eq_atkinLehnerInvolutionFull N p hpN
    have he : ∀ c, w c = w' c := fun c => Subtype.ext (by rw [hw, hw'])
    intro c
    rw [he, he]
    exact AlgEquiv.congr_fun hww' c

  have hu0 : w (ι (jChartFin N p)) - ι (jChartFin N p) ^ p ∈ RingHom.ker (θ 0) := by
    rw [RingHom.mem_ker, map_sub, map_pow, hfrob, sub_self]
  have hθj : θ 0 (jChartFin (N * p) p) = jqModC (AlgebraicClosure κ) := by
    rw [hpin (jChartFin (N * p) p) (jqModC ℤ)]
    · exact coeffMap_jqModC (Int.castRingHom (AlgebraicClosure κ))
    · show jq = _
      rw [coeffMap_jqModC, jqModC_rat]
  have hu1 : w (ι (jChartFin N p)) - ι (jChartFin N p) ^ p ∉ RingHom.ker (θ 1) := by
    rw [RingHom.mem_ker, hθ1, map_sub, map_pow, hww, map_sub, map_pow, hfrob, hιj, hθj, ← pow_mul]
    exact jqModC_sub_pow_ne_zero (p := p) (AlgebraicClosure κ)

  have hnot1 : ¬ Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp]
      κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) (RingHom.ker (θ 1)) ≤ RingHom.ker (σ 0).toRingHom :=
    fun hI1 => case_one_false N κ ι hι w σ h0 (AlgebraicClosure κ) θ hθ1 hpin hfrob hI1

  have hyes0 : Ideal.map (Algebra.TensorProduct.includeRight : ↥(chartAlgFin (N * p) p) →ₐ[ℤp]
      κ ⊗[ℤp] ↥(chartAlgFin (N * p) p)) (RingHom.ker (θ 0)) ≤ RingHom.ker (σ 0).toRingHom :=
    (hP.mul_le.mp (map_ker_mul_map_ker_le N κ θ hmin (RingHom.ker (σ 0).toRingHom))).resolve_right hnot1

  have h𝔭' : 𝔭 = RingHom.ker (θ 0) ∨ 𝔭 = RingHom.ker (θ 1) := by
    rw [hmin] at h𝔭
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h𝔭
  rcases h𝔭' with rfl | rfl
  · exact ⟨fun _ => hu0, fun _ => hyes0⟩
  · exact ⟨fun h => (hnot1 h).elim, fun h => (hu1 h).elim⟩

end KerRetr

end IgusaFrobRing

namespace InfOnC0Alg

open scoped TensorProduct
open ModularCurve ModularCurve.IgusaScheme

variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]

set_option quotPrecheck false in
local notation "ℤq" => ↥(GaloisRep.ratLocalizedAt q)
set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldFull (N₀ * q))
set_option quotPrecheck false in
local notation "𝒪" => ↥(IgusaScheme.chartAlgFin (N₀ * q) q)
set_option quotPrecheck false in
local notation "𝒪N" => ↥(IgusaScheme.chartAlgFin N₀ q)
set_option quotPrecheck false in
local notation "BB" => ↥(IgusaScheme.chartAlgInf (N₀ * q) q)

theorem mul_mem_nonunits {F : Type*} [Field F] (W : ValuationSubring F) {x y : F} (hx : x ∈ W)
    (hy : y ∈ W.nonunits) : x * y ∈ W.nonunits := by
  obtain ⟨hy', hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hy
  refine ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨mul_mem hx hy', ?_⟩
  have : (⟨x * y, mul_mem hx hy'⟩ : W) = ⟨x, hx⟩ * ⟨y, hy'⟩ := rfl
  rw [this]
  exact Ideal.mul_mem_left _ _ hm

structure Setup where
  hqN : ¬ q ∣ N₀
  W : Fin 2 → ValuationSubring FF
  hW₀ : ∀ f : FF, f ∈ W 0 ↔ ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod q)) y ≠ 0 ∧
    (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x
  hW₁ : ∀ f : FF, f ∈ W 1 ↔ atkinLehnerInvolutionFull N₀ q f ∈ W 0
  P : Fin 2 → Ideal 𝒪
  hPmem : ∀ (i : Fin 2) (a : 𝒪), a ∈ P i ↔ ((a : FF) ∈ (W i).nonunits)
  hPprime : ∀ i, (P i).IsPrime
  hP01 : P 0 ≠ P 1
  hPmin : (Ideal.span {((q : ℕ) : 𝒪)}).minimalPrimes = {P 0, P 1}
  hjW : ∀ i, (jFull (N₀ * q) : FF) ∈ W i
  w : 𝒪 ≃ₐ[ℤq] 𝒪
  hw : ∀ b, ((w b : 𝒪) : FF) = atkinLehnerInvolutionFull N₀ q (b : FF)
  hww : w.trans w = AlgEquiv.refl
  b₁ : BB
  hb₁W : ((b₁ : BB) : FF) ∈ (W 1).nonunits
  hb₁coeff : (((b₁ : BB) : FF) : LaurentSeries ℚ).coeff 0 = 1

  hOggW : ((w (IgusaScheme.jChartFin (N₀ * q) q) : 𝒪) : FF) - (jFull (N₀ * q) : FF) ^ q ∈ (W 0).nonunits

theorem nonempty_setup (hqN : ¬ q ∣ N₀) : Nonempty (Setup N₀ q) := by
  obtain ⟨W, hW₀, hW₁, hne, habove, hcomplete⟩ :=
    exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd N₀ q hqN
  obtain ⟨P, hPmem, hPprime, hP01, hPmin⟩ :=
    DRModelPackageLevel.exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair N₀ q hqN W hW₀ hW₁ hne
      habove hcomplete
  obtain ⟨w, hw, hww⟩ := exists_algEquiv_chartAlgFin_mul_eq_atkinLehnerInvolutionFull N₀ q hqN
  obtain ⟨-, ⟨htB, -, -, -⟩, hsep⟩ := exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd N₀ q hqN
  obtain ⟨⟨ht1, -⟩, ⟨hb1, hb1c⟩⟩ := hsep (W 0) (W 1) hW₀ hW₁
  have hjW : ∀ i, (jFull (N₀ * q) : FF) ∈ W i := by
    intro i
    have h := ((habove i).2.1 Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)).1
    rw [Polynomial.eval₂_X] at h
    exact h

  let uB : BB := IgusaScheme.jInvChartInf (N₀ * q) q
  let tB : BB := ⟨_, htB⟩
  refine ⟨⟨hqN, W, hW₀, hW₁, P, hPmem, hPprime, hP01, hPmin, hjW, w, hw, hww, tB ^ q - uB ^ (q ^ 2 - 1), ?_, ?_, ?_⟩⟩
  · convert hb1 using 2
    simp only [Subalgebra.coe_sub, Subalgebra.coe_pow]
    rfl
  · have : (((tB ^ q - uB ^ (q ^ 2 - 1) : BB) : FF) : LaurentSeries ℚ) =
        (((⟨qExpand ℚ q jq, jqd_mem_full (N₀ * q) (dvd_mul_left q N₀)⟩ : FF) * (jFull (N₀ * q))⁻¹ ^ q) ^ q -
          ((jFull (N₀ * q))⁻¹) ^ (q ^ 2 - 1) : FF) := by
      simp only [Subalgebra.coe_sub, Subalgebra.coe_pow]
      rfl
    rw [this]
    exact hb1c
  ·
    have hj : (jFull (N₀ * q) : FF) ≠ 0 := jFull_ne_zero (N₀ * q)
    have e : ((w (IgusaScheme.jChartFin (N₀ * q) q) : 𝒪) : FF) - (jFull (N₀ * q) : FF) ^ q =
        (jFull (N₀ * q) : FF) ^ q *
          ((⟨qExpand ℚ q jq, jqd_mem_full (N₀ * q) (dvd_mul_left q N₀)⟩ : FF) * (jFull (N₀ * q))⁻¹ ^ q - 1) := by
      have hwj : ((w (IgusaScheme.jChartFin (N₀ * q) q) : 𝒪) : FF) =
          (⟨qExpand ℚ q jq, jqd_mem_full (N₀ * q) (dvd_mul_left q N₀)⟩ : FF) := by
        rw [hw, IgusaScheme.coe_jChartFin]
        have h1 := (isAtkinLehnerAutFull_atkinLehnerInvolutionFull N₀ q
          (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N₀ q Fact.out hqN) 1 inferInstance (one_dvd N₀)).1
        have hj1 : (⟨qExpand ℚ 1 jq, jqd_mem_full (N₀ * q) (Dvd.dvd.mul_right (one_dvd N₀) q)⟩ : FF) = jFull (N₀ * q) :=
          Subtype.ext (qExpand_one_apply jq)
        rw [hj1] at h1
        rw [h1]
        exact Subtype.ext (qExpand_congr (Nat.one_mul q) jq)
      rw [hwj, mul_sub, mul_one, ← mul_assoc, mul_comm ((jFull (N₀ * q) : FF) ^ q), mul_assoc, ← mul_pow,
        mul_inv_cancel₀ hj, one_pow, mul_one]
    rw [e]
    exact mul_mem_nonunits (W 0) (pow_mem (hjW 0) q) ht1

end InfOnC0Alg

namespace InfOnC0Alg

open scoped TensorProduct
open ModularCurve ModularCurve.IgusaScheme

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]

set_option quotPrecheck false in
local notation "ℤq" => ↥(GaloisRep.ratLocalizedAt q)
set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldFull (N₀ * q))
set_option quotPrecheck false in
local notation "𝒪" => ↥(IgusaScheme.chartAlgFin (N₀ * q) q)
set_option quotPrecheck false in
local notation "𝒪₀" => ↥(IgusaScheme.chartAlgFin N₀ q)
set_option quotPrecheck false in
local notation "BB" => ↥(IgusaScheme.chartAlgInf (N₀ * q) q)

namespace Setup

variable (S : Setup N₀ q)

scoped instance P_isPrime (i : Fin 2) : (S.P i).IsPrime := S.hPprime i

theorem P_mem_minimalPrimes (i : Fin 2) : S.P i ∈ (Ideal.span {((q : ℕ) : 𝒪)}).minimalPrimes := by
  rw [S.hPmin]
  fin_cases i
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

theorem P_eq_of_le {i k : Fin 2} (h : S.P i ≤ S.P k) : S.P i = S.P k :=
  le_antisymm h ((S.P_mem_minimalPrimes k).2 ⟨S.hPprime i, (S.P_mem_minimalPrimes i).1.2⟩ h)

theorem w_w (c : 𝒪) : S.w (S.w c) = c := AlgEquiv.congr_fun S.hww c

section WithIota

variable (iota : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
  (hiota : ∀ b, (((iota b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
    ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))

include hiota in
theorem iota_jChartFin : iota (IgusaScheme.jChartFin N₀ q) = IgusaScheme.jChartFin (N₀ * q) q := by
  have hj1 : (((iota (IgusaScheme.jChartFin N₀ q) : 𝒪) : FF) : LaurentSeries ℚ) = jq := by rw [hiota]; rfl
  have hj2 : (((IgusaScheme.jChartFin (N₀ * q) q : 𝒪) : FF) : LaurentSeries ℚ) = jq := rfl
  exact Subtype.ext (Subtype.ext (hj1.trans hj2.symm))

abbrev Ogg : 𝒪 := S.w (iota (IgusaScheme.jChartFin N₀ q)) - iota (IgusaScheme.jChartFin N₀ q) ^ q

include hiota in
theorem Ogg_mem_P0 : S.Ogg iota ∈ S.P 0 := by
  rw [S.hPmem]
  show ((S.w (iota (IgusaScheme.jChartFin N₀ q)) - iota (IgusaScheme.jChartFin N₀ q) ^ q :
    ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (S.W 0).nonunits
  rw [iota_jChartFin iota hiota, Subalgebra.coe_sub, Subalgebra.coe_pow, IgusaScheme.coe_jChartFin]
  exact S.hOggW

variable (κ : Type) [Field κ] [CharP κ q] [Algebra ↥(GaloisRep.ratLocalizedAt q) κ]

include hiota in

theorem map_P0_le_ker (σ₀ : κ ⊗[ℤq] 𝒪 →ₐ[κ] κ ⊗[ℤq] 𝒪₀)
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota z) = z) :
    Ideal.map (Algebra.TensorProduct.includeRight : 𝒪 →ₐ[ℤq] κ ⊗[ℤq] 𝒪) (S.P 0) ≤ RingHom.ker σ₀.toRingHom :=
  (map_le_ker_retraction_iff_mem_of_mem_minimalPrimes_of_not_dvd N₀ q S.hqN κ iota hiota S.w S.hw σ₀ h0 (S.P 0)
    (S.P_mem_minimalPrimes 0)).mpr (S.Ogg_mem_P0 iota hiota)

abbrev I (i : Fin 2) : Ideal (κ ⊗[ℤq] 𝒪) :=
  Ideal.map (Algebra.TensorProduct.includeRight : 𝒪 →ₐ[ℤq] κ ⊗[ℤq] 𝒪) (S.P i)

theorem I_mul_le (Q : Ideal (κ ⊗[ℤq] 𝒪)) [hQ : Q.IsPrime] : S.I κ 0 * S.I κ 1 ≤ Q := by
  have hrad : (Ideal.span {((q : ℕ) : 𝒪)}).radical ≤
      Q.comap (Algebra.TensorProduct.includeRight : 𝒪 →ₐ[ℤq] κ ⊗[ℤq] 𝒪) := by
    intro z hz
    obtain ⟨n, hn⟩ := hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hn
    have hc' : z ^ n = ((q : ℕ) : 𝒪) * c := by rw [← hc]; exact mul_comm c _
    rw [Ideal.mem_comap]
    refine hQ.mem_of_pow_mem n ?_
    rw [← map_pow, hc', Algebra.TensorProduct.includeRight_apply, IgusaFrobRing.one_tmul_natCast_mul κ]
    exact Ideal.zero_mem _
  rw [← Ideal.map_mul]
  refine (Ideal.map_mono ?_).trans (Ideal.map_le_iff_le_comap.mpr hrad)
  rw [← Ideal.sInf_minimalPrimes, S.hPmin, sInf_pair]
  exact Ideal.mul_le_inf

theorem I_le_or_I_le (Q : Ideal (κ ⊗[ℤq] 𝒪)) [hQ : Q.IsPrime] : S.I κ 0 ≤ Q ∨ S.I κ 1 ≤ Q :=
  hQ.mul_le.mp (S.I_mul_le κ Q)

variable [IsAlgClosed κ]

include iota hiota in

theorem exists_readings :
    ∃ θ : Fin 2 → (𝒪 →+* LaurentSeries κ), RingHom.ker (θ 0) = S.P 0 ∧ RingHom.ker (θ 1) = S.P 1 ∧
      θ 1 (S.Ogg iota) ≠ 0 ∧ θ 1 (IgusaScheme.jChartFin (N₀ * q) q) ≠ 0 := by
  obtain ⟨θ, hθ1, hpin, hne, hmin, hfrob, -⟩ :=
    exists_ringHom_laurentSeries_pair_chartAlgFin_mul_frobenius_of_not_dvd N₀ q S.hqN iota hiota S.w S.hw κ
  have hiotaj := iota_jChartFin iota hiota

  have hu0 : S.Ogg iota ∈ RingHom.ker (θ 0) := by
    rw [RingHom.mem_ker, map_sub, map_pow, hfrob, sub_self]
  have hθj : θ 0 (IgusaScheme.jChartFin (N₀ * q) q) = jqModC κ := by
    rw [hpin (IgusaScheme.jChartFin (N₀ * q) q) (jqModC ℤ)]
    · exact coeffMap_jqModC (Int.castRingHom κ)
    · show jq = _
      rw [coeffMap_jqModC, jqModC_rat]
  have hu1 : S.Ogg iota ∉ RingHom.ker (θ 1) := by
    rw [RingHom.mem_ker, hθ1, map_sub, map_pow, S.w_w, map_sub, map_pow, hfrob, hiotaj, hθj, ← pow_mul]
    exact IgusaFrobRing.jqModC_sub_pow_ne_zero (p := q) κ
  have hP0 : S.P 0 ∈ ({RingHom.ker (θ 0), RingHom.ker (θ 1)} : Set (Ideal 𝒪)) := by
    rw [← hmin]; exact S.P_mem_minimalPrimes 0
  have hP1 : S.P 1 ∈ ({RingHom.ker (θ 0), RingHom.ker (θ 1)} : Set (Ideal 𝒪)) := by
    rw [← hmin]; exact S.P_mem_minimalPrimes 1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP0 hP1
  have h0 : RingHom.ker (θ 0) = S.P 0 := by
    rcases hP0 with h | h
    · exact h.symm
    · exact absurd (h ▸ S.Ogg_mem_P0 iota hiota) hu1
  have hθ1j : θ 1 (IgusaScheme.jChartFin (N₀ * q) q) ≠ 0 := by
    rw [hθ1, ← hiotaj, hfrob, hiotaj, hθj]
    exact pow_ne_zero _ (jqModC_ne_zero_of_nontrivial κ)
  refine ⟨θ, h0, ?_, fun h => hu1 (RingHom.mem_ker.mpr h), hθ1j⟩
  rcases hP1 with h | h
  · exact absurd (h.trans h0) S.hP01.symm
  · exact h.symm

include iota hiota in

theorem not_I_le_radical (i : Fin 2) : ¬ S.I κ i ≤ (⊥ : Ideal (κ ⊗[ℤq] 𝒪)).radical := by
  obtain ⟨θ, hθ0, hθ1, -, -⟩ := S.exists_readings iota hiota κ

  obtain ⟨k, hik⟩ : ∃ k : Fin 2, k ≠ i := ⟨i + 1, by fin_cases i <;> decide⟩
  have hk : RingHom.ker (θ k) = S.P k := by fin_cases k <;> [exact hθ0; exact hθ1]
  intro hle
  apply hik

  have hsub : S.P i ≤ S.P k := by
    intro a ha
    have h1 : ((1 : κ) ⊗ₜ[ℤq] a) ∈ S.I κ i := Ideal.mem_map_of_mem _ ha
    obtain ⟨n, hn⟩ := hle h1
    rw [Ideal.mem_bot] at hn
    let Θ : κ ⊗[ℤq] 𝒪 →+* LaurentSeries κ :=
      IgusaFrobRing.tensorRingHom (p := q) (algebraMap κ (LaurentSeries κ)) (θ k)
    have h2 : (θ k a) ^ n = 0 := by
      have := congrArg Θ hn
      rw [map_pow, map_zero] at this
      rwa [show Θ ((1 : κ) ⊗ₜ[ℤq] a) = θ k a by
        rw [IgusaFrobRing.tensorRingHom_tmul, map_one, one_mul]] at this
    rw [← hk, RingHom.mem_ker]
    exact pow_eq_zero_iff'.mp h2 |>.1
  have heq := S.P_eq_of_le hsub

  by_contra hki
  fin_cases i <;> fin_cases k <;> simp_all [S.hP01, S.hP01.symm]

include iota hiota in

theorem one_tmul_Ogg_mul_j_not_mem_radical :
    ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] (S.Ogg iota * IgusaScheme.jChartFin (N₀ * q) q)) ∉
      (⊥ : Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] 𝒪)).radical := by
  obtain ⟨θ, -, -, hOgg, hj⟩ := S.exists_readings iota hiota κ
  rintro ⟨n, hn⟩
  rw [Ideal.mem_bot] at hn
  let Θ : κ ⊗[↥(GaloisRep.ratLocalizedAt q)] 𝒪 →+* LaurentSeries κ :=
    IgusaFrobRing.tensorRingHom (p := q) (algebraMap κ (LaurentSeries κ)) (θ 1)
  have h2 := congrArg Θ hn
  rw [map_pow, map_zero, show Θ ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)]
      (S.Ogg iota * IgusaScheme.jChartFin (N₀ * q) q)) = θ 1 (S.Ogg iota) * θ 1 (IgusaScheme.jChartFin (N₀ * q) q) by
    rw [IgusaFrobRing.tensorRingHom_tmul, map_one, one_mul, map_mul]] at h2
  rcases mul_eq_zero.mp (pow_eq_zero_iff'.mp h2).1 with h | h
  · exact hOgg h
  · exact hj h

end WithIota

theorem exists_pow_mul_b₁ :
    ∃ (n : ℕ) (a : 𝒪), a ∈ S.P 1 ∧
      IgusaScheme.inclInf (N₀ * q) q S.b₁ * IgusaScheme.inclFin (N₀ * q) q (IgusaScheme.jChartFin (N₀ * q) q ^ n) =
        IgusaScheme.inclFin (N₀ * q) q a := by
  letI := (IgusaScheme.inclFin (N₀ * q) q).toRingHom.toAlgebra
  haveI := IgusaScheme.isLocalization_away_inclFin (N₀ * q) q
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (Submonoid.powers (IgusaScheme.jChartFin (N₀ * q) q))
    (IgusaScheme.inclInf (N₀ * q) q S.b₁)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  refine ⟨n, a, ?_, ?_⟩
  · rw [S.hPmem]
    have hval : (a : FF) = (S.b₁ : FF) * (jFull (N₀ * q) : FF) ^ n := by
      have := congrArg (fun x : ↥(IgusaScheme.chartAlgMid (N₀ * q) q) => (x : FF)) h
      simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Subalgebra.coe_mul,
        IgusaScheme.coe_chartIncl] at this
      rw [← this, ← hn, Subalgebra.coe_pow, IgusaScheme.coe_jChartFin]
    rw [hval, mul_comm ((S.b₁ : BB) : FF) ((jFull (N₀ * q) : FF) ^ n)]
    exact mul_mem_nonunits (S.W 1) (pow_mem (S.hjW 1) n) S.hb₁W
  · rw [hn]
    exact h

theorem rho_b₁ (rhoInf : BB →ₐ[ℤq] ℤq)
    (hrho : ∀ b : BB, ((rhoInf b : ℤq) : ℚ) = ((b : FF) : LaurentSeries ℚ).coeff 0) : rhoInf S.b₁ = 1 :=
  Subtype.ext (by rw [hrho, S.hb₁coeff]; rfl)

end Setup
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Alg.Setup"

end InfOnC0Alg
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Alg.Setup P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Alg"

end
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Alg.Setup P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Alg"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
open scoped TensorProduct

namespace InfOnC0Geo

variable (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime] (κ : Type) [CommRing κ] [Algebra (R q) κ]

theorem chart_comm_fin :
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q))).toRingHom) ≫ ιFin N q) ≫ igusaTo N q =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (R q) κ)) := by
  rw [Category.assoc, ιFin_igusaTo, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem chart_comm_inf :
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R q) (A := κ) (B := ↥(chartAlgInf N q))).toRingHom) ≫ ιInf N q) ≫ igusaTo N q =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R q) (A := κ) (B := ↥(chartAlgInf N q)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (R q) κ)) := by
  rw [Category.assoc, ιInf_igusaTo, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

def cFin : Spec (CommRingCat.of (κ ⊗[R q] ↥(chartAlgFin N q))) ⟶
    pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))) :=
  pullback.lift _ _ (chart_comm_fin N q κ)

def cInf : Spec (CommRingCat.of (κ ⊗[R q] ↥(chartAlgInf N q))) ⟶
    pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))) :=
  pullback.lift _ _ (chart_comm_inf N q κ)

@[scoped simp] theorem cFin_fst : cFin N q κ ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
      (R := R q) (A := κ) (B := ↥(chartAlgFin N q))).toRingHom) ≫ ιFin N q := pullback.lift_fst _ _ _
@[scoped simp] theorem cFin_snd : cFin N q κ ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := R q) (A := κ) (B := ↥(chartAlgFin N q)))) := pullback.lift_snd _ _ _
@[scoped simp] theorem cInf_fst : cInf N q κ ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
      (R := R q) (A := κ) (B := ↥(chartAlgInf N q))).toRingHom) ≫ ιInf N q := pullback.lift_fst _ _ _
@[scoped simp] theorem cInf_snd : cInf N q κ ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := R q) (A := κ) (B := ↥(chartAlgInf N q)))) := pullback.lift_snd _ _ _

theorem isPullback_cFin :
    IsPullback (cFin N q κ) (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q))).toRingHom)) (pullback.fst _ _) (ιFin N q) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd _ _)
    (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))) (h₂₂ := igusaTo N q) ?_ (cFin_fst N q κ)
    (IsPullback.of_hasPullback _ _).flip
  rw [cFin_snd, ιFin_igusaTo]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct (R q) κ ↥(chartAlgFin N q))

theorem isPullback_cInf :
    IsPullback (cInf N q κ) (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R q) (A := κ) (B := ↥(chartAlgInf N q))).toRingHom)) (pullback.fst _ _) (ιInf N q) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd _ _)
    (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))) (h₂₂ := igusaTo N q) ?_ (cInf_fst N q κ)
    (IsPullback.of_hasPullback _ _).flip
  rw [cInf_snd, ιInf_igusaTo]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct (R q) κ ↥(chartAlgInf N q))

scoped instance isOpenImmersion_cFin : IsOpenImmersion (cFin N q κ) := by
  rw [← (isPullback_cFin N q κ).isoPullback_hom_fst]; infer_instance

scoped instance isOpenImmersion_cInf : IsOpenImmersion (cInf N q κ) := by
  rw [← (isPullback_cInf N q κ).isoPullback_hom_fst]; infer_instance

theorem mem_range_cFin_iff (x : ↥(pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))))) :
    x ∈ Set.range (cFin N q κ) ↔ pullback.fst (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))) x ∈
      Set.range (ιFin N q) := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Scheme.Hom.comp_apply, cFin_fst, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · intro hx
    have H := isPullback_cFin N q κ
    have hx' : x ∈ Set.range (pullback.fst (pullback.fst (igusaTo N q)
        (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ)))) (ιFin N q)) := by
      rw [Scheme.Pullback.range_fst]; exact hx
    obtain ⟨t, rfl⟩ := hx'
    exact ⟨H.isoPullback.inv t, by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst]⟩

theorem mem_range_cInf_iff (x : ↥(pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))))) :
    x ∈ Set.range (cInf N q κ) ↔ pullback.fst (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))) x ∈
      Set.range (ιInf N q) := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Scheme.Hom.comp_apply, cInf_fst, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · intro hx
    have H := isPullback_cInf N q κ
    have hx' : x ∈ Set.range (pullback.fst (pullback.fst (igusaTo N q)
        (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ)))) (ιInf N q)) := by
      rw [Scheme.Pullback.range_fst]; exact hx
    obtain ⟨t, rfl⟩ := hx'
    exact ⟨H.isoPullback.inv t, by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst]⟩

theorem mem_range_cFin_or (x : ↥(pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))))) :
    x ∈ Set.range (cFin N q κ) ∨ x ∈ Set.range (cInf N q κ) := by
  rw [mem_range_cFin_iff, mem_range_cInf_iff]
  exact mem_range_ιFin_or_mem_range_ιInf N q _

theorem specMap_inclFin_cFin :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) (inclFin N q)).toRingHom) ≫ cFin N q κ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) (inclInf N q)).toRingHom) ≫ cInf N q κ := by
  have e1 : (Algebra.TensorProduct.map (AlgHom.id κ κ) (inclFin N q)).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R q) (A := κ) (B := ↥(chartAlgFin N q))).toRingHom =
      (Algebra.TensorProduct.includeRight (R := R q) (A := κ) (B := ↥(chartAlgMid N q))).toRingHom.comp
        (inclFin N q).toRingHom :=
    RingHom.ext fun b => by
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have e2 : (Algebra.TensorProduct.map (AlgHom.id κ κ) (inclInf N q)).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R q) (A := κ) (B := ↥(chartAlgInf N q))).toRingHom =
      (Algebra.TensorProduct.includeRight (R := R q) (A := κ) (B := ↥(chartAlgMid N q))).toRingHom.comp
        (inclInf N q).toRingHom :=
    RingHom.ext fun b => by
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have e3 : (Algebra.TensorProduct.map (AlgHom.id κ κ) (inclFin N q)).toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := R q) (A := κ) (B := ↥(chartAlgFin N q))) =
      Algebra.TensorProduct.includeLeftRingHom :=
    RingHom.ext fun a => by
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  have e4 : (Algebra.TensorProduct.map (AlgHom.id κ κ) (inclInf N q)).toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := R q) (A := κ) (B := ↥(chartAlgInf N q))) =
      Algebra.TensorProduct.includeLeftRingHom :=
    RingHom.ext fun a => by
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, cFin_fst, cInf_fst, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1, e2, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp,
      Spec.map_comp_assoc, Spec.map_comp_assoc]
    show _ ≫ fFin N q ≫ ιFin N q = _ ≫ fInf N q ≫ ιInf N q
    rw [glue_condition]
  · rw [Category.assoc, Category.assoc, cFin_snd, cInf_snd, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, e3, e4]

theorem specializes_of_cFin {x y : PrimeSpectrum (κ ⊗[R q] ↥(chartAlgFin N q))}
    (h : cFin N q κ x ⤳ cFin N q κ y) : x ≤ y :=
  (PrimeSpectrum.le_iff_specializes x y).mpr ((cFin N q κ).isOpenEmbedding.isInducing.specializes_iff.mp h)

theorem specializes_of_cInf {x y : PrimeSpectrum (κ ⊗[R q] ↥(chartAlgInf N q))}
    (h : cInf N q κ x ⤳ cInf N q κ y) : x ≤ y :=
  (PrimeSpectrum.le_iff_specializes x y).mpr ((cInf N q κ).isOpenEmbedding.isInducing.specializes_iff.mp h)

end InfOnC0Geo
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Alg.Setup P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Alg P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Geo"

end
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Alg.Setup P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Alg P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Geo"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve~TwoChartIntegralModel NeronModelInfra"
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
open scoped TensorProduct

namespace InfOnC0Main

theorem eq_closedPoint_of_field (κ : Type) [Field κ] (z : ↥(Spec (CommRingCat.of κ))) : z = IsLocalRing.closedPoint κ := by
  apply PrimeSpectrum.ext
  rw [Ideal.eq_bot_of_prime (z : PrimeSpectrum κ).asIdeal]
  exact (Ideal.eq_bot_of_prime _).symm

theorem exists_specMap_eq_of_not_mem {R : Type} [CommRing R] (κ : Type) [Field κ] [Algebra R κ]
    {A M : Type} [CommRing A] [CommRing M] [Algebra R A] [Algebra R M] (f : A →ₐ[R] M) (j : A)
    (hM : letI := f.toRingHom.toAlgebra; IsLocalization.Away j M)
    (Q : PrimeSpectrum (κ ⊗[R] A)) (hj : (1 : κ) ⊗ₜ[R] j ∉ Q.asIdeal) :
    ∃ 𝔐 : PrimeSpectrum (κ ⊗[R] M),
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) f).toRingHom) 𝔐 = Q := by
  letI algAM : Algebra A M := f.toRingHom.toAlgebra
  haveI : IsScalarTower R A M := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  letI algT : Algebra (κ ⊗[R] A) (κ ⊗[R] M) := (Algebra.TensorProduct.map (AlgHom.id κ κ) f).toRingHom.toAlgebra
  haveI : IsScalarTower κ (κ ⊗[R] A) (κ ⊗[R] M) := IsScalarTower.of_algebraMap_eq' <| by
    show algebraMap κ (κ ⊗[R] M) =
      (Algebra.TensorProduct.map (AlgHom.id κ κ) f).toRingHom.comp (algebraMap κ (κ ⊗[R] A))
    rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
  haveI : IsLocalization ((Submonoid.powers j).map (Algebra.TensorProduct.includeRight (R := R) (A := κ)))
      (κ ⊗[R] M) :=
    IsLocalization.tensorProduct_tensorProduct_right R κ (Submonoid.powers j) M (by
      show (Algebra.TensorProduct.map (AlgHom.id κ κ) f).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
        (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := M)).toRingHom.comp f.toRingHom
      exact RingHom.ext fun b => by
        simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply])
  have hQ : Q ∈ Set.range (PrimeSpectrum.comap (algebraMap (κ ⊗[R] A) (κ ⊗[R] M))) := by
    rw [PrimeSpectrum.localization_comap_range (κ ⊗[R] M) ((Submonoid.powers j).map
      (Algebra.TensorProduct.includeRight (R := R) (A := κ)))]
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩ hmem
    apply hj
    refine Q.2.mem_of_pow_mem n ?_
    simpa only [Algebra.TensorProduct.includeRight_apply, map_pow, Algebra.TensorProduct.tmul_pow, one_pow,
      SetLike.mem_coe] using hmem
  obtain ⟨𝔐, h𝔐⟩ := hQ
  refine ⟨𝔐, ?_⟩
  rw [Spec.map_apply, CommRingCat.hom_ofHom]
  exact h𝔐

theorem main
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of (DRLevel.R q)))) (DRLevel.toBase N₀ q))
    (rhoInf : ↥(IgusaScheme.chartAlgInf (N₀ * q) q) →ₐ[DRLevel.R q] DRLevel.R q)
    (hrho : ∀ b : ↥(IgusaScheme.chartAlgInf (N₀ * q) q),
      ((rhoInf b : DRLevel.R q) : ℚ) = ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ).coeff 0)
    (hεchart : εinf.1 = Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ IgusaScheme.ιInf (N₀ * q) q)
    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (iota0 : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hiota : ∀ b, (((iota0 b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hpichart : IgusaScheme.ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ IgusaScheme.ιFin N₀ q)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] (toκ : DRLevel.R q →+* κ)
    (comp0 : DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ)
    (hcomp_over : comp0 ≫ pullback.snd _ _ = pullback.snd _ _)
    [hcomp_ci : IsClosedImmersion comp0]
    (hcomp_pi : comp0 ≫ DRLevel.fibreMap0 π toκ = 𝟙 _)
    (comp1 : DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ)
    (hcomp1_over : comp1 ≫ pullback.snd _ _ = pullback.snd _ _)
    [hcomp1_ci : IsClosedImmersion comp1]
    (hjoint : ∀ y : DRLevel.fibre (N₀ := N₀) toκ, y ∈ Set.range comp0.base ∨ y ∈ Set.range comp1.base) :
    Set.range (DRLevel.sectionFibre εinf toκ).base ⊆ Set.range comp0.base := by
  classical
  letI : Algebra (R q) κ := toκ.toAlgebra
  have htoκ : algebraMap (R q) κ = toκ := rfl
  obtain ⟨S⟩ := InfOnC0Alg.nonempty_setup N₀ q hqN

  let O : Type := ↥(IgusaScheme.chartAlgFin (N₀ * q) q)
  let B : Type := ↥(IgusaScheme.chartAlgInf (N₀ * q) q)
  let Mid : Type := ↥(IgusaScheme.chartAlgMid (N₀ * q) q)
  let cF := InfOnC0Geo.cFin (N₀ * q) q κ
  let cI := InfOnC0Geo.cInf (N₀ * q) q κ
  let c0 := InfOnC0Geo.cFin N₀ q κ

  haveI hint0 : IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ) := isIntegral_pullback_igusaTo_of_charP N₀ q hqN κ
  let ξ : ↥(DRLevel.fibre0 (N₀ := N₀) toκ) := genericPoint _
  have hξ : ∀ z : ↥(DRLevel.fibre0 (N₀ := N₀) toκ), ξ ⤳ z := fun z => genericPoint_specializes z
  have hC0 : ∀ y ∈ Set.range comp0.base, comp0.base ξ ⤳ y := by
    rintro _ ⟨z, rfl⟩; exact (hξ z).map comp0.base.hom.continuous
  have hC1 : ∀ y ∈ Set.range comp1.base, comp1.base ξ ⤳ y := by
    rintro _ ⟨z, rfl⟩; exact (hξ z).map comp1.base.hom.continuous

  let φ : κ ⊗[R q] B →+* κ := IgusaFrobRing.tensorRingHom (p := q) (RingHom.id κ) (toκ.comp rhoInf.toRingHom)
  have hφ : ∀ (x : κ) (b : B), φ (x ⊗ₜ[R q] b) = x * toκ (rhoInf b) := fun x b =>
    IgusaFrobRing.tensorRingHom_tmul (p := q) _ _ x b
  have hsec : DRLevel.sectionFibre εinf toκ = Spec.map (CommRingCat.ofHom φ) ≫ cI := by
    apply pullback.hom_ext
    · rw [DRLevel.sectionFibre, pullback.lift_fst, Category.assoc]
      show _ = _ ≫ InfOnC0Geo.cInf (N₀ * q) q κ ≫ pullback.fst _ _
      rw [InfOnC0Geo.cInf_fst, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hεchart, ← Spec.map_comp_assoc,
        ← CommRingCat.ofHom_comp]
      congr 3
      refine RingHom.ext fun b => ?_
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeRight_apply, hφ, one_mul]
    · rw [DRLevel.sectionFibre, pullback.lift_snd, Category.assoc]
      show _ = _ ≫ InfOnC0Geo.cInf (N₀ * q) q κ ≫ pullback.snd _ _
      rw [InfOnC0Geo.cInf_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : φ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R q) (A := κ) (B := B)) = RingHom.id κ :=
        RingHom.ext fun a => by
          simp only [RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, hφ, map_one,
            RingHom.id_apply, mul_one]
      rw [this, CommRingCat.ofHom_id]
      exact (Spec.map_id _).symm
  let mInf : PrimeSpectrum (κ ⊗[R q] B) := PrimeSpectrum.comap φ (IsLocalRing.closedPoint κ)
  have hmInf : ∀ z : κ ⊗[R q] B, z ∈ (mInf : PrimeSpectrum (κ ⊗[R q] B)).asIdeal ↔ φ z = 0 := by
    intro z
    show z ∈ Ideal.comap φ (IsLocalRing.maximalIdeal κ) ↔ _
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]

  suffices key : cI mInf ∈ Set.range comp0.base by
    rintro _ ⟨z, rfl⟩
    rw [eq_closedPoint_of_field κ z, hsec, Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom]
    exact key

  obtain ⟨σ₀, h0, hcompσ⟩ := exists_retraction_chart_comp_zero_eq N₀ q hqN π iota0 hiota hpichart κ c0
    (InfOnC0Geo.cFin_fst N₀ q κ) (InfOnC0Geo.cFin_snd N₀ q κ) cF (InfOnC0Geo.cFin_fst (N₀ * q) q κ)
    (InfOnC0Geo.cFin_snd (N₀ * q) q κ) ![comp0, comp1]
    (fun i => by fin_cases i <;> assumption) (fun i => by fin_cases i <;> simp <;> infer_instance)
    (by show comp0 ≫ _ = _; exact hcomp_pi)
  replace hcompσ : c0 ≫ comp0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ cF := hcompσ

  haveI : IsDomain (κ ⊗[R q] ↥(IgusaScheme.chartAlgFin N₀ q)) := IgusaFrobRing.isDomain_tensor_chartAlgFin N₀ κ hqN
  have hξc0 : ξ ∈ Set.range c0 := by
    rw [(genericPoint_spec _).mem_open_set_iff c0.isOpenEmbedding.isOpen_range]
    obtain ⟨pt⟩ := (inferInstance : Nonempty (PrimeSpectrum (κ ⊗[R q] ↥(IgusaScheme.chartAlgFin N₀ q))))
    exact ⟨c0 pt, trivial, pt, rfl⟩
  obtain ⟨x0, hx0⟩ := hξc0
  let p₀ : PrimeSpectrum (κ ⊗[R q] O) := PrimeSpectrum.comap σ₀.toRingHom x0
  have hη₀ : comp0.base ξ = cF p₀ := by
    rw [← hx0, ← Scheme.Hom.comp_apply, hcompσ, Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom]
  have hp₀ : S.I κ 0 ≤ p₀.asIdeal := by
    refine (S.map_P0_le_ker iota0 hiota κ σ₀ h0).trans ?_
    intro z hz
    show z ∈ Ideal.comap σ₀.toRingHom (x0 : PrimeSpectrum _).asIdeal
    rw [Ideal.mem_comap, RingHom.mem_ker.mp hz]
    exact Ideal.zero_mem _

  have hrad : ∀ J : Ideal (κ ⊗[R q] O), (∀ 𝔓 : PrimeSpectrum (κ ⊗[R q] O), J ≤ 𝔓.asIdeal) → J ≤ (⊥ : Ideal _).radical := by
    intro J hJ
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun K hK => hJ ⟨K, hK.2⟩

  by_contra hnot
  have hInf1 : cI mInf ∈ Set.range comp1.base := (hjoint _).resolve_left hnot
  have hη1Inf : comp1.base ξ ⤳ cI mInf := hC1 _ hInf1

  have hη1F : comp1.base ξ ∈ Set.range cF := by
    by_contra hno
    apply S.not_I_le_radical iota0 hiota κ 0
    refine hrad _ fun 𝔓 => hp₀.trans ?_
    have hmem : cF 𝔓 ∈ Set.range comp0.base := by
      rcases hjoint (cF 𝔓) with h | h
      · exact h
      · exact absurd ((hC1 _ h).mem_open cF.isOpenEmbedding.isOpen_range ⟨𝔓, rfl⟩) hno
    exact InfOnC0Geo.specializes_of_cFin (N₀ * q) q κ (hη₀ ▸ hC0 _ hmem)
  obtain ⟨Q, hQ⟩ := hη1F
  change PrimeSpectrum (κ ⊗[R q] O) at Q

  have hcov : ∀ 𝔓 : PrimeSpectrum (κ ⊗[R q] O), p₀ ≤ 𝔓 ∨ Q ≤ 𝔓 := by
    intro 𝔓
    rcases hjoint (cF 𝔓) with h | h
    · exact Or.inl (InfOnC0Geo.specializes_of_cFin (N₀ * q) q κ (hη₀ ▸ hC0 _ h))
    · exact Or.inr (InfOnC0Geo.specializes_of_cFin (N₀ * q) q κ (hQ ▸ hC1 _ h))

  rcases S.I_le_or_I_le κ Q.asIdeal with hQ0 | hQ1
  ·
    apply S.not_I_le_radical iota0 hiota κ 0
    refine hrad _ fun 𝔓 => ?_
    rcases hcov 𝔓 with h | h
    · exact hp₀.trans h
    · exact hQ0.trans h
  ·

    have hjQ : ((1 : κ) ⊗ₜ[R q] IgusaScheme.jChartFin (N₀ * q) q) ∉ Q.asIdeal := by
      intro hj
      apply S.one_tmul_Ogg_mul_j_not_mem_radical iota0 hiota κ
      have : Ideal.span {((1 : κ) ⊗ₜ[R q] (S.Ogg iota0 * IgusaScheme.jChartFin (N₀ * q) q))} ≤ (⊥ : Ideal _).radical := by
        refine hrad _ fun 𝔓 => ?_
        rw [Ideal.span_singleton_le_iff_mem, show ((1 : κ) ⊗ₜ[R q] (S.Ogg iota0 * IgusaScheme.jChartFin (N₀ * q) q)) =
            ((1 : κ) ⊗ₜ[R q] S.Ogg iota0) * ((1 : κ) ⊗ₜ[R q] IgusaScheme.jChartFin (N₀ * q) q) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
        · rcases hcov 𝔓 with h | h
          · exact Ideal.mul_mem_right _ _ (h (hp₀ (Ideal.mem_map_of_mem _ (S.Ogg_mem_P0 iota0 hiota))))
          · exact Ideal.mul_mem_left _ _ (h hj)
      exact this (Ideal.subset_span (Set.mem_singleton _))

    obtain ⟨𝔐, h𝔐⟩ := exists_specMap_eq_of_not_mem κ (IgusaScheme.inclFin (N₀ * q) q)
      (IgusaScheme.jChartFin (N₀ * q) q) (IgusaScheme.isLocalization_away_inclFin (N₀ * q) q) Q hjQ

    let Q' : PrimeSpectrum (κ ⊗[R q] B) :=
      PrimeSpectrum.comap (Algebra.TensorProduct.map (AlgHom.id κ κ) (IgusaScheme.inclInf (N₀ * q) q)).toRingHom 𝔐
    have hη1I : comp1.base ξ = cI Q' := by
      rw [← hQ, ← h𝔐, ← Scheme.Hom.comp_apply]
      show (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ)
          (IgusaScheme.inclFin (N₀ * q) q)).toRingHom) ≫ InfOnC0Geo.cFin (N₀ * q) q κ) 𝔐 = _
      rw [InfOnC0Geo.specMap_inclFin_cFin, Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom]
    have hQ'm : Q' ≤ mInf := InfOnC0Geo.specializes_of_cInf (N₀ * q) q κ (hη1I ▸ hη1Inf)

    obtain ⟨n, a, haP1, hab⟩ := S.exists_pow_mul_b₁
    have haQ : ((1 : κ) ⊗ₜ[R q] a) ∈ Q.asIdeal := hQ1 (Ideal.mem_map_of_mem _ haP1)
    rw [← h𝔐, Spec.map_apply, CommRingCat.hom_ofHom, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at haQ hjQ
    let T := Algebra.TensorProduct.map (AlgHom.id κ κ) (IgusaScheme.inclFin (N₀ * q) q)
    change T ((1 : κ) ⊗ₜ[R q] a) ∈ 𝔐.asIdeal at haQ
    change T ((1 : κ) ⊗ₜ[R q] IgusaScheme.jChartFin (N₀ * q) q) ∉ 𝔐.asIdeal at hjQ
    have hTa : T ((1 : κ) ⊗ₜ[R q] a) = ((1 : κ) ⊗ₜ[R q] IgusaScheme.inclInf (N₀ * q) q S.b₁) *
        ((1 : κ) ⊗ₜ[R q] IgusaScheme.inclFin (N₀ * q) q (IgusaScheme.jChartFin (N₀ * q) q)) ^ n := by
      rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_pow, hab]
      exact Algebra.TensorProduct.map_tmul _ _ _ _
    have hTj : T ((1 : κ) ⊗ₜ[R q] IgusaScheme.jChartFin (N₀ * q) q) =
        (1 : κ) ⊗ₜ[R q] IgusaScheme.inclFin (N₀ * q) q (IgusaScheme.jChartFin (N₀ * q) q) :=
      Algebra.TensorProduct.map_tmul _ _ _ _
    rw [hTa] at haQ
    rw [hTj] at hjQ
    have hb₁𝔐 : ((1 : κ) ⊗ₜ[R q] IgusaScheme.inclInf (N₀ * q) q S.b₁) ∈ 𝔐.asIdeal := by
      rcases 𝔐.2.mem_or_mem haQ with h | h
      · exact h
      · exact absurd (𝔐.2.mem_of_pow_mem n h) hjQ
    have hb₁Q' : ((1 : κ) ⊗ₜ[R q] S.b₁) ∈ (Q' : PrimeSpectrum _).asIdeal := by
      simp only [Q', PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact hb₁𝔐
    have h0 := (hmInf _).mp (hQ'm hb₁Q')
    rw [hφ, one_mul, S.rho_b₁ rhoInf hrho, map_one] at h0
    exact one_ne_zero h0

end InfOnC0Main
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Alg.Setup P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Alg P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Geo"

end
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Alg.Setup P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Alg P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.InfOnC0Geo"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve~TwoChartIntegralModel NeronModelInfra"
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of (DRLevel.R q)))) (DRLevel.toBase N₀ q))
    (rhoInf : ↥(IgusaScheme.chartAlgInf (N₀ * q) q) →ₐ[DRLevel.R q] DRLevel.R q)
    (hrho : ∀ b : ↥(IgusaScheme.chartAlgInf (N₀ * q) q),
      ((rhoInf b : DRLevel.R q) : ℚ) = ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ).coeff 0)
    (hεchart : εinf.1 = Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ IgusaScheme.ιInf (N₀ * q) q)

    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (iota0 : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hiota : ∀ b, (((iota0 b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hpichart : IgusaScheme.ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ IgusaScheme.ιFin N₀ q)

    (iotaInf : ↥(IgusaScheme.chartAlgInf N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgInf (N₀ * q) q))
    (hiotaInf : ∀ b, (((iotaInf b : ↥(IgusaScheme.chartAlgInf (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hpichartInf : IgusaScheme.ιInf (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iotaInf.toRingHom) ≫ IgusaScheme.ιInf N₀ q)

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)

    (comp0 : DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ)
    (hcomp_over : comp0 ≫ pullback.snd _ _ = pullback.snd _ _)
    [hcomp_ci : IsClosedImmersion comp0]
    (hcomp_pi : comp0 ≫ DRLevel.fibreMap0 π toκ = 𝟙 _)

    (comp1 : DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ)
    (hcomp1_over : comp1 ≫ pullback.snd _ _ = pullback.snd _ _)
    [hcomp1_ci : IsClosedImmersion comp1]
    (hjoint : ∀ y : DRLevel.fibre (N₀ := N₀) toκ, y ∈ Set.range comp0.base ∨ y ∈ Set.range comp1.base) :
    Set.range (DRLevel.sectionFibre εinf toκ).base ⊆ Set.range comp0.base :=
  InfOnC0Main.main N₀ q hqN εinf rhoInf hrho hεchart π iota0 hiota hpichart κ toκ comp0 hcomp_over hcomp_pi comp1
    hcomp1_over hjoint

end S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id
end P2MW
export P2MW.S_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id (solution)
