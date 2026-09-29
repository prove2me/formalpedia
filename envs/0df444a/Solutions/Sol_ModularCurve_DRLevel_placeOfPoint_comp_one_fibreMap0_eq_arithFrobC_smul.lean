-- Prove2me | solution 1 for ModularCurve.DRLevel.placeOfPoint_comp_one_fibreMap0_eq_arithFrobC_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7265db1a-4579-5c15-a79f-dcbfd55b4618

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_IgusaScheme_retraction_one_tmul_iota_eq_pow_of_not_dvd
import Theorems.Thm_ModularCurve_DRLevel_exists_retraction_chart_comp_zero_eq
import Theorems.Thm_AlgebraicCurve_CurveModel_placeOfPoint_eq_smul_of_fromSpecStalk_comp_eq_frobenius
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_IgusaScheme_jqN_mem_chartAlgFin_and_jFull_mem_chartAlg_jqN
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_placeOfPoint_comp_one_fibreMap0_eq_arithFrobC_smul
p2m_attr_erase "instance" "ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "instance" "instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeRingHom AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU"
p2m_attr_erase "simp" "ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
p2m_open "ModularCurve P2MW.S_ModularCurve_DRLevel_placeOfPoint_comp_one_fibreMap0_eq_arithFrobC_smul.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel P2MW.S_ModularCurve_DRLevel_placeOfPoint_comp_one_fibreMap0_eq_arithFrobC_smul.ModularCurve.DRLevel"

open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R DRLevel.X DRLevel.toBase DRLevel.toBase0 DRLevel.fibre DRLevel.fibre0 DRLevel.fibreMap DRLevel.fibreMap0 IgusaScheme.chartAlgFin IgusaScheme.jChartFin IgusaScheme IgusaScheme.ιFin IgusaScheme.igusaTo IgusaScheme.ιFin_igusaTo qExpand jq modularFunctionFieldFull atkinLehnerInvolutionFull jGeomGen jNGeomGen jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem charP_modularFunctionFieldC arithFrobC baseAut_arithFrobC_apply arithFrobC_smul_jq arithFrobC_smul_jqN IgusaScheme.retraction_one_tmul_iota_eq_pow_of_not_dvd DRLevel.exists_retraction_chart_comp_zero_eq finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero nonempty_modularPolynomialData IgusaScheme.jqN_mem_chartAlgFin_and_jFull_mem_chartAlg_jqN"
namespace DRLevel
p2m_export "ModularCurve.DRLevel" "R X toBase toBase0 fibre fibre0 fibreMap fibreMap0 exists_retraction_chart_comp_zero_eq"
namespace FrobPlace
p2m_open "ModularCurve.DRLevel ModularCurve"

section D0

variable (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [CharP κ q] [PerfectField κ] (N : ℕ) [NeZero N]

omit [Fact q.Prime] [PerfectField κ] in
theorem charP_modularFunctionFieldC : CharP ↥(modularFunctionFieldC κ N) q :=
  charP_of_injective_algebraMap (algebraMap κ ↥(modularFunctionFieldC κ N)).injective q

theorem baseAut_arithFrobC_inv_apply_pow (c : κ) :
    SemilinearAut.baseAut (arithFrobC q κ N)⁻¹ (c ^ q) = c := by
  rw [← baseAut_arithFrobC_apply q κ N c, ← RingAut.mul_apply, ← SemilinearAut.baseAut_mul, inv_mul_cancel,
    SemilinearAut.baseAut_one, RingAut.one_apply]

noncomputable def relFrob : ↥(modularFunctionFieldC κ N) →ₐ[κ] ↥(modularFunctionFieldC κ N) :=
  haveI := charP_modularFunctionFieldC q κ N
  { (frobenius ↥(modularFunctionFieldC κ N) q).comp
      (MulSemiringAction.toRingHom (SemilinearAut κ ↥(modularFunctionFieldC κ N)) ↥(modularFunctionFieldC κ N)
        (arithFrobC q κ N)⁻¹) with
    commutes' := fun c => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
        RingHom.coe_comp, Function.comp_apply, MulSemiringAction.toRingHom_apply, frobenius_def,
        SemilinearAut.smul_algebraMap, ← map_pow, baseAut_arithFrobC_inv_apply_pow] }

theorem relFrob_apply (f : ↥(modularFunctionFieldC κ N)) :
    relFrob q κ N f = ((arithFrobC q κ N)⁻¹ • f) ^ q := rfl

theorem relFrob_jqN :
    relFrob q κ N ⟨jqNModC κ N, jqNModC_mem κ N⟩ = ⟨jqNModC κ N, jqNModC_mem κ N⟩ ^ q := by
  rw [relFrob_apply, inv_smul_eq_iff.mpr (arithFrobC_smul_jqN q κ N).symm]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem finiteAlong_relFrob (hN : (N : κ) ≠ 0) : FiniteAlong κ (relFrob q κ N) := by
  classical
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  obtain ⟨hfd, -⟩ := finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero κ N hN data
  obtain ⟨jN, hjN⟩ : ∃ jN : ↥(modularFunctionFieldC κ N), jN = ⟨jqNModC κ N, jqNModC_mem κ N⟩ := ⟨_, rfl⟩
  rw [← hjN] at hfd
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ, Φ = relFrob q κ N := ⟨_, rfl⟩
  rw [← hΦdef]
  have hΦjN : Φ jN = jN ^ q := by rw [hΦdef, hjN]; exact relFrob_jqN q κ N

  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : IntermediateField κ ↥(modularFunctionFieldC κ N),
      E₁ = IntermediateField.adjoin κ {jN ^ q} := ⟨_, rfl⟩
  have hmem1 : jN ^ q ∈ E₁ := hE₁ ▸ IntermediateField.mem_adjoin_simple_self κ (jN ^ q)
  have h10 : E₁ ≤ IntermediateField.adjoin κ {jN} := by
    rw [hE₁, IntermediateField.adjoin_simple_le_iff]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self κ jN) q
  have h1Φ : E₁ ≤ Φ.fieldRange := by
    rw [hE₁, IntermediateField.adjoin_simple_le_iff, ← hΦjN]
    exact ⟨jN, rfl⟩

  have hint : IsIntegral ↥E₁ jN := by
    refine ⟨Polynomial.X ^ q - Polynomial.C ⟨jN ^ q, hmem1⟩, Polynomial.monic_X_pow_sub_C _ (Fact.out : q.Prime).ne_zero, ?_⟩
    simp [Polynomial.eval₂_sub, sub_self]
  haveI hF : FiniteDimensional ↥E₁ ↥(IntermediateField.adjoin ↥E₁ ({jN} : Set ↥(modularFunctionFieldC κ N))) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hres : IntermediateField.restrictScalars κ (IntermediateField.adjoin ↥E₁ ({jN} : Set ↥(modularFunctionFieldC κ N))) =
      IntermediateField.adjoin κ {jN} := by
    rw [IntermediateField.restrictScalars_adjoin, hE₁]
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (hx | hx)
      · exact h10 (hE₁ ▸ hx)
      · rw [Set.mem_singleton_iff.mp hx]; exact IntermediateField.mem_adjoin_simple_self κ jN
    · exact IntermediateField.adjoin.mono _ _ _ (Set.subset_union_right)
  haveI hF2 : FiniteDimensional ↥(IntermediateField.adjoin ↥E₁ ({jN} : Set ↥(modularFunctionFieldC κ N)))
      ↥(modularFunctionFieldC κ N) := by
    have : FiniteDimensional
        ↥(IntermediateField.restrictScalars κ (IntermediateField.adjoin ↥E₁ ({jN} : Set ↥(modularFunctionFieldC κ N))))
        ↥(modularFunctionFieldC κ N) := by
      rw [hres]; exact hfd
    exact this
  haveI h1L : FiniteDimensional ↥E₁ ↥(modularFunctionFieldC κ N) :=
    FiniteDimensional.trans ↥E₁ ↥(IntermediateField.adjoin ↥E₁ ({jN} : Set ↥(modularFunctionFieldC κ N)))
      ↥(modularFunctionFieldC κ N)

  haveI hEL : FiniteDimensional ↥(IntermediateField.extendScalars h1Φ) ↥(modularFunctionFieldC κ N) :=
    Module.Finite.of_restrictScalars_finite ↥E₁ _ _

  obtain ⟨s, hs⟩ := hEL
  have hmem : ∀ x : ↥(modularFunctionFieldC κ N),
      x ∈ Submodule.span ↥(IntermediateField.extendScalars h1Φ) (s : Set ↥(modularFunctionFieldC κ N)) :=
    fun x => hs ▸ Submodule.mem_top
  let inst : Module ↥(modularFunctionFieldC κ N) ↥(modularFunctionFieldC κ N) := (algebraAlong Φ).toModule
  change @Module.Finite ↥(modularFunctionFieldC κ N) ↥(modularFunctionFieldC κ N) _ _ inst
  refine (@Module.finite_def ↥(modularFunctionFieldC κ N) ↥(modularFunctionFieldC κ N) _ _ inst).mpr ⟨s, ?_⟩
  rw [eq_top_iff]
  rintro x -
  induction hmem x using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul e y _ hy =>
    obtain ⟨l, hl⟩ : ∃ l, Φ l = (e : ↥(modularFunctionFieldC κ N)) := AlgHom.mem_fieldRange.mp e.2
    have key := @Submodule.smul_mem _ _ _ _ inst _ y l hy
    convert key using 1
    rw [IntermediateField.smul_def, ← hl]
    rfl

end D0

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]

theorem chart_comm (N : ℕ) [NeZero N] (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N q))).toRingHom) ≫ IgusaScheme.ιFin N q) ≫
        IgusaScheme.igusaTo N q =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N q)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)) := by
  rw [Category.assoc, IgusaScheme.ιFin_igusaTo, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem apply_inv_apply {X Y : Scheme} (e : X ⟶ Y) [IsIso e] (y : Y) : e.base ((inv e).base y) = y := by
  change (inv e ≫ e).base y = y
  rw [IsIso.inv_hom_id]
  rfl

theorem inv_apply_apply {X Y : Scheme} (e : X ⟶ Y) [IsIso e] (x : X) : (inv e).base (e.base x) = x := by
  change (e ≫ inv e).base x = x
  rw [IsIso.hom_inv_id]
  rfl

noncomputable def chart0 (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) ⟶
      DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) :=
  pullback.lift _ _ (chart_comm (q := q) N₀ κ)

noncomputable def chart (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ⟶
      DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ) :=
  pullback.lift _ _ (chart_comm (q := q) (N₀ * q) κ)

theorem chart_fibreMap (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ]
    (φ : DRLevel.X N₀ q ⟶ DRLevel.X N₀ q) (hφ : φ ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (θ : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hchart : IgusaScheme.ιFin (N₀ * q) q ≫ φ = Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q) :
    chart (N₀ := N₀) (q := q) κ ≫ DRLevel.fibreMap φ hφ (algebraMap (DRLevel.R q) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) θ).toRingHom) ≫ chart (N₀ := N₀) (q := q) κ := by
  apply pullback.hom_ext
  · simp only [chart, DRLevel.fibreMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [hchart, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
  · simp only [chart, DRLevel.fibreMap, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp [Algebra.TensorProduct.includeLeftRingHom_apply]

theorem chart_fibreMap0 (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ]
    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (ι : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hchart : IgusaScheme.ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ IgusaScheme.ιFin N₀ q) :
    chart (N₀ := N₀) (q := q) κ ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) ι).toRingHom) ≫ chart0 (N₀ := N₀) (q := q) κ := by
  apply pullback.hom_ext
  · simp only [chart, chart0, DRLevel.fibreMap0, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [hchart, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
  · simp only [chart, chart0, DRLevel.fibreMap0, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp [Algebra.TensorProduct.includeLeftRingHom_apply]

attribute [reassoc] chart_fibreMap

noncomputable def chart0' (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) ⟶
      DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) :=
  Spec.map (Algebra.TensorProduct.comm (DRLevel.R q) ↥(IgusaScheme.chartAlgFin N₀ q) κ).toRingEquiv.toCommRingCatIso.hom ≫
    (pullbackSpecIso (DRLevel.R q) ↥(IgusaScheme.chartAlgFin N₀ q) κ).inv ≫
      (pullback.congrHom (IgusaScheme.ιFin_igusaTo N₀ q) rfl).inv ≫
        (pullbackRightPullbackFstIso (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))
          (IgusaScheme.ιFin N₀ q)).inv ≫
          pullback.snd (IgusaScheme.ιFin N₀ q) (pullback.fst _ _)

theorem isOpenImmersion_chart0' (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    IsOpenImmersion (chart0' (N₀ := N₀) (q := q) κ) := by
  unfold chart0'; infer_instance

attribute [local instance] isOpenImmersion_chart0'

theorem chart0'_eq (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    chart0' (N₀ := N₀) (q := q) κ = chart0 (N₀ := N₀) (q := q) κ := by
  apply pullback.hom_ext
  · simp only [chart0', chart0, Category.assoc, pullback.lift_fst]
    rw [← pullback.condition, pullbackRightPullbackFstIso_inv_fst_assoc, pullback.congrHom_inv, pullback.lift_fst_assoc,
      Category.comp_id, pullbackSpecIso_inv_fst_assoc, RingEquiv.toCommRingCatIso_hom, ← Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp]
    congr 3
  · simp only [chart0', chart0, Category.assoc, pullback.lift_snd]
    rw [pullbackRightPullbackFstIso_inv_snd_snd, pullback.congrHom_inv, pullback.lift_snd, Category.comp_id,
      pullbackSpecIso_inv_snd, RingEquiv.toCommRingCatIso_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

theorem opensRange_chart0' (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    (chart0' (N₀ := N₀) (q := q) κ).opensRange =
      (pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) ⁻¹ᵁ
        (IgusaScheme.ιFin N₀ q).opensRange := by
  unfold chart0'
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackSnd]

theorem fromSpec_image_top {X : Scheme} {A : CommRingCat} (f : Spec A ⟶ X) [IsOpenImmersion f] (hU : IsAffineOpen (f ''ᵁ ⊤)) :
    hU.fromSpec = Spec.map ((Scheme.ΓSpecIso A).inv ≫ (f.appIso ⊤).inv) ≫ f := by
  have h1 : Spec.map (f.appLE (f ''ᵁ ⊤) ⊤ (le_of_eq (f.preimage_image_eq ⊤).symm)) ≫ hU.fromSpec =
      (isAffineOpen_top (Spec A)).fromSpec ≫ f := IsAffineOpen.SpecMap_appLE_fromSpec _ hU (isAffineOpen_top _) _
  have h2 : (isAffineOpen_top (Spec A)).fromSpec = Spec.map (Scheme.ΓSpecIso A).inv := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have h3 : f.appLE (f ''ᵁ ⊤) ⊤ (le_of_eq (f.preimage_image_eq ⊤).symm) = (f.appIso ⊤).hom := (Scheme.Hom.appIso_hom' _ _).symm
  rw [h3, h2] at h1
  rw [Spec.map_comp, Category.assoc, ← h1, ← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]

theorem adjoin_jGens_eq_top (κ : Type) [Field κ] (N : ℕ) [NeZero N] :
    IntermediateField.adjoin κ ({⟨jqModC κ, jqModC_mem κ N⟩, ⟨jqNModC κ N, jqNModC_mem κ N⟩} :
      Set ↥(modularFunctionFieldC κ N)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  have hle : modularFunctionFieldC κ N ≤
      IntermediateField.lift (F := modularFunctionFieldC κ N)
        (IntermediateField.adjoin κ ({⟨jqModC κ, jqModC_mem κ N⟩, ⟨jqNModC κ N, jqNModC_mem κ N⟩} :
          Set ↥(modularFunctionFieldC κ N))) := by
    change IntermediateField.adjoin κ {jqModC κ, jqNModC κ N} ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | rfl)
    · exact ⟨⟨jqModC κ, jqModC_mem κ N⟩, IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _), rfl⟩
    · exact ⟨⟨jqNModC κ N, jqNModC_mem κ N⟩, IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl), rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [← Subtype.ext hyx]

set_option maxHeartbeats 24000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem frob_comm_of_pins (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [CharP κ q] [PerfectField κ] (N : ℕ) [NeZero N]
    [Algebra (↥(GaloisRep.ratLocalizedAt q)) κ]
    (r : κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q) →+* ↥(modularFunctionFieldC κ N))
    (hr : Function.Injective r)
    (hrκ : ∀ a : κ, r (a ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] 1) = algebraMap κ _ a)
    (hrj : r ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] IgusaScheme.jChartFin N q) = ⟨jqModC κ, jqModC_mem κ N⟩)
    (bN : ↥(IgusaScheme.chartAlgFin N q)) (hrjN : r ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] bN) = ⟨jqNModC κ N, jqNModC_mem κ N⟩)
    (F : κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q) →ₐ[κ] κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q))
    (hF : ∀ b, F ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] b) = ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] b) ^ q)
    (Φ : ↥(modularFunctionFieldC κ N) →ₐ[κ] ↥(modularFunctionFieldC κ N))
    (hΦ : ∀ f, Φ f = ((arithFrobC q κ N)⁻¹ • f) ^ q) :
    ∀ z, r (F z) = Φ (r z) := by
  classical

  haveI : IsDomain (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) := hr.isDomain r
  have halg : ∀ a : κ, algebraMap κ (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) a = a ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] 1 := fun a => by
    rw [Algebra.TensorProduct.algebraMap_apply]; rfl
  have hFκ : ∀ a : κ, F (a ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] 1) = a ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] 1 := fun a => by rw [← halg]; exact F.commutes a

  haveI hAchar : CharP (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) q :=
    charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective κ (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q))) q
  have hfrobR : ∀ x : ↥(GaloisRep.ratLocalizedAt q), frobenius κ q (algebraMap (↥(GaloisRep.ratLocalizedAt q)) κ x) = algebraMap (↥(GaloisRep.ratLocalizedAt q)) κ x := by
    intro x
    have hd : (((x : ℚ).den : ℕ) : κ) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff κ q]
      exact fun h => (Fact.out : q.Prime).ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm x.2) h)
    have hxR : x * (((x : ℚ).den : ℕ) : ↥(GaloisRep.ratLocalizedAt q)) = (((x : ℚ).num : ℤ) : ↥(GaloisRep.ratLocalizedAt q)) :=
      Subtype.ext (by push_cast; exact Rat.mul_den_eq_num _)
    have h1 : algebraMap (↥(GaloisRep.ratLocalizedAt q)) κ x * (((x : ℚ).den : ℕ) : κ) = (((x : ℚ).num : ℤ) : κ) := by
      have := congrArg (algebraMap (↥(GaloisRep.ratLocalizedAt q)) κ) hxR
      rwa [map_mul, map_natCast, map_intCast] at this
    apply mul_right_cancel₀ hd
    rw [← map_natCast (frobenius κ q), ← map_mul, h1, map_intCast, ← h1, map_natCast]
  let frobκ : κ →ₐ[↥(GaloisRep.ratLocalizedAt q)] κ := { frobenius κ q with commutes' := hfrobR }
  have hfrobκ : ∀ a, frobκ a = a ^ q := fun a => rfl
  let G' : κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q) →ₐ[↥(GaloisRep.ratLocalizedAt q)] κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q) := Algebra.TensorProduct.map frobκ (AlgHom.id (↥(GaloisRep.ratLocalizedAt q)) ↥(IgusaScheme.chartAlgFin N q))
  have hG'F : ∀ z, G' (F z) = frobenius (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) q z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    | tmul a b =>
      have hab : a ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] b = (a ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] (1 : ↥(IgusaScheme.chartAlgFin N q))) * ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hab, map_mul, map_mul, hFκ, hF, map_pow, frobenius_def]
      simp only [G', Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hfrobκ, map_one]
      rw [Algebra.TensorProduct.tmul_pow, one_pow, mul_pow, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
        one_pow, one_pow]
  have hFinj : Function.Injective F := by
    refine Function.Injective.of_comp (f := G') ?_
    have : (G' ∘ F : κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q) → κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) = frobenius (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) q := funext hG'F
    rw [this]
    exact frobenius_inj (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) q

  have huinj : Function.Injective (r.comp F.toRingHom) := hr.comp hFinj
  obtain ⟨uK, huK⟩ : ∃ uK : FractionRing (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) →+* ↥(modularFunctionFieldC κ N), uK = IsFractionRing.lift huinj := ⟨_, rfl⟩
  obtain ⟨rK, hrKdef⟩ : ∃ rK : FractionRing (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) →+* ↥(modularFunctionFieldC κ N), rK = IsFractionRing.lift hr := ⟨_, rfl⟩
  have hrK : ∀ z, rK (algebraMap (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) (FractionRing (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q))) z) = r z := fun z => by
    rw [hrKdef, IsFractionRing.lift_algebraMap]
  have hu : ∀ z, uK (algebraMap (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) (FractionRing (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q))) z) = r (F z) := fun z => by
    rw [huK, IsFractionRing.lift_algebraMap]; rfl
  have hv : ∀ z, (Φ.toRingHom.comp rK) (algebraMap (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) (FractionRing (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q))) z) = Φ (r z) := fun z => by
    rw [RingHom.comp_apply, hrK]; rfl
  have hga : ∀ a : κ, uK (algebraMap (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) (FractionRing (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q))) (a ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] (1 : ↥(IgusaScheme.chartAlgFin N q)))) =
      (Φ.toRingHom.comp rK) (algebraMap (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) (FractionRing (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q))) (a ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] (1 : ↥(IgusaScheme.chartAlgFin N q)))) := fun a => by
    rw [hu, hv, hFκ, hrκ, AlgHom.commutes]
  have hgj : uK (algebraMap (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) (FractionRing (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q))) ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] IgusaScheme.jChartFin N q)) =
      (Φ.toRingHom.comp rK) (algebraMap (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) (FractionRing (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q))) ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] IgusaScheme.jChartFin N q)) := by
    rw [hu, hv, hF, map_pow, hrj, hΦ, inv_smul_eq_iff.mpr (arithFrobC_smul_jq q κ N).symm]
  have hgN : uK (algebraMap (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) (FractionRing (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q))) ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] bN)) =
      (Φ.toRingHom.comp rK) (algebraMap (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) (FractionRing (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q))) ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] bN)) := by
    rw [hu, hv, hF, map_pow, hrjN, hΦ, inv_smul_eq_iff.mpr (arithFrobC_smul_jqN q κ N).symm]
  have hEq : uK.eqLocusField (Φ.toRingHom.comp rK) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hTa : ∀ a : κ, algebraMap κ (↥(modularFunctionFieldC κ N)) a ∈ (uK.eqLocusField (Φ.toRingHom.comp rK)).map rK := fun a =>
      ⟨algebraMap (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) (FractionRing (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q))) (a ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] (1 : ↥(IgusaScheme.chartAlgFin N q))), hga a, by rw [hrK, hrκ]⟩
    have hT : Subfield.toIntermediateField ((uK.eqLocusField (Φ.toRingHom.comp rK)).map rK) hTa = ⊤ := by
      rw [eq_top_iff, ← adjoin_jGens_eq_top κ N, IntermediateField.adjoin_le_iff]
      rintro y (rfl | rfl)
      · exact ⟨_, hgj, by rw [hrK, hrj]⟩
      · exact ⟨_, hgN, by rw [hrK, hrjN]⟩
    have hx : rK x ∈ Subfield.toIntermediateField ((uK.eqLocusField (Φ.toRingHom.comp rK)).map rK) hTa := by
      rw [hT]; exact IntermediateField.mem_top
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← rK.injective hyx]
  intro z
  have hz : algebraMap (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q)) (FractionRing (κ ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin N q))) z ∈ uK.eqLocusField (Φ.toRingHom.comp rK) :=
    hEq ▸ Subfield.mem_top _
  rw [← hu, ← hv]
  exact hz

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem fromSpecStalk_comp_eq_of_chart (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [Algebra (DRLevel.R q) κ]
    (M : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    [IsIso e] (heM : e ≫ pullback.snd _ _ = M.toBase)
    [hMne : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q)
      (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))]
    (hMpin : ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
        let readb : ↥(modularFunctionFieldC κ N₀) :=
          M.ffEquiv.symm
            (M.C.germToFunctionField
              ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
              (((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
                (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))))
        ((b = IgusaScheme.jChartFin N₀ q → readb = jGeomGen κ N₀) ∧
          (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq → readb = jNGeomGen κ N₀)))
    (θ₀ : DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) ⟶ DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (Φfin : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[κ] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))
    (hsq : chart0' (N₀ := N₀) (q := q) κ ≫ θ₀ = Spec.map (CommRingCat.ofHom Φfin.toRingHom) ≫ chart0' (N₀ := N₀) (q := q) κ)
    (hΦfin : ∀ b, Φfin ((1 : κ) ⊗ₜ[DRLevel.R q] b) = ((1 : κ) ⊗ₜ[DRLevel.R q] b) ^ q)
    (Φ : ↥(modularFunctionFieldC κ N₀) →ₐ[κ] ↥(modularFunctionFieldC κ N₀))
    (hΦ : ∀ f, Φ f = ((arithFrobC q κ N₀)⁻¹ • f) ^ q) :
    M.C.fromSpecStalk (genericPoint M.C) ≫ (e ≫ θ₀ ≫ inv e) =
      Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (Φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
        M.C.fromSpecStalk (genericPoint M.C) := by

  obtain ⟨c', hc'def⟩ : ∃ c' : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) ⟶ M.C,
      c' = chart0' (N₀ := N₀) (q := q) κ ≫ inv e := ⟨_, rfl⟩
  haveI hc'oi : IsOpenImmersion c' := hc'def ▸ inferInstance
  have hc'θ : c' ≫ (e ≫ θ₀ ≫ inv e) = Spec.map (CommRingCat.ofHom Φfin.toRingHom) ≫ c' := by
    simp only [hc'def, Category.assoc, IsIso.inv_hom_id_assoc]
    rw [reassoc_of% hsq]
  have hc'range : Set.range c'.base = e.base ⁻¹' ((pullback.fst (DRLevel.toBase0 N₀ q)
      (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))).base ⁻¹' Set.range (IgusaScheme.ιFin N₀ q).base) := by
    rw [hc'def, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      show Set.range (chart0' (N₀ := N₀) (q := q) κ).base = _ from
        congrArg SetLike.coe (opensRange_chart0' (N₀ := N₀) (q := q) κ)]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_preimage, Set.mem_preimage, apply_inv_apply]
      exact hy
    · intro hx
      exact ⟨e.base x, hx, inv_apply_apply e x⟩

  have hWeq : c' ''ᵁ ⊤ = (e ≫ pullback.fst (DRLevel.toBase0 N₀ q)
      (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤) := by
    apply TopologicalSpace.Opens.ext
    simp only [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp,
      TopologicalSpace.Opens.map_coe, Set.preimage_comp, hc'range]
  have hW : IsAffineOpen (c' ''ᵁ ⊤) := (isAffineOpen_top _).image_of_isOpenImmersion _
  have hηW : genericPoint M.C ∈ c' ''ᵁ ⊤ := by
    change genericPoint M.C ∈ ((c' ''ᵁ ⊤ : M.C.Opens) : Set M.C)
    rw [(genericPoint_spec M.C).mem_open_set_iff (c' ''ᵁ ⊤).isOpen]
    obtain ⟨⟨x, hx⟩⟩ := hMne
    exact ⟨x, trivial, hWeq ▸ hx⟩

  have hfs : M.C.fromSpecStalk (genericPoint M.C) =
      Spec.map (M.C.presheaf.germ _ (genericPoint M.C) hηW) ≫ hW.fromSpec :=
    (hW.fromSpecStalk_eq_fromSpecStalk hηW).symm
  have hfromSpec : hW.fromSpec =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)))).inv ≫
        (c'.appIso ⊤).inv) ≫ c' := by
    have h1 : Spec.map (c'.appLE (c' ''ᵁ ⊤) ⊤ (le_of_eq (c'.preimage_image_eq ⊤).symm)) ≫ hW.fromSpec =
        (isAffineOpen_top (Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))))).fromSpec ≫ c' :=
      IsAffineOpen.SpecMap_appLE_fromSpec _ hW (isAffineOpen_top _) _
    have h2 : (isAffineOpen_top (Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))))).fromSpec =
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)))).inv := by
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    have h3 : c'.appLE (c' ''ᵁ ⊤) ⊤ (le_of_eq (c'.preimage_image_eq ⊤).symm) = (c'.appIso ⊤).hom :=
      (Scheme.Hom.appIso_hom' _ _).symm
    rw [h3, h2] at h1
    rw [Spec.map_comp, Category.assoc, ← h1, ← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]

  set h'' : M.C.presheaf.stalk (genericPoint M.C) ⟶ M.C.presheaf.stalk (genericPoint M.C) :=
    CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (Φ.toRingHom.comp M.ffEquiv.symm.toRingHom)) with hh''
  obtain ⟨δ, hδ⟩ : ∃ δ : (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) ⟶ Γ(M.C, c' ''ᵁ ⊤), δ = (Scheme.ΓSpecIso (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)))).inv ≫ (c'.appIso ⊤).inv := ⟨_, rfl⟩
  rw [← hδ] at hfromSpec

  have key : CommRingCat.ofHom Φfin.toRingHom ≫ δ ≫ M.C.presheaf.germ _ (genericPoint M.C) hηW =
      δ ≫ M.C.presheaf.germ _ (genericPoint M.C) hηW ≫ h'' := by

    have hc'base : c' ≫ M.toBase = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q)))) := by
      rw [hc'def, Category.assoc, ← heM, IsIso.inv_hom_id_assoc, chart0'_eq]
      exact pullback.lift_snd _ _ _
    have hδκ : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))) ≫ δ =
        (Scheme.ΓSpecIso (CommRingCat.of κ)).inv ≫ M.toBase.appTop ≫ M.C.presheaf.map (homOfLE le_top).op := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp, Spec.map_comp, ← hc'base, ← Category.assoc (Spec.map δ), ← hfromSpec,
        ← hW.fromSpec_toSpecΓ]
      simp only [Category.assoc]
      rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

    have hc'fst : c' ≫ e ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom) ≫ IgusaScheme.ιFin N₀ q := by
      rw [hc'def, Category.assoc, IsIso.inv_hom_id_assoc, chart0'_eq]
      exact pullback.lift_fst _ _ _
    have hU : IsAffineOpen ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤) := (isAffineOpen_top _).image_of_isOpenImmersion _
    have hle : c' ''ᵁ ⊤ ≤ (e ≫ pullback.fst (DRLevel.toBase0 N₀ q)
        (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤) := hWeq.le
    have hδb : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom ≫ δ =
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv ≫ ((IgusaScheme.ιFin N₀ q).appIso ⊤).inv) ≫
          (e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))).appLE _ _ hle := by
      apply Spec.map_injective
      rw [← cancel_mono (IgusaScheme.ιFin N₀ q), Spec.map_comp, Category.assoc, ← hc'fst, ← Category.assoc (Spec.map δ),
        ← hfromSpec, Spec.map_comp, Category.assoc, ← fromSpec_image_top (IgusaScheme.ιFin N₀ q) hU,
        IsAffineOpen.SpecMap_appLE_fromSpec _ hU hW hle]

    haveI : IsIso δ := by rw [hδ]; infer_instance
    obtain ⟨r, hrdef⟩ : ∃ r : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q) →+* ↥(modularFunctionFieldC κ N₀),
        r = M.ffEquiv.symm.toRingHom.comp (δ ≫ M.C.presheaf.germ _ (genericPoint M.C) hηW).hom := ⟨_, rfl⟩
    have hr : Function.Injective r := by
      rw [hrdef, RingHom.coe_comp]
      refine M.ffEquiv.symm.injective.comp ?_
      rw [CommRingCat.hom_comp, RingHom.coe_comp]
      exact (@Scheme.germToFunctionField_injective M.C _ (c' ''ᵁ ⊤) ⟨⟨_, hηW⟩⟩).comp (ConcreteCategory.bijective_of_isIso δ).1
    have hrκ : ∀ a : κ, r (a ⊗ₜ[DRLevel.R q] 1) = algebraMap κ _ a := by
      intro a
      apply M.ffEquiv.injective
      rw [M.ffEquiv_algebraMap, hrdef]
      change M.ffEquiv (M.ffEquiv.symm _) = _
      rw [RingEquiv.apply_symm_apply]
      have := congrArg (fun φ => (φ ≫ M.C.presheaf.germ _ (genericPoint M.C) hηW).hom a) hδκ
      simp only [Category.assoc, TopCat.Presheaf.germ_res'] at this
      simpa [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
        AlgebraicCurve.baseToFunctionField] using this
    have hrb : ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q), r ((1 : κ) ⊗ₜ[DRLevel.R q] b) =
        M.ffEquiv.symm (M.C.germToFunctionField
          ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) ⁻¹ᵁ
            ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
          (((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))).app
            ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
            (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b)))) := by
      intro b
      rw [hrdef]
      have := congrArg (fun φ => (φ ≫ M.C.presheaf.germ _ (genericPoint M.C) hηW).hom b) hδb
      simp only [Category.assoc, Scheme.Hom.appLE, TopCat.Presheaf.germ_res'] at this
      simp only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp]
      first | simpa [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeRight_apply, Scheme.germToFunctionField] using this | (have h_1 := this; simp [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeRight_apply, Scheme.germToFunctionField] at h_1; exact h_1) | (have h_1 := this; simp [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeRight_apply, Scheme.germToFunctionField] at h_1 ⊢; exact h_1) | exact (this)
    have hrj : r ((1 : κ) ⊗ₜ[DRLevel.R q] IgusaScheme.jChartFin N₀ q) = ⟨jqModC κ, jqModC_mem κ N₀⟩ := by
      rw [hrb]; exact (hMpin _).1 rfl
    obtain ⟨bN, hbN⟩ : ∃ bN : ↥(IgusaScheme.chartAlgFin N₀ q), ((bN : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) =
        qExpand ℚ N₀ jq :=
      ⟨⟨_, (IgusaScheme.jqN_mem_chartAlgFin_and_jFull_mem_chartAlg_jqN N₀ q).1⟩, rfl⟩
    have hrjN : r ((1 : κ) ⊗ₜ[DRLevel.R q] bN) = ⟨jqNModC κ N₀, jqNModC_mem κ N₀⟩ := by
      rw [hrb]; exact (hMpin _).2 hbN
    have hcomm := frob_comm_of_pins q κ N₀ r hr hrκ hrj bN hrjN Φfin hΦfin Φ hΦ

    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    have h1 := hcomm z
    rw [hrdef] at h1
    have h2 := congrArg M.ffEquiv h1
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at h2
    first | simpa [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hh''] using h2 | (have h_1 := h2; simp [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hh''] at h_1; exact h_1) | (have h_1 := h2; simp [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hh''] at h_1 ⊢; exact h_1) | exact (h2)

  show M.C.fromSpecStalk (genericPoint M.C) ≫ (e ≫ θ₀ ≫ inv e) = Spec.map h'' ≫ M.C.fromSpecStalk (genericPoint M.C)
  rw [hfs, hfromSpec, Category.assoc, Category.assoc, hc'θ]
  have k2 := congrArg Spec.map key
  rw [Spec.map_comp, Spec.map_comp, Spec.map_comp, Spec.map_comp] at k2
  simp only [Category.assoc] at k2
  rw [reassoc_of% k2]

end ModularCurve.DRLevel.FrobPlace

open ModularCurve.DRLevel.FrobPlace in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

    (w : DRLevel.X N₀ q ≅ DRLevel.X N₀ q) (hw : w.hom ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (theta : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ≃ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (htheta : ∀ b, ((theta b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) =
      atkinLehnerInvolutionFull N₀ q (b : ↥(modularFunctionFieldFull (N₀ * q))))
    (hwchart : IgusaScheme.ιFin (N₀ * q) q ≫ w.hom =
      Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)

    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (iota0 : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hiota : ∀ b, (((iota0 b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hpichart : IgusaScheme.ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ IgusaScheme.ιFin N₀ q)

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)

    (M : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) [IsIso e]
    (heM : e ≫ pullback.snd _ _ = M.toBase)
    [hMne : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ
      ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))]
    (hMpin : ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
        let readb : ↥(modularFunctionFieldC κ N₀) :=
          M.ffEquiv.symm
            (M.C.germToFunctionField
              ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
              (((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
                (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))))
        ((b = IgusaScheme.jChartFin N₀ q → readb = jGeomGen κ N₀) ∧
          (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq → readb = jNGeomGen κ N₀)))

    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ))
    (hcomp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hcomp_ci : ∀ i, IsClosedImmersion (comp i))
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π toκ = 𝟙 _)
    (hcomp_w : comp 0 ≫ DRLevel.fibreMap w.hom hw toκ = comp 1) :
    ∀ P : closedPoints M.C,
      ∃ h : (inv e).base ((e ≫ comp 1 ≫ DRLevel.fibreMap0 π toκ).base P.1) ∈ closedPoints M.C,
        M.placeOfPoint ⟨_, h⟩ = arithFrobC q κ N₀ • M.placeOfPoint P := by
  intro P

  obtain ⟨_inst, rfl⟩ : ∃ _i : Algebra (DRLevel.R q) κ, @algebraMap (DRLevel.R q) κ _ _ _i = toκ :=
    ⟨toκ.toAlgebra, rfl⟩

  let θ : M.C ⟶ M.C := e ≫ comp 1 ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) ≫ inv e
  have hθP : (inv e).base ((e ≫ comp 1 ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ)).base P.1) = θ.base P.1 := rfl

  obtain ⟨Φ, hΦ, hfin⟩ : ∃ Φ : ↥(modularFunctionFieldC κ N₀) →ₐ[κ] ↥(modularFunctionFieldC κ N₀),
      (∀ f, Φ f = ((arithFrobC q κ N₀)⁻¹ • f) ^ q) ∧ FiniteAlong κ Φ :=
    ⟨relFrob q κ N₀, relFrob_apply q κ N₀,
      finiteAlong_relFrob q κ N₀ fun h => hqN ((CharP.cast_eq_zero_iff κ q N₀).mp h)⟩

  obtain ⟨σ0, hσ0, hsq0⟩ := ModularCurve.DRLevel.exists_retraction_chart_comp_zero_eq N₀ q hqN π iota0 hiota hpichart κ
    (chart0 (N₀ := N₀) (q := q) κ) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (chart (N₀ := N₀) (q := q) κ) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    comp hcomp_over hcomp_ci hcomp_pi

  have hC : ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
      (σ0.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom))
        ((1 : κ) ⊗ₜ[DRLevel.R q] iota0 b) = ((1 : κ) ⊗ₜ[DRLevel.R q] b) ^ q := by
    have := ModularCurve.IgusaScheme.retraction_one_tmul_iota_eq_pow_of_not_dvd N₀ q hqN κ iota0 hiota theta htheta
      ![σ0, σ0.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)]
      (fun z => by simpa using hσ0 z) (fun z => by simp)
    simpa using this

  have hsq1 : chart0 (N₀ := N₀) (q := q) κ ≫ comp 1 ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) =
      Spec.map (CommRingCat.ofHom ((σ0.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).comp
        (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0)).toRingHom) ≫ chart0 (N₀ := N₀) (q := q) κ := by
    have key : chart (N₀ := N₀) (q := q) κ ≫ DRLevel.fibreMap w.hom hw (algebraMap (DRLevel.R q) κ) ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom) ≫
            chart0 (N₀ := N₀) (q := q) κ :=
      (chart_fibreMap_assoc (N₀ := N₀) (q := q) κ w.hom hw theta.toAlgHom hwchart _).trans
        (congrArg _ (chart_fibreMap0 (N₀ := N₀) (q := q) κ π iota0 hpichart))
    rw [← hcomp_w, Category.assoc, reassoc_of% hsq0, key, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl

  have hθgen : M.C.fromSpecStalk (genericPoint M.C) ≫ θ =
      Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (Φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
        M.C.fromSpecStalk (genericPoint M.C) := by
    have hsq1' : chart0' (N₀ := N₀) (q := q) κ ≫ comp 1 ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) =
        Spec.map (CommRingCat.ofHom ((σ0.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).comp
          (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0)).toRingHom) ≫ chart0' (N₀ := N₀) (q := q) κ := by
      rw [chart0'_eq]; exact hsq1
    have := fromSpecStalk_comp_eq_of_chart (N₀ := N₀) (q := q) κ M e heM hMpin
      (comp 1 ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ))
      ((σ0.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).comp (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0))
      hsq1' (fun b => by simpa using hC b) Φ hΦ
    simpa only [θ, Category.assoc] using this

  obtain ⟨h, hP⟩ := AlgebraicCurve.CurveModel.placeOfPoint_eq_smul_of_fromSpecStalk_comp_eq_frobenius q M
    (arithFrobC q κ N₀) Φ hΦ hfin θ hθgen P
  refine ⟨hθP ▸ h, ?_⟩
  convert hP using 3

end S_ModularCurve_DRLevel_placeOfPoint_comp_one_fibreMap0_eq_arithFrobC_smul
end P2MW
export P2MW.S_ModularCurve_DRLevel_placeOfPoint_comp_one_fibreMap0_eq_arithFrobC_smul (solution)
