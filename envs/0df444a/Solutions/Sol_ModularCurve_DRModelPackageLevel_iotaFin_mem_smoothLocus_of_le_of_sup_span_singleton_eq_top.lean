-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/352fe3ac-9368-5a67-9def-0567848ba49a

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_comp_zero
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure"
p2m_attr_erase "instance" "instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "instance" "ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero"
p2m_attr_erase "simp" "ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_dCoord WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.veluWSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel.neZero_mul DRModelPackageLevel IgusaScheme.chartAlgFin IgusaScheme IgusaScheme.ιFin IgusaScheme.ιFin_igusaTo"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "neZero_mul mk comp smoothLocus mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_comp_zero"
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

namespace SmoothAux

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔓 : DRModelPackageLevel N₀ q hqN)

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

section Smooth

variable (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
  (hdict : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ)
    (y : ↥(fibre (N₀ := N₀) toκ)) (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)),
    (pullback.fst (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base y = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 →
    v ∉ 𝔮.asIdeal → y ∈ Set.range (𝔓.comp κ toκ 0).base ∧ y ∉ Set.range (𝔓.comp κ toκ 1).base)

structure GeomPt (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) where
  κ : Type
  [field : Field κ]
  [charP : CharP κ q]
  [algClosed : IsAlgClosed κ]
  toκ : R q →+* κ
  y : ↥(fibre (N₀ := N₀) toκ)
  fst_y : (pullback.fst (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base y = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮

attribute [scoped instance] GeomPt.field GeomPt.charP GeomPt.algClosed

def geomPt (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) [𝔮.asIdeal.IsMaximal] (hq𝔮 : (q : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) ∈ 𝔮.asIdeal) :
    GeomPt (N₀ := N₀) (q := q) 𝔮 := by
  letI : Field (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ 𝔮.asIdeal) := Ideal.Quotient.field 𝔮.asIdeal
  let κ := AlgebraicClosure (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ 𝔮.asIdeal)
  let φA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →+* κ := (algebraMap (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ 𝔮.asIdeal) κ).comp (Ideal.Quotient.mk 𝔮.asIdeal)
  let toκ : R q →+* κ := φA.comp (algebraMap (R q) ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
  haveI : CharP κ q := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)]
    have : φA (q : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) = 0 := by
      simp only [φA, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hq𝔮, map_zero]
    simpa using this
  let xκ : Spec (CommRingCat.of κ) ⟶ X N₀ q := Spec.map (CommRingCat.ofHom φA) ≫ IgusaScheme.ιFin (N₀ * q) q
  have hx : xκ ≫ toBase N₀ q = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom toκ) := by
    simp only [xκ, Category.assoc, Category.id_comp]
    erw [IgusaScheme.ιFin_igusaTo]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine { κ := κ, toκ := toκ, y := (pullback.lift xκ (𝟙 _) hx).base (IsLocalRing.closedPoint κ), fst_y := ?_ }
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  simp only [xκ, Scheme.Hom.comp_apply]
  congr 1
  apply PrimeSpectrum.ext
  change Ideal.comap φA (IsLocalRing.maximalIdeal κ) = 𝔮.asIdeal
  rw [IsLocalRing.maximalIdeal_eq_bot (R := κ), ← RingHom.ker_eq_comap_bot]
  simp only [φA]
  rw [RingHom.ker_comp_of_injective _ (FaithfulSMul.algebraMap_injective _ _), Ideal.mk_ker]

include hdict in

theorem ιFin_mem_smoothLocus_of_isMaximal (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) [𝔮.asIdeal.IsMaximal]
    (hq𝔮 : (q : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) ∈ 𝔮.asIdeal) (hv : v ∉ 𝔮.asIdeal) :
    (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 ∈ (𝔓.smoothLocus : Set ↥(X N₀ q)) := by
  classical
  let P := geomPt (N₀ := N₀) 𝔮 hq𝔮
  obtain ⟨h0, h1⟩ := hdict P.κ P.toκ P.y 𝔮 P.fst_y hv
  have := (mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_comp_zero N₀ q hqN 𝔓 P.κ P.toκ P.y h0 h1).1
  rwa [P.fst_y] at this

end Smooth

theorem natCast_mem_of_isMaximal (I : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    [Module.Finite (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)]
    (M : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) [hM : M.IsMaximal] (hIM : I ≤ M) :
    (q : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) ∈ M := by
  haveI : Algebra.IsIntegral (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I) := Algebra.IsIntegral.of_finite _ _
  haveI := GaloisRep.ratLocalizedAt.isLocalRing (p := q) Fact.out
  have hcomap : Ideal.comap (Ideal.Quotient.mk I) (M.map (Ideal.Quotient.mk I)) = M := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.2 hIM]
  have hne : M.map (Ideal.Quotient.mk I) ≠ ⊤ := fun h => hM.ne_top (by rw [← hcomap, h, Ideal.comap_top])
  haveI : (M.map (Ideal.Quotient.mk I)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hM).resolve_left hne
  have hP := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R q) (M.map (Ideal.Quotient.mk I))
  have hPeq : Ideal.comap (algebraMap (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)) (M.map (Ideal.Quotient.mk I)) =
      Ideal.span {(q : R q)} := by
    rw [IsLocalRing.eq_maximalIdeal hP, GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast q Fact.out]
  have hq : algebraMap (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I) q ∈ M.map (Ideal.Quotient.mk I) := by
    rw [← Ideal.mem_comap, hPeq]; exact Ideal.mem_span_singleton_self _
  rw [← hcomap, Ideal.mem_comap, map_natCast]
  rwa [map_natCast] at hq

end SmoothAux
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top.ModularCurve.DRModelPackageLevel.SmoothAux"

end ModularCurve.DRModelPackageLevel
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top.ModularCurve.DRModelPackageLevel.SmoothAux P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top.ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top.ModularCurve.DRModelPackageLevel"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top.ModularCurve.DRModelPackageLevel.SmoothAux P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top.ModularCurve.DRModelPackageLevel.SmoothAux P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top.ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top.ModularCurve.DRModelPackageLevel"

open _root_.ModularCurve.DRModelPackageLevel _root_.P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top.ModularCurve.DRModelPackageLevel ModularCurve.DRModelPackageLevel.SmoothAux in
attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hdict : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ)
      (y : ↥(fibre (N₀ := N₀) toκ)) (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)),
      (pullback.fst (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base y = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 →
      v ∉ 𝔮.asIdeal → y ∈ Set.range (𝔓.comp κ toκ 0).base ∧ y ∉ Set.range (𝔓.comp κ toκ 1).base)
    (I : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) [Module.Finite (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)]
    (hIv : I ⊔ Ideal.span {v} = ⊤)
    (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (h𝔮 : I ≤ 𝔮.asIdeal) :
    (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 ∈ (𝔓.smoothLocus : Set ↥(X N₀ q)) := by
  classical
  obtain ⟨Mx, hMx, hle⟩ := Ideal.exists_le_maximal 𝔮.asIdeal 𝔮.isPrime.ne_top
  let 𝔮₀ : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := ⟨Mx, hMx.isPrime⟩
  haveI : 𝔮₀.asIdeal.IsMaximal := hMx
  have hq0 : (q : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) ∈ 𝔮₀.asIdeal := natCast_mem_of_isMaximal I Mx (h𝔮.trans hle)
  have hv0 : v ∉ 𝔮₀.asIdeal := fun hv =>
    hMx.ne_top (top_le_iff.1 (hIv ▸ sup_le (h𝔮.trans hle) ((Ideal.span_singleton_le_iff_mem _).2 hv)))
  have h0 := ιFin_mem_smoothLocus_of_isMaximal 𝔓 v hdict 𝔮₀ hq0 hv0
  have hspec : 𝔮 ⤳ 𝔮₀ := (PrimeSpectrum.le_iff_specializes 𝔮 𝔮₀).1 hle
  exact (hspec.map (IgusaScheme.ιFin (N₀ * q) q).continuous).mem_open 𝔓.smoothLocus.isOpen h0

end S_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top (solution)
