-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.fibreMap_w_mem_diff_connectedComponentIn_and_sectionFibre_cuspZero_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/6717014b-4c37-525e-a57b-d9e35473e8ab

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Theorems.Thm_AlgebraicGeometry_RelPicard_preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
import Theorems.Thm_ModularCurve_DRModelPackageLevel_finite_crossings
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegral_pullback_igusaTo_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_fibreMap_w_mem_diff_connectedComponentIn_and_sectionFibre_cuspZero_mem
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"

namespace FarLevelAux

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔓 : DRModelPackageLevel N₀ q hqN)
  {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)

theorem fibreMap_fst (φ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q) :
    fibreMap φ hφ toκ ≫ pullback.fst (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) =
      pullback.fst (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ≫ φ := by
  unfold fibreMap
  rw [pullback.lift_fst]

theorem fibreMap_snd (φ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q) :
    fibreMap φ hφ toκ ≫ pullback.snd (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) =
      pullback.snd (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) := by
  unfold fibreMap
  rw [pullback.lift_snd, Category.comp_id]

include 𝔓 in

theorem preimage_w_smoothLocus : 𝔓.w.hom ⁻¹ᵁ 𝔓.smoothLocus = 𝔓.smoothLocus := by

  have key : ∀ V : (X N₀ q).Opens, Smooth (V.ι ≫ toBase N₀ q) → Smooth ((𝔓.w.hom ⁻¹ᵁ V).ι ≫ toBase N₀ q) := by
    intro V hV
    have : (𝔓.w.hom ⁻¹ᵁ V).ι ≫ toBase N₀ q = (𝔓.w.hom ∣_ V) ≫ V.ι ≫ toBase N₀ q := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, 𝔓.w_over]
    rw [this]
    haveI := hV
    infer_instance
  apply le_antisymm
  · exact 𝔓.smoothLocus_maximal _ (key _ 𝔓.smoothLocus_relDim.smooth)
  ·
    have hww : 𝔓.w.hom ⁻¹ᵁ (𝔓.w.hom ⁻¹ᵁ 𝔓.smoothLocus) = 𝔓.smoothLocus := by
      rw [← Scheme.Hom.comp_preimage, 𝔓.w_invol]; rfl
    calc 𝔓.smoothLocus = 𝔓.w.hom ⁻¹ᵁ (𝔓.w.hom ⁻¹ᵁ 𝔓.smoothLocus) := hww.symm
      _ ≤ 𝔓.w.hom ⁻¹ᵁ 𝔓.smoothLocus :=
        𝔓.w.hom.preimage_mono (𝔓.smoothLocus_maximal _ (key _ 𝔓.smoothLocus_relDim.smooth))

theorem preimage_fibreMap_w_traceU :
    fibreMap 𝔓.w.hom 𝔓.w_over toκ ⁻¹ᵁ (pullback.fst (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus) =
      pullback.fst (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus := by
  rw [← Scheme.Hom.comp_preimage, fibreMap_fst, Scheme.Hom.comp_preimage, preimage_w_smoothLocus]

theorem sectionFibre_εinf_comp_fibreMap_w :
    sectionFibre 𝔓.εinf toκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over toκ = sectionFibre 𝔓.εzero toκ := by
  apply pullback.hom_ext
  · rw [Category.assoc, fibreMap_fst]
    unfold sectionFibre
    rw [pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc, 𝔓.w_sections]
  · rw [Category.assoc, fibreMap_snd]
    unfold sectionFibre
    rw [pullback.lift_snd, pullback.lift_snd]

theorem sectionFibre_mem_traceU (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q))
    (hε : Set.range ε.1.base ⊆ (𝔓.smoothLocus : Set (X N₀ q))) :
    (sectionFibre ε toκ).base (IsLocalRing.closedPoint κ) ∈
      ((pullback.fst (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus : (fibre (N₀ := N₀) toκ).Opens) :
        Set ↥(fibre (N₀ := N₀) toκ)) := by
  show (sectionFibre ε toκ ≫ pullback.fst (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (IsLocalRing.closedPoint κ) ∈
    (𝔓.smoothLocus : Set (X N₀ q))
  unfold sectionFibre
  rw [pullback.lift_fst]
  exact hε ⟨(Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint κ), rfl⟩

theorem not_range_comp_subset (i j : Fin 2) (hij : i ≠ j) :
    ¬ Set.range (𝔓.comp κ toκ i).base ⊆ Set.range (𝔓.comp κ toκ j).base := by
  intro hsub

  letI : Algebra (R q) κ := toκ.toAlgebra
  haveI : IsIntegral ↑(fibre0 (N₀ := N₀) toκ) := IgusaScheme.isIntegral_pullback_igusaTo_of_charP N₀ q hqN κ
  haveI : SmoothOfRelativeDimension 1 (igusaTo N₀ q) := (IgusaScheme.isProper_and_smooth_and_geometricallyIntegral N₀ q hqN).2.1
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hinf : (Set.univ : Set ↥(fibre0 (N₀ := N₀) toκ)).Infinite :=
    (AlgebraicCurve.infinite_setOf_isClosed_singleton (pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))).mono
      (Set.subset_univ _)

  haveI : Finite ↥(pullback (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)) := 𝔓.finite_crossings toκ

  apply hinf

  have hlift : ∀ z : ↥(fibre0 (N₀ := N₀) toκ), ∃ c : ↥(pullback (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)),
      (if i = 0 then (pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)).base c else (pullback.snd (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)).base c) = z := by
    intro z
    obtain ⟨z', hz'⟩ := hsub ⟨z, rfl⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    ·
      obtain ⟨c, hc1, hc2⟩ := Scheme.Pullback.exists_preimage_pullback z z' hz'.symm
      exact ⟨c, by simpa using hc1⟩
    · obtain ⟨c, hc1, hc2⟩ := Scheme.Pullback.exists_preimage_pullback z' z hz'
      exact ⟨c, by simpa using hc2⟩
    · exact absurd rfl hij
  choose g hg using hlift
  haveI : Finite ↥(fibre0 (N₀ := N₀) toκ) := by
    refine Finite.of_injective g ?_
    intro a b hab
    have := hg a
    rw [show g a = g b from hab, hg b] at this
    exact this.symm
  exact Set.finite_univ_iff.mpr ‹_›

end FarLevelAux

open FarLevelAux in
theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ) :
    (∀ y : ↥(DRLevel.fibre (N₀ := N₀) toκ),
      y ∈ connectedComponentIn ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus :
          (DRLevel.fibre (N₀ := N₀) toκ).Opens) : Set ↥(DRLevel.fibre (N₀ := N₀) toκ))
          ((DRLevel.sectionFibre 𝔓.εinf toκ).base (IsLocalRing.closedPoint κ)) →
      (DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over toκ).base y ∈
        ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus :
          (DRLevel.fibre (N₀ := N₀) toκ).Opens) : Set ↥(DRLevel.fibre (N₀ := N₀) toκ)) \
        connectedComponentIn ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus :
          (DRLevel.fibre (N₀ := N₀) toκ).Opens) : Set ↥(DRLevel.fibre (N₀ := N₀) toκ))
          ((DRLevel.sectionFibre 𝔓.εinf toκ).base (IsLocalRing.closedPoint κ))) ∧
    (DRLevel.sectionFibre 𝔓.εzero toκ).base (IsLocalRing.closedPoint κ) ∈
      ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus :
        (DRLevel.fibre (N₀ := N₀) toκ).Opens) : Set ↥(DRLevel.fibre (N₀ := N₀) toκ)) \
      connectedComponentIn ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus :
        (DRLevel.fibre (N₀ := N₀) toκ).Opens) : Set ↥(DRLevel.fibre (N₀ := N₀) toκ))
        ((DRLevel.sectionFibre 𝔓.εinf toκ).base (IsLocalRing.closedPoint κ)) := by

  set UU : Set ↥(DRLevel.fibre (N₀ := N₀) toκ) :=
    ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus :
      (DRLevel.fibre (N₀ := N₀) toκ).Opens) : Set ↥(DRLevel.fibre (N₀ := N₀) toκ)) with hUU
  set pinf := (DRLevel.sectionFibre 𝔓.εinf toκ).base (IsLocalRing.closedPoint κ) with hpinf
  set p0 := (DRLevel.sectionFibre 𝔓.εzero toκ).base (IsLocalRing.closedPoint κ) with hp0

  obtain ⟨hPr, hSm, hGi⟩ := IgusaScheme.isProper_and_smooth_and_geometricallyIntegral N₀ q hqN
  haveI := hPr; haveI := hSm; haveI := hGi
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI := 𝔓.comp_isClosedImmersion κ toκ 0
  haveI := 𝔓.comp_isClosedImmersion κ toκ 1
  haveI := 𝔓.flat; haveI := 𝔓.lfp; haveI := 𝔓.isProper
  haveI : Smooth (𝔓.smoothLocus.ι ≫ toBase N₀ q) := 𝔓.smoothLocus_relDim.smooth

  obtain ⟨-, hcc0, hcc1, -, -⟩ :=
    RelPicard.preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves (toBase N₀ q) 𝔓.smoothLocus
      𝔓.smoothLocus_maximal (Spec.map (CommRingCat.ofHom toκ)) (𝔓.fibre_reduced κ toκ)
      (pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) (pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      ⟨𝔓.comp κ toκ 0, 𝔓.comp_over κ toκ 0⟩ ⟨𝔓.comp κ toκ 1, 𝔓.comp_over κ toκ 1⟩
      (𝔓.comp_jointly_surjective κ toκ)
      (not_range_comp_subset 𝔓 toκ 0 1 (by decide)) (not_range_comp_subset 𝔓 toκ 1 0 (by decide))
      pinf (𝔓.εinf_mem_comp0 κ toκ ⟨_, rfl⟩) (sectionFibre_mem_traceU 𝔓 toκ 𝔓.εinf 𝔓.εinf_mem_smoothLocus)

  have hfar : ∀ z : ↥(DRLevel.fibre (N₀ := N₀) toκ), z ∈ Set.range (𝔓.comp κ toκ 1).base → z ∈ UU →
      z ∈ UU \ connectedComponentIn UU pinf := by
    intro z hz1 hzU
    have : z ∈ Set.range (𝔓.comp κ toκ 1).base ∩ UU := ⟨hz1, hzU⟩
    rwa [hcc1] at this
  refine ⟨fun y hy => ?_, ?_⟩
  ·
    have hy' : y ∈ Set.range (𝔓.comp κ toκ 0).base ∩ UU := by rw [hcc0]; exact hy
    obtain ⟨⟨y0, rfl⟩, hyU⟩ := hy'
    apply hfar
    ·
      refine ⟨y0, ?_⟩
      rw [← 𝔓.comp_w κ toκ]
      rfl
    ·
      show fibreMap 𝔓.w.hom 𝔓.w_over toκ ((𝔓.comp κ toκ 0).base y0) ∈ UU
      rw [hUU, ← preimage_fibreMap_w_traceU 𝔓 toκ] at hyU
      exact hyU
  ·
    apply hfar
    · exact 𝔓.εzero_mem_comp1 κ toκ ⟨_, rfl⟩
    · exact sectionFibre_mem_traceU 𝔓 toκ 𝔓.εzero 𝔓.εzero_mem_smoothLocus

end S_ModularCurve_DRModelPackageLevel_fibreMap_w_mem_diff_connectedComponentIn_and_sectionFibre_cuspZero_mem
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_fibreMap_w_mem_diff_connectedComponentIn_and_sectionFibre_cuspZero_mem (solution)
