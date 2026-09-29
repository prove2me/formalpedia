-- Prove2me | solution 1 for ModularCurve.DRLevel.isReduced_pullback_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/cf5c8ca1-c930-5180-88e1-97639b6cadd7

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_DRLevel_exists_retraction_chart_comp_zero_eq
import Theorems.Thm_ModularCurve_IgusaScheme_retraction_one_tmul_iota_eq_pow_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_RingHom_isReduced_quotient_ker_sup_ker_of_exists_apply_eq_pow
import Theorems.Thm_ModularCurve_DRLevel_fst_pullback_comp_mem_range_iotaFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_isReduced_pullback_comp
p2m_attr_erase "instance" "ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableNonsingular instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeRingHom AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
open scoped TensorProduct

noncomputable section

namespace F9R

private lemma isPullback_chart (M q : ℕ) [NeZero M] [Fact q.Prime] (κ : Type) [Field κ] [Algebra (DRLevel.R q) κ]
    (c : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin M q))) ⟶
      pullback (IgusaScheme.igusaTo M q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin M q))).toRingHom) ≫ IgusaScheme.ιFin M q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin M q))))) :
    IsPullback c (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin M q))).toRingHom))
      (pullback.fst _ _) (IgusaScheme.ιFin M q) := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (DRLevel.R q) κ ↥(IgusaScheme.chartAlgFin M q))

  have s : IsPullback (c ≫ pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin M q))).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))
      (IgusaScheme.ιFin M q ≫ IgusaScheme.igusaTo M q) := by
    rw [hcsnd, IgusaScheme.ιFin_igusaTo]
    exact sq
  exact IsPullback.of_right s hcfst (IsPullback.of_hasPullback _ _).flip

private lemma isOpenImmersion_chart (M q : ℕ) [NeZero M] [Fact q.Prime] (κ : Type) [Field κ] [Algebra (DRLevel.R q) κ]
    (c : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin M q))) ⟶
      pullback (IgusaScheme.igusaTo M q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin M q))).toRingHom) ≫ IgusaScheme.ιFin M q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin M q))))) :
    IsOpenImmersion c ∧ Set.range c.base = (pullback.fst (IgusaScheme.igusaTo M q)
      (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))).base ⁻¹' Set.range (IgusaScheme.ιFin M q).base := by
  have H := isPullback_chart M q κ c hcfst hcsnd
  have hc : c = H.isoPullback.hom ≫ pullback.fst _ _ := (H.isoPullback_hom_fst).symm
  refine ⟨by rw [hc]; infer_instance, ?_⟩
  rw [← Scheme.Pullback.range_fst, hc]
  ext x; constructor
  · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.hom.base y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.inv.base y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]⟩

end F9R

namespace F9R

private lemma chart_fibreMap (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (κ : Type) [Field κ] [Algebra (DRLevel.R q) κ]
    (w : DRLevel.X N₀ q ≅ DRLevel.X N₀ q) (hw : w.hom ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (theta : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ≃ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hwchart : IgusaScheme.ιFin (N₀ * q) q ≫ w.hom =
      Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (c : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ⟶
      DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hcfst : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hcsnd : c ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))))) :
    c ≫ DRLevel.fibreMap w.hom hw (algebraMap (DRLevel.R q) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom) ≫ c := by
    apply pullback.hom_ext
    · simp only [Category.assoc, DRLevel.fibreMap, pullback.lift_fst]
      rw [reassoc_of% hcfst, hwchart, hcfst]
      simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
      have hring : (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ)
            (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom.comp theta.toRingEquiv.toRingHom =
          (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ)
              (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom :=
        RingHom.ext fun b => by simp [Algebra.TensorProduct.map_tmul]
      rw [hring]
    · simp only [Category.assoc, DRLevel.fibreMap, pullback.lift_snd, Category.comp_id]
      try rw [hcsnd]
      try rw [hcsnd]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have hring : (Algebra.TensorProduct.includeLeftRingHom (R := DRLevel.R q) (A := κ)
            (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) =
          (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom.comp
            (Algebra.TensorProduct.includeLeftRingHom (R := DRLevel.R q) (A := κ)
              (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) :=
        RingHom.ext fun a => by simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeftRingHom_apply]
      rw [← hring]

private lemma chart_fibreMap0 (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (κ : Type) [Field κ] [Algebra (DRLevel.R q) κ]
    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (iota0 : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hpichart : IgusaScheme.ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ IgusaScheme.ιFin N₀ q)
    (c₀ : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) ⟶
      DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hc₀fst : c₀ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom) ≫ IgusaScheme.ιFin N₀ q)
    (hc₀snd : c₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q)))))
    (c : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ⟶
      DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hcfst : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hcsnd : c ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))))) :
    c ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom) ≫ c₀ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, DRLevel.fibreMap0, pullback.lift_fst]
      rw [reassoc_of% hcfst, hpichart, hc₀fst]
      simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
      have hring : (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ)
            (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom.comp iota0.toRingHom =
          (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ)
              (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom :=
        RingHom.ext fun b => by simp [Algebra.TensorProduct.map_tmul]
      rw [hring]
    · simp only [Category.assoc, DRLevel.fibreMap0, pullback.lift_snd, Category.comp_id]
      try rw [hcsnd]
      try rw [hc₀snd]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have hring : (Algebra.TensorProduct.includeLeftRingHom (R := DRLevel.R q) (A := κ)
            (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) =
          (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom.comp
            (Algebra.TensorProduct.includeLeftRingHom (R := DRLevel.R q) (A := κ)
              (B := ↥(IgusaScheme.chartAlgFin N₀ q))) :=
        RingHom.ext fun a => by simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeftRingHom_apply]
      rw [← hring]

end F9R

section F9HelpersSection

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace F9Helpers

private theorem algebraMap_tensor_surjective
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (hB : Function.Surjective (algebraMap A B)) (hC : Function.Surjective (algebraMap A C)) :
    Function.Surjective (algebraMap A (B ⊗[A] C)) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul b c =>
      obtain ⟨a, rfl⟩ := hB b
      obtain ⟨a', rfl⟩ := hC c
      refine ⟨a * a', ?_⟩
      rw [map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply' a',
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add u v hu hv =>
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨a', rfl⟩ := hv
      exact ⟨a + a', map_add _ _ _⟩

private theorem ker_algebraMap_tensor
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (hB : Function.Surjective (algebraMap A B)) (hC : Function.Surjective (algebraMap A C)) :
    RingHom.ker (algebraMap A (B ⊗[A] C)) =
      RingHom.ker (algebraMap A B) ⊔ RingHom.ker (algebraMap A C) := by
  classical
  set K : Ideal A := RingHom.ker (algebraMap A B) ⊔ RingHom.ker (algebraMap A C) with hK
  have hkB : RingHom.ker (Algebra.ofId A B) ≤ K := le_sup_left
  have hkC : RingHom.ker (Algebra.ofId A C) ≤ K := le_sup_right
  let eB : (A ⧸ RingHom.ker (Algebra.ofId A B)) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hB
  let eC : (A ⧸ RingHom.ker (Algebra.ofId A C)) ≃ₐ[A] C :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A C) hC
  let fB : B →ₐ[A] A ⧸ K := (Ideal.Quotient.factorₐ A hkB).comp eB.symm.toAlgHom
  let fC : C →ₐ[A] A ⧸ K := (Ideal.Quotient.factorₐ A hkC).comp eC.symm.toAlgHom
  let ψ : B ⊗[A] C →ₐ[A] A ⧸ K := Algebra.TensorProduct.productMap fB fC
  apply le_antisymm
  · intro a ha
    rw [RingHom.mem_ker] at ha
    have h1 : ψ (algebraMap A (B ⊗[A] C) a) = 0 := by rw [ha, map_zero]
    rw [AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h1
  · apply sup_le
    · intro a ha
      rw [RingHom.mem_ker] at ha ⊢
      rw [Algebra.TensorProduct.algebraMap_apply, ha, TensorProduct.zero_tmul]
    · intro a ha
      rw [RingHom.mem_ker] at ha ⊢
      rw [Algebra.TensorProduct.algebraMap_apply', ha, TensorProduct.tmul_zero]

private noncomputable def quotientKerSupKerEquivTensor
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (hB : Function.Surjective (algebraMap A B)) (hC : Function.Surjective (algebraMap A C)) :
    (A ⧸ (RingHom.ker (algebraMap A B) ⊔ RingHom.ker (algebraMap A C))) ≃ₐ[A] B ⊗[A] C :=
  (Ideal.quotientEquivAlgOfEq A (ker_algebraMap_tensor hB hC).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A (B ⊗[A] C))
      (algebraMap_tensor_surjective hB hC))

private noncomputable def pullbackCompMonoIso {𝒞 : Type*} [Category 𝒞] {X Y W Z : 𝒞}
    (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] [HasPullback f g] :
    pullback (f ≫ i) (g ≫ i) ≅ pullback f g :=
  limit.isoLimitCone ⟨_, pullbackIsPullbackOfCompMono f g i⟩

private theorem nonempty_pullback_iso_Spec_quotient_ker_sup_ker
    {A B : Type u} [CommRing A] [CommRing B]
    (σ₀ σ₁ : A →+* B) (hσ₀ : Function.Surjective σ₀) (hσ₁ : Function.Surjective σ₁)
    {Y : Scheme.{u}} (c : Spec (CommRingCat.of A) ⟶ Y) [Mono c]
    (f₀ f₁ : Spec (CommRingCat.of B) ⟶ Y)
    (h₀ : f₀ = Spec.map (CommRingCat.ofHom σ₀) ≫ c) (h₁ : f₁ = Spec.map (CommRingCat.ofHom σ₁) ≫ c) :
    Nonempty (pullback f₀ f₁ ≅ Spec (CommRingCat.of (A ⧸ (RingHom.ker σ₀ ⊔ RingHom.ker σ₁)))) := by
  classical
  subst h₀ h₁

  let i1 : pullback (Spec.map (CommRingCat.ofHom σ₀) ≫ c) (Spec.map (CommRingCat.ofHom σ₁) ≫ c) ≅
      pullback (Spec.map (CommRingCat.ofHom σ₀)) (Spec.map (CommRingCat.ofHom σ₁)) :=
    pullbackCompMonoIso _ _ c

  let e₀ : (A ⧸ RingHom.ker σ₀) ≃+* B := RingHom.quotientKerEquivOfSurjective hσ₀
  let e₁ : (A ⧸ RingHom.ker σ₁) ≃+* B := RingHom.quotientKerEquivOfSurjective hσ₁
  have fac₀ : Spec.map (CommRingCat.ofHom σ₀) =
      Spec.map e₀.toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ RingHom.ker σ₀))) := by
    rw [← Spec.map_comp]
    congr 1
  have fac₁ : Spec.map (CommRingCat.ofHom σ₁) =
      Spec.map e₁.toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ RingHom.ker σ₁))) := by
    rw [← Spec.map_comp]
    congr 1
  let i2 : pullback (Spec.map (CommRingCat.ofHom σ₀)) (Spec.map (CommRingCat.ofHom σ₁)) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ RingHom.ker σ₀))))
        (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ RingHom.ker σ₁)))) :=
    pullback.congrHom fac₀ fac₁ ≪≫
      asIso (pullback.map _ _ _ _ (Spec.map e₀.toCommRingCatIso.hom) (Spec.map e₁.toCommRingCatIso.hom) (𝟙 _)
        (by rw [Category.comp_id]) (by rw [Category.comp_id]))

  let i3 := pullbackSpecIso A (A ⧸ RingHom.ker σ₀) (A ⧸ RingHom.ker σ₁)

  have hk₀ : RingHom.ker (algebraMap A (A ⧸ RingHom.ker σ₀)) = RingHom.ker σ₀ := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  have hk₁ : RingHom.ker (algebraMap A (A ⧸ RingHom.ker σ₁)) = RingHom.ker σ₁ := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  let e : (A ⧸ (RingHom.ker σ₀ ⊔ RingHom.ker σ₁)) ≃ₐ[A]
      (A ⧸ RingHom.ker σ₀) ⊗[A] (A ⧸ RingHom.ker σ₁) :=
    (Ideal.quotientEquivAlgOfEq A (by rw [hk₀, hk₁])).trans
      (quotientKerSupKerEquivTensor (A := A) (B := A ⧸ RingHom.ker σ₀) (C := A ⧸ RingHom.ker σ₁)
        Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective)
  let i4 : Spec (CommRingCat.of ((A ⧸ RingHom.ker σ₀) ⊗[A] (A ⧸ RingHom.ker σ₁))) ≅
      Spec (CommRingCat.of (A ⧸ (RingHom.ker σ₀ ⊔ RingHom.ker σ₁))) :=
    asIso (Spec.map e.toRingEquiv.toCommRingCatIso.hom)
  exact ⟨i1 ≪≫ i2 ≪≫ i3 ≪≫ i4⟩

end F9Helpers

private theorem F9R.isNoetherianRing_tensor_chartAlgFin
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (κ : Type) [Field κ] [Algebra (DRLevel.R q) κ] :
    IsNoetherianRing (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)) := by
  haveI : Algebra.FiniteType (DRLevel.R q) ↥(IgusaScheme.chartAlgFin N₀ q) :=
    (ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf N₀ q).1
  haveI : Algebra.FiniteType κ (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)) := inferInstance
  exact Algebra.FiniteType.isNoetherianRing κ _

private theorem F9R.forall_exists_eq_pow_of_forall_tmul_one
    {R κ M A : Type*} [CommRing R] [Field κ] [Algebra R κ] [CommRing M] [Algebra R M]
    [CommRing A] [Algebra κ A] (p : ℕ) [Fact p.Prime] [CharP κ p] [PerfectRing κ p] [CharP A p]
    (f : κ ⊗[R] M →ₐ[κ] A) (hf : ∀ m : M, ∃ c : A, f ((1 : κ) ⊗ₜ[R] m) = c ^ p) :
    ∀ z : κ ⊗[R] M, ∃ c : A, f z = c ^ p := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, zero_pow (Fact.out : p.Prime).ne_zero]⟩
  | tmul x m =>
      obtain ⟨c, hc⟩ := hf m
      refine ⟨algebraMap κ A ((frobeniusEquiv κ p).symm x) * c, ?_⟩
      have hx : x ⊗ₜ[R] m = x • ((1 : κ) ⊗ₜ[R] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hy : ((frobeniusEquiv κ p).symm x) ^ p = x := by
        rw [← frobenius_def]; exact frobenius_apply_frobeniusEquiv_symm κ p x
      rw [hx, map_smul, hc, mul_pow, ← map_pow, hy, Algebra.smul_def]
  | add u v hu hv =>
      obtain ⟨c, hc⟩ := hu
      obtain ⟨d, hd⟩ := hv
      exact ⟨c + d, by rw [map_add, hc, hd, add_pow_char]⟩

end F9HelpersSection

set_option maxHeartbeats 16000000 in
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

    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ))
    (hcomp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hcomp_ci : ∀ i, IsClosedImmersion (comp i))
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π toκ = 𝟙 _)
    (hcomp_w : comp 0 ≫ DRLevel.fibreMap w.hom hw toκ = comp 1) :
    IsReduced (pullback (comp 0) (comp 1)) := by
  letI instAlg : Algebra (DRLevel.R q) κ := toκ.toAlgebra

  have hcompat0 : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom) ≫ IgusaScheme.ιFin N₀ q) ≫
        DRLevel.toBase0 N₀ q =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q)))) ≫ Spec.map (CommRingCat.ofHom toκ) := by
    rw [Category.assoc, IgusaScheme.ιFin_igusaTo, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    show Algebra.TensorProduct.includeRight (algebraMap _ _ r) = (toκ r) ⊗ₜ 1
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    rfl
  let c₀ : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) ⟶ DRLevel.fibre0 (N₀ := N₀) toκ :=
    pullback.lift _ _ hcompat0
  have hcompat : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q) ≫
        DRLevel.toBase N₀ q =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q)))) ≫ Spec.map (CommRingCat.ofHom toκ) := by
    rw [Category.assoc, IgusaScheme.ιFin_igusaTo, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    show Algebra.TensorProduct.includeRight (algebraMap _ _ r) = (toκ r) ⊗ₜ 1
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    rfl
  let c : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ⟶ DRLevel.fibre (N₀ := N₀) toκ :=
    pullback.lift _ _ hcompat

  obtain ⟨hc₀_oi, hc₀_range⟩ := F9R.isOpenImmersion_chart N₀ q κ c₀ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  obtain ⟨hc_oi, hc_range⟩ := F9R.isOpenImmersion_chart (N₀ * q) q κ c (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

  obtain ⟨σ₀, hσ₀, hsq₀⟩ := ModularCurve.DRLevel.exists_retraction_chart_comp_zero_eq N₀ q hqN π iota0 hiota hpichart κ
    c₀ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) c (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    comp hcomp_over hcomp_ci hcomp_pi

  have hc₀fst : c₀ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom) ≫ IgusaScheme.ιFin N₀ q :=
    pullback.lift_fst _ _ _
  have hc₀snd : c₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q)))) :=
    pullback.lift_snd _ _ _
  have hcfst : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q :=
    pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q)))) :=
    pullback.lift_snd _ _ _

  have hwsq : c ≫ DRLevel.fibreMap w.hom hw toκ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom) ≫ c :=
    F9R.chart_fibreMap N₀ q κ w hw theta hwchart c hcfst hcsnd
  have hπsq : c ≫ DRLevel.fibreMap0 π toκ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom) ≫ c₀ :=
    F9R.chart_fibreMap0 N₀ q κ π iota0 hpichart c₀ hc₀fst hc₀snd c hcfst hcsnd

  let σ₁ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[κ] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q) :=
    σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)
  have hσ₁ : σ₁.toRingHom = σ₀.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom := rfl
  have hsq₁ : c₀ ≫ comp 1 = Spec.map (CommRingCat.ofHom σ₁.toRingHom) ≫ c := by
    rw [← hcomp_w, reassoc_of% hsq₀, hwsq, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hσ₁]

  have hZ := ModularCurve.DRLevel.fst_pullback_comp_mem_range_iotaFin N₀ q hqN w hw theta htheta hwchart π iota0 hiota hpichart κ toκ comp hcomp_over hcomp_ci hcomp_pi hcomp_w
  have hfst : ∀ n, (pullback.fst (comp 0) (comp 1)).base n ∈ Set.range c₀.base := by
    intro n; rw [hc₀_range]; exact hZ n

  have hw' : w.inv ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q := by rw [Iso.inv_comp_eq, hw]
  have hwchart' : IgusaScheme.ιFin (N₀ * q) q ≫ w.inv =
      Spec.map (CommRingCat.ofHom theta.symm.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q := by
    rw [Iso.comp_inv_eq, Category.assoc, hwchart, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    have : theta.symm.toRingEquiv.toRingHom.comp theta.toRingEquiv.toRingHom = RingHom.id _ :=
      RingHom.ext fun b => theta.symm_apply_apply b
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have hwsq' : c ≫ DRLevel.fibreMap w.inv hw' toκ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.symm.toAlgHom).toRingHom) ≫ c :=
    F9R.chart_fibreMap N₀ q κ w.symm hw' theta.symm hwchart' c hcfst hcsnd
  have hwinv : DRLevel.fibreMap w.hom hw toκ ≫ DRLevel.fibreMap w.inv hw' toκ = 𝟙 _ := by
    apply pullback.hom_ext <;>
      simp [DRLevel.fibreMap, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]
  have hsnd : ∀ n, (pullback.snd (comp 0) (comp 1)).base n ∈ Set.range c₀.base := by
    intro n

    obtain ⟨y, hy⟩ := hfst n
    have h1 : (DRLevel.fibreMap w.hom hw toκ).base ((comp 0).base ((pullback.snd (comp 0) (comp 1)).base n)) ∈
        Set.range c.base := by
      rw [← Scheme.Hom.comp_apply, hcomp_w, ← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply,
        ← hy, ← Scheme.Hom.comp_apply, hsq₀]
      exact ⟨_, rfl⟩
    have h2 : (comp 0).base ((pullback.snd (comp 0) (comp 1)).base n) ∈ Set.range c.base := by
      obtain ⟨u, hu⟩ := h1
      have hz : (DRLevel.fibreMap w.hom hw toκ ≫ DRLevel.fibreMap w.inv hw' toκ).base
          ((comp 0).base ((pullback.snd (comp 0) (comp 1)).base n)) = (c ≫ DRLevel.fibreMap w.inv hw' toκ).base u := by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hu]
      rw [hwinv, hwsq', Scheme.Hom.id_base] at hz
      exact ⟨_, hz.symm⟩

    obtain ⟨v, hv⟩ := h2
    have h3 : (pullback.snd (comp 0) (comp 1)).base n =
        (DRLevel.fibreMap0 π toκ).base ((comp 0).base ((pullback.snd (comp 0) (comp 1)).base n)) := by
      rw [← Scheme.Hom.comp_apply (comp 0), hcomp_pi, Scheme.Hom.id_base]; rfl
    rw [h3, ← hv, ← Scheme.Hom.comp_apply, hπsq]
    exact ⟨_, rfl⟩

  let e : pullback (c₀ ≫ comp 0) (c₀ ≫ comp 1) ⟶ pullback (comp 0) (comp 1) :=
    pullback.map _ _ _ _ c₀ c₀ (𝟙 _) (by simp) (by simp)
  let l₁ : pullback (comp 0) (comp 1) ⟶ Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) :=
    IsOpenImmersion.lift c₀ (pullback.fst (comp 0) (comp 1)) (by rintro _ ⟨n, rfl⟩; exact hfst n)
  let l₂ : pullback (comp 0) (comp 1) ⟶ Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) :=
    IsOpenImmersion.lift c₀ (pullback.snd (comp 0) (comp 1)) (by rintro _ ⟨n, rfl⟩; exact hsnd n)
  have hl₁ : l₁ ≫ c₀ = pullback.fst (comp 0) (comp 1) := IsOpenImmersion.lift_fac _ _ _
  have hl₂ : l₂ ≫ c₀ = pullback.snd (comp 0) (comp 1) := IsOpenImmersion.lift_fac _ _ _
  let einv : pullback (comp 0) (comp 1) ⟶ pullback (c₀ ≫ comp 0) (c₀ ≫ comp 1) :=
    pullback.lift l₁ l₂ (by rw [reassoc_of% hl₁, reassoc_of% hl₂, pullback.condition])
  have heinv_fst : einv ≫ pullback.fst _ _ = l₁ := pullback.lift_fst _ _ _
  have heinv_snd : einv ≫ pullback.snd _ _ = l₂ := pullback.lift_snd _ _ _
  have he_fst : e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ c₀ := pullback.lift_fst _ _ _
  have he_snd : e ≫ pullback.snd _ _ = pullback.snd _ _ ≫ c₀ := pullback.lift_snd _ _ _
  have he₁ : e ≫ einv = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [← cancel_mono c₀]
      simp only [Category.assoc, Category.id_comp]
      rw [reassoc_of% heinv_fst, hl₁, he_fst]
    · rw [← cancel_mono c₀]
      simp only [Category.assoc, Category.id_comp]
      rw [reassoc_of% heinv_snd, hl₂, he_snd]
  have he₂ : einv ≫ e = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp]
      rw [he_fst, reassoc_of% heinv_fst, hl₁]
    · simp only [Category.assoc, Category.id_comp]
      rw [he_snd, reassoc_of% heinv_snd, hl₂]
  haveI : IsIso e := ⟨⟨einv, he₁, he₂⟩⟩

  let I : Ideal (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) :=
    RingHom.ker σ₁.toRingHom ⊔ RingHom.ker σ₀.toRingHom

  have hθθ : ∀ y, Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom
      (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.symm.toAlgHom y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [Algebra.TensorProduct.map_tmul]
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  have hσ₀surj : Function.Surjective σ₀.toRingHom := fun z => ⟨_, hσ₀ z⟩
  have hσ₁surj : Function.Surjective σ₁.toRingHom := fun z =>
    ⟨Algebra.TensorProduct.map (AlgHom.id κ κ) theta.symm.toAlgHom (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z), by
      show σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom _) = z
      rw [hθθ, hσ₀]⟩
  obtain ⟨e''⟩ := F9Helpers.nonempty_pullback_iso_Spec_quotient_ker_sup_ker σ₁.toRingHom σ₀.toRingHom hσ₁surj hσ₀surj
    c (c₀ ≫ comp 1) (c₀ ≫ comp 0) hsq₁ hsq₀
  let e' : pullback (c₀ ≫ comp 0) (c₀ ≫ comp 1) ≅
      Spec (CommRingCat.of ((κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) ⧸ I)) :=
    pullbackSymmetry _ _ ≪≫ e''

  haveI : IsNoetherianRing (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)) :=
    F9R.isNoetherianRing_tensor_chartAlgFin N₀ q κ
  let ι₀f : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q) → κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) :=
    fun b => Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 b
  let ι₁f : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q) → κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) :=
    fun b => Algebra.TensorProduct.map (AlgHom.id κ κ) theta.symm.toAlgHom (ι₀f b)
  have h₀' : ∀ b, σ₁.toRingHom (ι₁f b) = b := fun b => by
    show σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom _) = b
    rw [hθθ, hσ₀]
  have h₁' : ∀ b, σ₀.toRingHom (ι₀f b) = b := fun b => hσ₀ b

  have hfrob1 : ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
      σ₁ ((1 : κ) ⊗ₜ[DRLevel.R q] iota0 b) = ((1 : κ) ⊗ₜ[DRLevel.R q] b) ^ q := by
    have := ModularCurve.IgusaScheme.retraction_one_tmul_iota_eq_pow_of_not_dvd N₀ q hqN κ iota0 hiota theta htheta
      ![σ₀, σ₁] (fun z => hσ₀ z) (fun z => rfl)
    exact this
  haveI hred : IsReduced ((κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) ⧸ I) := by
    rcases subsingleton_or_nontrivial (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)) with hB | hB
    ·
      have h01 : (0 : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) = 1 := by
        have := congrArg (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0)
          (Subsingleton.elim (0 : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)) 1)
        rwa [map_zero, map_one] at this
      haveI : Subsingleton (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) := subsingleton_of_zero_eq_one h01
      haveI : Subsingleton ((κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) ⧸ I) :=
        Ideal.Quotient.mk_surjective.subsingleton
      infer_instance
    · haveI : CharP (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)) q :=
        charP_of_injective_algebraMap (algebraMap κ _).injective q
      haveI : ExpChar κ q := ExpChar.prime Fact.out
      have hfrob : ∀ b, ∃ c, σ₁.toRingHom (ι₀f b) = c ^ q := by
        refine F9R.forall_exists_eq_pow_of_forall_tmul_one q
          (σ₁.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0)) fun b => ⟨(1 : κ) ⊗ₜ[DRLevel.R q] b, ?_⟩
        show σ₁ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 ((1 : κ) ⊗ₜ[DRLevel.R q] b)) = _
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        exact hfrob1 b
      exact RingHom.isReduced_quotient_ker_sup_ker_of_exists_apply_eq_pow σ₁.toRingHom σ₀.toRingHom ι₁f ι₀f h₀' h₁' q (Fact.out : q.Prime).two_le hfrob
  haveI : IsReduced (Spec (CommRingCat.of ((κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) ⧸ I))) :=
    inferInstance
  exact isReduced_of_isOpenImmersion (inv e ≫ e'.hom)

end

end S_ModularCurve_DRLevel_isReduced_pullback_comp
end P2MW
export P2MW.S_ModularCurve_DRLevel_isReduced_pullback_comp (solution)
