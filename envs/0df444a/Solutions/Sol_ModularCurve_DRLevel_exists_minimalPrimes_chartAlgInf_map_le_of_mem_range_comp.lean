-- Prove2me | solution 1 for ModularCurve.DRLevel.exists_minimalPrimes_chartAlgInf_map_le_of_mem_range_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1b8a5917-6a00-58d9-97fe-4702c047a0d2

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_IgusaScheme_exists_ringHom_laurentSeries_pair_chartAlgFin_mul_frobenius_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_map_le_ker_retraction_iff_mem_of_mem_minimalPrimes_of_not_dvd
import Theorems.Thm_ModularCurve_DRLevel_exists_retraction_chart_comp_zero_eq
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegral_pullback_igusaTo_of_charP
import Theorems.Thm_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_exists_minimalPrimes_chartAlgInf_map_le_of_mem_range_comp
p2m_attr_erase "instance" "ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableNonsingular instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeRingHom AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply"
p2m_attr_erase "simp" "NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
open scoped TensorProduct

noncomputable section

namespace PoleCompsA

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

end PoleCompsA

namespace PoleCompsA

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

end PoleCompsA

namespace PoleCompsA

private lemma isPullback_chartInf (M q : ℕ) [NeZero M] [Fact q.Prime] (κ : Type) [Field κ] [Algebra (DRLevel.R q) κ]
    (c : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgInf M q))) ⟶
      pullback (IgusaScheme.igusaTo M q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf M q))).toRingHom) ≫ IgusaScheme.ιInf M q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf M q))))) :
    IsPullback c (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf M q))).toRingHom))
      (pullback.fst _ _) (IgusaScheme.ιInf M q) := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (DRLevel.R q) κ ↥(IgusaScheme.chartAlgInf M q))
  have s : IsPullback (c ≫ pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf M q))).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))
      (IgusaScheme.ιInf M q ≫ IgusaScheme.igusaTo M q) := by
    rw [hcsnd, IgusaScheme.ιInf_igusaTo]
    exact sq
  exact IsPullback.of_right s hcfst (IsPullback.of_hasPullback _ _).flip

private lemma isOpenImmersion_chartInf (M q : ℕ) [NeZero M] [Fact q.Prime] (κ : Type) [Field κ] [Algebra (DRLevel.R q) κ]
    (c : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgInf M q))) ⟶
      pullback (IgusaScheme.igusaTo M q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf M q))).toRingHom) ≫ IgusaScheme.ιInf M q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf M q))))) :
    IsOpenImmersion c ∧ Set.range c.base = (pullback.fst (IgusaScheme.igusaTo M q)
      (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))).base ⁻¹' Set.range (IgusaScheme.ιInf M q).base := by
  have H := isPullback_chartInf M q κ c hcfst hcsnd
  have hc : c = H.isoPullback.hom ≫ pullback.fst _ _ := (H.isoPullback_hom_fst).symm
  refine ⟨by rw [hc]; infer_instance, ?_⟩
  rw [← Scheme.Pullback.range_fst, hc]
  ext x; constructor
  · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.hom.base y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.inv.base y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]⟩

private theorem ig_ιFin_eq_ιInf_iff (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (x₀ : IgusaScheme.XFin N ℓ) (xi : IgusaScheme.XInf N ℓ) :
    (IgusaScheme.ιFin N ℓ).base x₀ = (IgusaScheme.ιInf N ℓ).base xi ↔
      ∃ w : IgusaScheme.XMid N ℓ, (IgusaScheme.fFin N ℓ).base w = x₀ ∧ (IgusaScheme.fInf N ℓ).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (F := span (IgusaScheme.fFin N ℓ) (IgusaScheme.fInf N ℓ))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · exact match fi, fj, h₁, h₂ with
        | .init _, .init _, h₁, h₂ => ⟨w, h₁, h₂⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨w, rfl, rfl⟩
    change (IgusaScheme.fFin N ℓ ≫ IgusaScheme.ιFin N ℓ).base w = (IgusaScheme.fInf N ℓ ≫ IgusaScheme.ιInf N ℓ).base w
    rw [IgusaScheme.glue_condition]

private theorem ig_range_fInf (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    Set.range (IgusaScheme.fInf N ℓ).base =
      ((PrimeSpectrum.basicOpen (IgusaScheme.jInvChartInf N ℓ) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(IgusaScheme.chartAlgInf N ℓ))) :
          Set (PrimeSpectrum ↥(IgusaScheme.chartAlgInf N ℓ))) := by
  letI := (IgusaScheme.inclInf N ℓ).toRingHom.toAlgebra
  haveI := IgusaScheme.isLocalization_away_inclInf N ℓ
  exact PrimeSpectrum.localization_away_comap_range ↥(IgusaScheme.chartAlgMid N ℓ) (IgusaScheme.jInvChartInf N ℓ)

private theorem ig_ιInf_mem_range_ιFin_iff (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (xi : IgusaScheme.XInf N ℓ) :
    (IgusaScheme.ιInf N ℓ).base xi ∈ Set.range (IgusaScheme.ιFin N ℓ).base ↔
      IgusaScheme.jInvChartInf N ℓ ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← ig_range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (ig_ιFin_eq_ιInf_iff N ℓ x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(IgusaScheme.fFin N ℓ).base w, (ig_ιFin_eq_ιInf_iff N ℓ _ _).mpr ⟨w, rfl, rfl⟩⟩

section FinRead

variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (κ : Type) [Field κ] [Algebra (DRLevel.R q) κ]
    (w : DRLevel.X N₀ q ≅ DRLevel.X N₀ q) (hw : w.hom ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (theta : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ≃ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hwchart : IgusaScheme.ιFin (N₀ * q) q ≫ w.hom =
      Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (iota0 : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hpichart : IgusaScheme.ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ IgusaScheme.ιFin N₀ q)
    (c₀ : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) ⟶ DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hc₀fst : c₀ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom) ≫ IgusaScheme.ιFin N₀ q)
    (hc₀snd : c₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q)))))
    (c : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ⟶ DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hcfst : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hcsnd : c ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q)))))
    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) ⟶ DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ)))
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) = 𝟙 _)
    (hcomp_w : comp 0 ≫ DRLevel.fibreMap w.hom hw (algebraMap (DRLevel.R q) κ) = comp 1)
    (σ₀ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[κ] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z)
    (hsq₀ : c₀ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c)

include hc₀fst hc₀snd hcfst hcsnd hpichart hcomp_pi h0 hsq₀ in

theorem mem_range_comp_zero_iff (z : ↥(Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))))) :
    c.base z ∈ Set.range (comp 0).base ↔ RingHom.ker σ₀.toRingHom ≤ z.asIdeal := by
  have hsurj : Function.Surjective σ₀.toRingHom := fun y => ⟨_, h0 y⟩
  constructor
  · rintro ⟨y₀, hy₀⟩

    have hπsq := PoleCompsA.chart_fibreMap0 N₀ q κ π iota0 hpichart c₀ hc₀fst hc₀snd c hcfst hcsnd
    have hy₀' : y₀ = c₀.base ((Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom)).base z) := by
      have h1 : y₀ = (comp 0 ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ)).base y₀ := by
        rw [hcomp_pi]; rfl
      rw [h1]
      change (DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ)).base ((comp 0).base y₀) = _
      rw [hy₀]
      change (c ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ)).base z = _
      rw [hπsq]
      rfl

    have hcz : c.base z = c.base ((Spec.map (CommRingCat.ofHom σ₀.toRingHom)).base
        ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom)).base z)) := by
      rw [← hy₀]
      change _ = (Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c).base _
      rw [← hsq₀, hy₀']
      rfl
    obtain ⟨hc_oi, -⟩ := PoleCompsA.isOpenImmersion_chart (N₀ * q) q κ c hcfst hcsnd
    have hz := c.isOpenEmbedding.injective hcz
    rw [hz]
    intro a ha
    show σ₀.toRingHom a ∈ ((Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom)).base z).asIdeal
    rw [RingHom.mem_ker.mp ha]
    exact Ideal.zero_mem _
  · intro hker

    have hprime : (Ideal.map σ₀.toRingHom z.asIdeal).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj hker
    let z₀ : ↥(Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)))) := ⟨Ideal.map σ₀.toRingHom z.asIdeal, hprime⟩
    have hz : (Spec.map (CommRingCat.ofHom σ₀.toRingHom)).base z₀ = z := by
      apply PrimeSpectrum.ext
      change Ideal.comap σ₀.toRingHom (Ideal.map σ₀.toRingHom z.asIdeal) = z.asIdeal
      rw [Ideal.comap_map_of_surjective _ hsurj, sup_eq_left]
      intro a ha
      exact hker ha
    refine ⟨c₀.base z₀, ?_⟩
    change (c₀ ≫ comp 0).base z₀ = _
    rw [hsq₀, ← hz]
    rfl

include hc₀fst hc₀snd hcfst hcsnd hpichart hcomp_pi h0 hsq₀ hwchart hcomp_w in

theorem mem_range_comp_one_iff (z : ↥(Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))))) :
    c.base z ∈ Set.range (comp 1).base ↔
      RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom ≤ z.asIdeal := by

  set T : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[κ] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) :=
    Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom with hT
  set S : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[κ] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) :=
    Algebra.TensorProduct.map (AlgHom.id κ κ) theta.symm.toAlgHom with hS
  have hST : ∀ a, S (T a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [hT, hS, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hTS : ∀ a, T (S a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [hT, hS, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

  have hwsq := PoleCompsA.chart_fibreMap N₀ q κ w hw theta hwchart c hcfst hcsnd
  have hw' : w.inv ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q := by rw [Iso.inv_comp_eq, hw]
  have hwchart' : IgusaScheme.ιFin (N₀ * q) q ≫ w.inv =
      Spec.map (CommRingCat.ofHom theta.symm.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q := by
    rw [Iso.comp_inv_eq, Category.assoc, hwchart, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    have : theta.symm.toRingEquiv.toRingHom.comp theta.toRingEquiv.toRingHom = RingHom.id _ :=
      RingHom.ext fun b => theta.symm_apply_apply b
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have hwsq' : c ≫ DRLevel.fibreMap w.inv hw' (algebraMap (DRLevel.R q) κ) =
      Spec.map (CommRingCat.ofHom S.toRingHom) ≫ c :=
    PoleCompsA.chart_fibreMap N₀ q κ w.symm hw' theta.symm hwchart' c hcfst hcsnd
  have hwinv : DRLevel.fibreMap w.hom hw (algebraMap (DRLevel.R q) κ) ≫
      DRLevel.fibreMap w.inv hw' (algebraMap (DRLevel.R q) κ) = 𝟙 _ := by
    apply pullback.hom_ext <;>
      simp [DRLevel.fibreMap, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]

  have key := mem_range_comp_zero_iff N₀ q κ π iota0 hpichart c₀ hc₀fst hc₀snd c hcfst hcsnd comp hcomp_pi σ₀ h0 hsq₀
    ((Spec.map (CommRingCat.ofHom S.toRingHom)).base z)

  have hiff : RingHom.ker σ₀.toRingHom ≤ ((Spec.map (CommRingCat.ofHom S.toRingHom)).base z).asIdeal ↔
      RingHom.ker (σ₀.comp T).toRingHom ≤ z.asIdeal := by
    constructor
    · intro h b hb
      have hb' : T b ∈ RingHom.ker σ₀.toRingHom := hb
      have h2 : S.toRingHom (T b) ∈ z.asIdeal := h hb'
      change S (T b) ∈ z.asIdeal at h2
      rwa [hST] at h2
    · intro h a ha
      show S.toRingHom a ∈ z.asIdeal
      apply h
      show σ₀ (T (S a)) = 0
      rw [hTS]
      exact ha
  rw [← hiff, ← key]

  constructor
  · rintro ⟨y₀, hy₀⟩
    refine ⟨y₀, ?_⟩
    have h1 : (comp 0).base y₀ = (comp 1 ≫ DRLevel.fibreMap w.inv hw' (algebraMap (DRLevel.R q) κ)).base y₀ := by
      rw [← hcomp_w, Category.assoc, hwinv, Category.comp_id]
    rw [h1, Scheme.Hom.comp_apply, hy₀, ← Scheme.Hom.comp_apply, hwsq', Scheme.Hom.comp_apply]
  · rintro ⟨y₀, hy₀⟩
    refine ⟨y₀, ?_⟩
    rw [← hcomp_w, Scheme.Hom.comp_apply, hy₀, ← Scheme.Hom.comp_apply, hwsq, Scheme.Hom.comp_apply]
    congr 1
    apply PrimeSpectrum.ext
    change Ideal.comap T.toRingHom (Ideal.comap S.toRingHom z.asIdeal) = z.asIdeal
    have hid : S.toRingHom.comp T.toRingHom = RingHom.id _ := RingHom.ext hST
    rw [Ideal.comap_comap, hid, Ideal.comap_id]

end FinRead

section KerMin

variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [Algebra (DRLevel.R q) κ]

theorem jqModC_ne_zero_def (K : Type) [Field K] : jqModC K ≠ 0 := by
  intro h0
  have := order_jqModC_def K
  rw [h0, HahnSeries.order_zero] at this
  norm_num at this

theorem jqModC_pow_ne_zero (K : Type) [Field K] (n : ℕ) : jqModC K ^ n ≠ 0 := pow_ne_zero n (jqModC_ne_zero_def K)

theorem exists_minimalPrimes_pair_fin (hqN : ¬ q ∣ N₀)
    (theta : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ≃ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (htheta : ∀ b, ((theta b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) =
      atkinLehnerInvolutionFull N₀ q (b : ↥(modularFunctionFieldFull (N₀ * q))))
    (iota0 : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hiota : ∀ b, (((iota0 b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (σ₀ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[κ] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z) :
    ∃ 𝔭 : Fin 2 → Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      (∀ i, 𝔭 i ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))}).minimalPrimes) ∧ 𝔭 0 ≠ 𝔭 1 ∧
      Ideal.map (Algebra.TensorProduct.includeRight : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[DRLevel.R q] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (𝔭 0) ≤
        RingHom.ker σ₀.toRingHom ∧
      Ideal.map (Algebra.TensorProduct.includeRight : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[DRLevel.R q] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (𝔭 1) ≤
        RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom ∧
      IgusaScheme.jChartFin (N₀ * q) q ∉ 𝔭 0 ∧ IgusaScheme.jChartFin (N₀ * q) q ∉ 𝔭 1 := by
  obtain ⟨θr, hθ1, hpin, hne, hmin, hfrob, -⟩ :=
    ModularCurve.IgusaScheme.exists_ringHom_laurentSeries_pair_chartAlgFin_mul_frobenius_of_not_dvd N₀ q hqN
      iota0 hiota theta htheta κ

  have hj1 : (((iota0 (IgusaScheme.jChartFin N₀ q) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) :
      LaurentSeries ℚ) = jq := by rw [hiota]; rfl
  have hj2 : (((IgusaScheme.jChartFin (N₀ * q) q : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) :
      LaurentSeries ℚ) = jq := rfl
  have hιj : iota0 (IgusaScheme.jChartFin N₀ q) = IgusaScheme.jChartFin (N₀ * q) q :=
    Subtype.ext (Subtype.ext (hj1.trans hj2.symm))

  have hθj : θr 0 (IgusaScheme.jChartFin (N₀ * q) q) = jqModC κ := by
    rw [hpin (IgusaScheme.jChartFin (N₀ * q) q) (jqModC ℤ)]
    · exact coeffMap_jqModC (Int.castRingHom κ)
    · show jq = _
      rw [coeffMap_jqModC, jqModC_rat]
  refine ⟨fun i => RingHom.ker (θr i), fun i => ?_, hne, ?_, ?_, ?_, ?_⟩
  · rw [hmin]
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  ·
    refine (ModularCurve.IgusaScheme.map_le_ker_retraction_iff_mem_of_mem_minimalPrimes_of_not_dvd N₀ q hqN κ
      iota0 hiota theta htheta σ₀ h0 (RingHom.ker (θr 0)) ?_).mpr ?_
    · rw [hmin]; exact Set.mem_insert _ _
    · rw [RingHom.mem_ker, map_sub, map_pow, hfrob, sub_self]
  ·
    have h0' := (ModularCurve.IgusaScheme.map_le_ker_retraction_iff_mem_of_mem_minimalPrimes_of_not_dvd N₀ q hqN κ
      iota0 hiota theta htheta σ₀ h0 (RingHom.ker (θr 0)) (by rw [hmin]; exact Set.mem_insert _ _)).mpr
      (by rw [RingHom.mem_ker, map_sub, map_pow, hfrob, sub_self])
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    show σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom ((1 : κ) ⊗ₜ a)) = 0
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hθa : (theta a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) ∈ RingHom.ker (θr 0) := by
      rw [RingHom.mem_ker, ← hθ1]; exact ha
    have := h0' (Ideal.mem_map_of_mem _ hθa)
    rwa [RingHom.mem_ker] at this
  · rw [RingHom.mem_ker, hθj]
    exact jqModC_ne_zero_def κ
  · rw [RingHom.mem_ker, hθ1, ← hιj, hfrob, hιj, hθj]
    exact jqModC_pow_ne_zero κ q

end KerMin

section FinToPole

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

def polePrime (𝔭 : Ideal ↥(IgusaScheme.chartAlgFin N ℓ)) : Ideal ↥(IgusaScheme.chartAlgInf N ℓ) :=
  Ideal.comap (IgusaScheme.inclInf N ℓ).toRingHom (Ideal.map (IgusaScheme.inclFin N ℓ).toRingHom 𝔭)

variable {N ℓ} in

theorem mem_polePrime_iff {𝔭 : Ideal ↥(IgusaScheme.chartAlgFin N ℓ)} {x : ↥(IgusaScheme.chartAlgInf N ℓ)} :
    x ∈ polePrime N ℓ 𝔭 ↔ (IgusaScheme.inclInf N ℓ).toRingHom x ∈ Ideal.map (IgusaScheme.inclFin N ℓ).toRingHom 𝔭 := by
  rw [polePrime, Ideal.mem_comap]

theorem inclInf_jInv_mul_inclFin_j :
    (IgusaScheme.inclInf N ℓ) (IgusaScheme.jInvChartInf N ℓ) * (IgusaScheme.inclFin N ℓ) (IgusaScheme.jChartFin N ℓ) = 1 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, IgusaScheme.coe_chartIncl, IgusaScheme.coe_chartIncl,
    IgusaScheme.coe_jInvChartInf, IgusaScheme.coe_jChartFin]
  exact inv_mul_cancel₀ (IgusaScheme.jFull_ne_zero N)

theorem natCast_eq_inclFin : ((ℓ : ℕ) : ↥(IgusaScheme.chartAlgMid N ℓ)) = (IgusaScheme.inclFin N ℓ) (ℓ : ↥(IgusaScheme.chartAlgFin N ℓ)) :=
  (map_natCast _ ℓ).symm

theorem natCast_eq_inclInf : ((ℓ : ℕ) : ↥(IgusaScheme.chartAlgMid N ℓ)) = (IgusaScheme.inclInf N ℓ) (ℓ : ↥(IgusaScheme.chartAlgInf N ℓ)) :=
  (map_natCast _ ℓ).symm

variable {N ℓ}

theorem map_inclFin_isPrime {𝔭 : Ideal ↥(IgusaScheme.chartAlgFin N ℓ)} (h𝔭 : 𝔭.IsPrime)
    (hj : IgusaScheme.jChartFin N ℓ ∉ 𝔭) : (Ideal.map (IgusaScheme.inclFin N ℓ).toRingHom 𝔭).IsPrime := by
  letI := (IgusaScheme.inclFin N ℓ).toRingHom.toAlgebra
  haveI := IgusaScheme.isLocalization_away_inclFin N ℓ
  have h := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (IgusaScheme.jChartFin N ℓ)) (↥(IgusaScheme.chartAlgMid N ℓ)) 𝔭 h𝔭
    ((Ideal.disjoint_powers_iff_notMem _ h𝔭.isRadical).mpr hj)
  rwa [RingHom.algebraMap_toAlgebra] at h

theorem comap_map_inclFin {𝔭 : Ideal ↥(IgusaScheme.chartAlgFin N ℓ)} (h𝔭 : 𝔭.IsPrime)
    (hj : IgusaScheme.jChartFin N ℓ ∉ 𝔭) :
    Ideal.comap (IgusaScheme.inclFin N ℓ).toRingHom (Ideal.map (IgusaScheme.inclFin N ℓ).toRingHom 𝔭) = 𝔭 := by
  letI := (IgusaScheme.inclFin N ℓ).toRingHom.toAlgebra
  haveI := IgusaScheme.isLocalization_away_inclFin N ℓ
  have h := IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers (IgusaScheme.jChartFin N ℓ)) (↥(IgusaScheme.chartAlgMid N ℓ)) h𝔭
    ((Ideal.disjoint_powers_iff_notMem _ h𝔭.isRadical).mpr hj)
  rwa [RingHom.algebraMap_toAlgebra] at h

theorem map_comap_inclFin (J : Ideal ↥(IgusaScheme.chartAlgMid N ℓ)) :
    Ideal.map (IgusaScheme.inclFin N ℓ).toRingHom (Ideal.comap (IgusaScheme.inclFin N ℓ).toRingHom J) = J := by
  letI := (IgusaScheme.inclFin N ℓ).toRingHom.toAlgebra
  haveI := IgusaScheme.isLocalization_away_inclFin N ℓ
  have h := IsLocalization.map_comap (Submonoid.powers (IgusaScheme.jChartFin N ℓ)) (↥(IgusaScheme.chartAlgMid N ℓ)) J
  rwa [RingHom.algebraMap_toAlgebra] at h

theorem map_inclInf_isPrime {Q : Ideal ↥(IgusaScheme.chartAlgInf N ℓ)} (hQ : Q.IsPrime)
    (hj : IgusaScheme.jInvChartInf N ℓ ∉ Q) : (Ideal.map (IgusaScheme.inclInf N ℓ).toRingHom Q).IsPrime := by
  letI := (IgusaScheme.inclInf N ℓ).toRingHom.toAlgebra
  haveI := IgusaScheme.isLocalization_away_inclInf N ℓ
  have h := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (IgusaScheme.jInvChartInf N ℓ)) (↥(IgusaScheme.chartAlgMid N ℓ)) Q hQ
    ((Ideal.disjoint_powers_iff_notMem _ hQ.isRadical).mpr hj)
  rwa [RingHom.algebraMap_toAlgebra] at h

theorem comap_map_inclInf {Q : Ideal ↥(IgusaScheme.chartAlgInf N ℓ)} (hQ : Q.IsPrime)
    (hj : IgusaScheme.jInvChartInf N ℓ ∉ Q) :
    Ideal.comap (IgusaScheme.inclInf N ℓ).toRingHom (Ideal.map (IgusaScheme.inclInf N ℓ).toRingHom Q) = Q := by
  letI := (IgusaScheme.inclInf N ℓ).toRingHom.toAlgebra
  haveI := IgusaScheme.isLocalization_away_inclInf N ℓ
  have h := IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers (IgusaScheme.jInvChartInf N ℓ)) (↥(IgusaScheme.chartAlgMid N ℓ)) hQ
    ((Ideal.disjoint_powers_iff_notMem _ hQ.isRadical).mpr hj)
  rwa [RingHom.algebraMap_toAlgebra] at h

theorem map_comap_inclInf (J : Ideal ↥(IgusaScheme.chartAlgMid N ℓ)) :
    Ideal.map (IgusaScheme.inclInf N ℓ).toRingHom (Ideal.comap (IgusaScheme.inclInf N ℓ).toRingHom J) = J := by
  letI := (IgusaScheme.inclInf N ℓ).toRingHom.toAlgebra
  haveI := IgusaScheme.isLocalization_away_inclInf N ℓ
  have h := IsLocalization.map_comap (Submonoid.powers (IgusaScheme.jInvChartInf N ℓ)) (↥(IgusaScheme.chartAlgMid N ℓ)) J
  rwa [RingHom.algebraMap_toAlgebra] at h

theorem jInv_not_mem_polePrime {𝔭 : Ideal ↥(IgusaScheme.chartAlgFin N ℓ)} (h𝔭 : 𝔭.IsPrime)
    (hj : IgusaScheme.jChartFin N ℓ ∉ 𝔭) : IgusaScheme.jInvChartInf N ℓ ∉ polePrime N ℓ 𝔭 := by
  intro h
  rw [mem_polePrime_iff] at h
  have hP := map_inclFin_isPrime h𝔭 hj
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]

  have h1 : (IgusaScheme.inclInf N ℓ).toRingHom (IgusaScheme.jInvChartInf N ℓ) *
      (IgusaScheme.inclFin N ℓ).toRingHom (IgusaScheme.jChartFin N ℓ) = 1 := by
    rw [AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.coe_toRingHom]
    exact inclInf_jInv_mul_inclFin_j N ℓ
  rw [← h1]
  exact Ideal.mul_mem_right _ _ h

theorem polePrime_isPrime {𝔭 : Ideal ↥(IgusaScheme.chartAlgFin N ℓ)} (h𝔭 : 𝔭.IsPrime)
    (hj : IgusaScheme.jChartFin N ℓ ∉ 𝔭) : (polePrime N ℓ 𝔭).IsPrime := by
  haveI := map_inclFin_isPrime h𝔭 hj
  exact Ideal.IsPrime.comap _

theorem map_inclInf_polePrime {𝔭 : Ideal ↥(IgusaScheme.chartAlgFin N ℓ)} :
    Ideal.map (IgusaScheme.inclInf N ℓ).toRingHom (polePrime N ℓ 𝔭) = Ideal.map (IgusaScheme.inclFin N ℓ).toRingHom 𝔭 :=
  map_comap_inclInf _

theorem polePrime_mem_minimalPrimes {𝔭 : Ideal ↥(IgusaScheme.chartAlgFin N ℓ)}
    (h𝔭 : 𝔭 ∈ (Ideal.span {((ℓ : ℕ) : ↥(IgusaScheme.chartAlgFin N ℓ))}).minimalPrimes)
    (hj : IgusaScheme.jChartFin N ℓ ∉ 𝔭) :
    polePrime N ℓ 𝔭 ∈ (Ideal.span {((ℓ : ℕ) : ↥(IgusaScheme.chartAlgInf N ℓ))}).minimalPrimes := by
  have hprime : 𝔭.IsPrime := h𝔭.1.1
  have hℓ𝔭 : ((ℓ : ℕ) : ↥(IgusaScheme.chartAlgFin N ℓ)) ∈ 𝔭 := h𝔭.1.2 (Ideal.mem_span_singleton_self _)
  refine ⟨⟨polePrime_isPrime hprime hj, ?_⟩, ?_⟩
  · rw [Ideal.span_singleton_le_iff_mem, polePrime, Ideal.mem_comap, map_natCast]
    simpa only [map_natCast] using Ideal.mem_map_of_mem (IgusaScheme.inclFin N ℓ).toRingHom hℓ𝔭
  · rintro Q ⟨hQ, hℓQ⟩ hQP

    have hjQ : IgusaScheme.jInvChartInf N ℓ ∉ Q := fun h => jInv_not_mem_polePrime hprime hj (hQP h)
    haveI := map_inclInf_isPrime hQ hjQ
    set Qt : Ideal ↥(IgusaScheme.chartAlgFin N ℓ) :=
      Ideal.comap (IgusaScheme.inclFin N ℓ).toRingHom (Ideal.map (IgusaScheme.inclInf N ℓ).toRingHom Q) with hQt
    have hQt_prime : Qt.IsPrime := Ideal.IsPrime.comap _
    have hℓQt : Ideal.span {((ℓ : ℕ) : ↥(IgusaScheme.chartAlgFin N ℓ))} ≤ Qt := by
      rw [Ideal.span_singleton_le_iff_mem, hQt, Ideal.mem_comap, map_natCast]
      simpa only [map_natCast] using
        Ideal.mem_map_of_mem (IgusaScheme.inclInf N ℓ).toRingHom (hℓQ (Ideal.mem_span_singleton_self _))
    have hQt_le : Qt ≤ 𝔭 := by
      rw [hQt, ← comap_map_inclFin hprime hj]
      refine Ideal.comap_mono ?_
      rw [← map_inclInf_polePrime]
      exact Ideal.map_mono hQP
    have h𝔭Qt : 𝔭 ≤ Qt := h𝔭.2 ⟨hQt_prime, hℓQt⟩ hQt_le

    intro b hb
    rw [mem_polePrime_iff] at hb
    rw [← comap_map_inclInf hQ hjQ, Ideal.mem_comap]
    have hb' := hb
    have hle : Ideal.map (IgusaScheme.inclFin N ℓ).toRingHom 𝔭 ≤ Ideal.map (IgusaScheme.inclInf N ℓ).toRingHom Q := by
      calc Ideal.map (IgusaScheme.inclFin N ℓ).toRingHom 𝔭
          ≤ Ideal.map (IgusaScheme.inclFin N ℓ).toRingHom Qt := Ideal.map_mono h𝔭Qt
        _ = Ideal.map (IgusaScheme.inclInf N ℓ).toRingHom Q := map_comap_inclFin _
    exact hle hb'

theorem polePrime_ne {𝔭 𝔭' : Ideal ↥(IgusaScheme.chartAlgFin N ℓ)} (h𝔭 : 𝔭.IsPrime) (h𝔭' : 𝔭'.IsPrime)
    (hj : IgusaScheme.jChartFin N ℓ ∉ 𝔭) (hj' : IgusaScheme.jChartFin N ℓ ∉ 𝔭') (hne : 𝔭 ≠ 𝔭') :
    polePrime N ℓ 𝔭 ≠ polePrime N ℓ 𝔭' := by
  intro h
  apply hne
  rw [← comap_map_inclFin h𝔭 hj, ← comap_map_inclFin h𝔭' hj', ← map_inclInf_polePrime, ← map_inclInf_polePrime, h]

theorem polePrime_le_comap {𝔭 : Ideal ↥(IgusaScheme.chartAlgFin N ℓ)} {𝔴 : Ideal ↥(IgusaScheme.chartAlgMid N ℓ)}
    (h : 𝔭 ≤ Ideal.comap (IgusaScheme.inclFin N ℓ).toRingHom 𝔴) :
    polePrime N ℓ 𝔭 ≤ Ideal.comap (IgusaScheme.inclInf N ℓ).toRingHom 𝔴 :=
  Ideal.comap_mono (Ideal.map_le_iff_le_comap.mpr h)

end FinToPole

section Assembly

theorem ideal_map_toRingHom {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (I : Ideal A) : Ideal.map f.toRingHom I = Ideal.map f I := rfl

theorem ideal_comap_toRingHom {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (J : Ideal B) : Ideal.comap f.toRingHom J = Ideal.comap f J := rfl

set_option maxHeartbeats 6400000 in

theorem poleComps
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

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] [Algebra (DRLevel.R q) κ]

    (c' : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgInf (N₀ * q) q))) ⟶
      DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιInf (N₀ * q) q)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf (N₀ * q) q)))))

    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) ⟶ DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ)))
    (hcomp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hcomp_ci : ∀ i, IsClosedImmersion (comp i))
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) = 𝟙 _)
    (hcomp_w : comp 0 ≫ DRLevel.fibreMap w.hom hw (algebraMap (DRLevel.R q) κ) = comp 1) :
    ∃ P : Fin 2 → Ideal ↥(IgusaScheme.chartAlgInf (N₀ * q) q),
      (∀ i, P i ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgInf (N₀ * q) q))}).minimalPrimes) ∧ P 0 ≠ P 1 ∧
      ∀ (i : Fin 2) (z : ↥(Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgInf (N₀ * q) q))))),
        c'.base z ∈ Set.range (comp i).base →
          Ideal.map (Algebra.TensorProduct.includeRight :
              ↥(IgusaScheme.chartAlgInf (N₀ * q) q) →ₐ[DRLevel.R q] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgInf (N₀ * q) q)) (P i) ≤ z.asIdeal := by

  have hcompat0 : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom) ≫ IgusaScheme.ιFin N₀ q) ≫ DRLevel.toBase0 N₀ q =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q)))) ≫ Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)) := by
    rw [Category.assoc, IgusaScheme.ιFin_igusaTo, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    show Algebra.TensorProduct.includeRight (algebraMap _ _ r) = (algebraMap (DRLevel.R q) κ r) ⊗ₜ 1
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  let c₀ : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) ⟶ DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) :=
    pullback.lift _ _ hcompat0
  have hc₀fst : c₀ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom) ≫ IgusaScheme.ιFin N₀ q :=
    pullback.lift_fst _ _ _
  have hc₀snd : c₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q)))) := pullback.lift_snd _ _ _
  have hcompat : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q) ≫ DRLevel.toBase N₀ q =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q)))) ≫ Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)) := by
    rw [Category.assoc, IgusaScheme.ιFin_igusaTo, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => ?_
    show Algebra.TensorProduct.includeRight (algebraMap _ _ r) = (algebraMap (DRLevel.R q) κ r) ⊗ₜ 1
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  let c : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ⟶ DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ) :=
    pullback.lift _ _ hcompat
  have hcfst : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q :=
    pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q)))) := pullback.lift_snd _ _ _
  obtain ⟨hc_oi, hc_range⟩ := PoleCompsA.isOpenImmersion_chart (N₀ * q) q κ c hcfst hcsnd

  obtain ⟨σ₀, h0, hsq₀⟩ := ModularCurve.DRLevel.exists_retraction_chart_comp_zero_eq N₀ q hqN π iota0 hiota hpichart κ
    c₀ hc₀fst hc₀snd c hcfst hcsnd comp hcomp_over hcomp_ci hcomp_pi

  obtain ⟨𝔭, h𝔭min, h𝔭ne, h𝔭0, h𝔭1, hj0, hj1⟩ :=
    exists_minimalPrimes_pair_fin N₀ q κ hqN theta htheta iota0 hiota σ₀ h0
  have hjnot : ∀ i, IgusaScheme.jChartFin (N₀ * q) q ∉ 𝔭 i := fun i => by
    fin_cases i
    · exact hj0
    · exact hj1

  let kers : Fin 2 → Ideal (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) := fun i =>
    if i = 0 then RingHom.ker σ₀.toRingHom
    else RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom
  have hkers : ∀ i, Ideal.map (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) (𝔭 i) ≤ kers i := fun i => by
    fin_cases i
    · exact h𝔭0
    · exact h𝔭1
  have hread : ∀ (i : Fin 2) (z : ↥(Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))))),
      c.base z ∈ Set.range (comp i).base ↔ kers i ≤ z.asIdeal := fun i z => by
    fin_cases i
    · exact mem_range_comp_zero_iff N₀ q κ π iota0 hpichart c₀ hc₀fst hc₀snd c hcfst hcsnd comp hcomp_pi σ₀ h0 hsq₀ z
    · exact mem_range_comp_one_iff N₀ q κ w hw theta hwchart π iota0 hpichart c₀ hc₀fst hc₀snd c hcfst hcsnd comp
        hcomp_pi hcomp_w σ₀ h0 hsq₀ z
  refine ⟨fun i => polePrime (N₀ * q) q (𝔭 i),
    fun i => polePrime_mem_minimalPrimes (h𝔭min i) (hjnot i),
    polePrime_ne (h𝔭min 0).1.1 (h𝔭min 1).1.1 (hjnot 0) (hjnot 1) h𝔭ne, ?_⟩
  intro i z' hz'

  haveI : IsIntegral (DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ)) :=
    ModularCurve.IgusaScheme.isIntegral_pullback_igusaTo_of_charP N₀ q hqN κ
  set Z : Set ↥(DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ)) := Set.range (comp i).base with hZ
  have hZirr : IsIrreducible Z := by
    rw [hZ, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (comp i).continuous.continuousOn
  set U : Set ↥(DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ)) := Set.range c.base with hU
  have hUopen : IsOpen U := c.isOpenEmbedding.isOpen_range

  have hZU : (Z ∩ U).Nonempty := by
    haveI : IsDomain (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)) :=
      (ModularCurve.IgusaScheme.isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed N₀ q hqN κ).1
    let z₀ : ↥(Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)))) := ⟨⊥, Ideal.bot_prime⟩
    refine ⟨(comp i).base (c₀.base z₀), ⟨_, rfl⟩, ?_⟩

    fin_cases i
    · refine ⟨(Spec.map (CommRingCat.ofHom σ₀.toRingHom)).base z₀, ?_⟩
      change _ = (c₀ ≫ comp 0).base z₀
      rw [hsq₀]
      rfl
    · have hwsq := PoleCompsA.chart_fibreMap N₀ q κ w hw theta hwchart c hcfst hcsnd
      refine ⟨(Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom)).base z₀, ?_⟩
      change (Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom) ≫ c).base z₀ = (c₀ ≫ comp 1).base z₀
      rw [← hwsq, ← hcomp_w, reassoc_of% hsq₀]

  set D : Set ↥(Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgInf (N₀ * q) q)))) :=
    (PrimeSpectrum.zeroLocus ((Ideal.map (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf (N₀ * q) q))) (polePrime (N₀ * q) q (𝔭 i)) : Ideal _) : Set _))ᶜ with hD
  have hDopen : IsOpen D := (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  obtain ⟨hc'_oi, -⟩ := PoleCompsA.isOpenImmersion_chartInf (N₀ * q) q κ c' hc'fst hc'snd
  set T : Set ↥(DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ)) := (c'.base '' D)ᶜ with hT
  have hTclosed : IsClosed T := (c'.isOpenEmbedding.isOpenMap D hDopen).isClosed_compl

  have hZUT : Z ∩ U ⊆ T := by
    rintro y ⟨hyZ, ⟨z, rfl⟩⟩ hmem
    obtain ⟨z'', hz''D, hyz''⟩ := hmem
    have hk : kers i ≤ z.asIdeal := (hread i z).mp hyZ
    have h𝔭z : 𝔭 i ≤ Ideal.comap (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom z.asIdeal := by
      rw [ideal_comap_toRingHom]
      exact Ideal.map_le_iff_le_comap.mp ((hkers i).trans hk)

    have hglue : (IgusaScheme.ιFin (N₀ * q) q).base ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom)).base z) =
        (IgusaScheme.ιInf (N₀ * q) q).base ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf (N₀ * q) q))).toRingHom)).base z'') := by
      change (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q).base z =
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιInf (N₀ * q) q).base z''
      rw [← hcfst, ← hc'fst]
      change (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))).base (c.base z) = (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))).base (c'.base z'')
      rw [hyz'']
    obtain ⟨wm, hwm0, hwm1⟩ := (PoleCompsA.ig_ιFin_eq_ιInf_iff (N₀ * q) q _ _).mp hglue
    have h1 : 𝔭 i ≤ Ideal.comap (IgusaScheme.inclFin (N₀ * q) q).toRingHom wm.asIdeal := by
      intro a ha
      have ha' := h𝔭z ha
      have e : ((IgusaScheme.fFin (N₀ * q) q).base wm).asIdeal =
          ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom)).base z).asIdeal := by rw [hwm0]
      have ha'' : a ∈ ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom)).base z).asIdeal := ha'
      rw [← e] at ha''
      exact ha''
    have h2 := polePrime_le_comap h1
    have h3 : ((IgusaScheme.fInf (N₀ * q) q).base wm).asIdeal =
        ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf (N₀ * q) q))).toRingHom)).base z'').asIdeal := by rw [hwm1]
    have h2' : polePrime (N₀ * q) q (𝔭 i) ≤ Ideal.comap (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf (N₀ * q) q))).toRingHom z''.asIdeal := by
      intro x hx
      have hx' : x ∈ ((IgusaScheme.fInf (N₀ * q) q).base wm).asIdeal := h2 hx
      rw [h3] at hx'
      exact hx'
    apply hz''D
    intro b hb
    have hb1 : b ∈ Ideal.map (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf (N₀ * q) q))).toRingHom (polePrime (N₀ * q) q (𝔭 i)) := by
      rw [ideal_map_toRingHom]; exact hb
    exact Ideal.map_le_iff_le_comap.mpr h2' hb1

  have hZT : Z ⊆ T :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hZirr.isPreirreducible hUopen hZU).trans
      (closure_minimal hZUT hTclosed)
  by_contra hcon
  exact hZT hz' ⟨z', fun h => hcon h, rfl⟩

end Assembly

end PoleCompsA

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

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] [Algebra (DRLevel.R q) κ]

    (c' : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgInf (N₀ * q) q))) ⟶
      DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιInf (N₀ * q) q)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgInf (N₀ * q) q)))))

    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) ⟶ DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ)))
    (hcomp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hcomp_ci : ∀ i, IsClosedImmersion (comp i))
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) = 𝟙 _)
    (hcomp_w : comp 0 ≫ DRLevel.fibreMap w.hom hw (algebraMap (DRLevel.R q) κ) = comp 1) :
    ∃ P : Fin 2 → Ideal ↥(IgusaScheme.chartAlgInf (N₀ * q) q),
      (∀ i, P i ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgInf (N₀ * q) q))}).minimalPrimes) ∧ P 0 ≠ P 1 ∧
      ∀ (i : Fin 2) (z : ↥(Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgInf (N₀ * q) q))))),
        c'.base z ∈ Set.range (comp i).base →
          Ideal.map (Algebra.TensorProduct.includeRight :
              ↥(IgusaScheme.chartAlgInf (N₀ * q) q) →ₐ[DRLevel.R q]
                κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgInf (N₀ * q) q)) (P i) ≤ z.asIdeal :=
  PoleCompsA.poleComps N₀ q hqN w hw theta htheta hwchart π iota0 hiota hpichart κ c' hc'fst hc'snd
    comp hcomp_over hcomp_ci hcomp_pi hcomp_w

end

end S_ModularCurve_DRLevel_exists_minimalPrimes_chartAlgInf_map_le_of_mem_range_comp
end P2MW
export P2MW.S_ModularCurve_DRLevel_exists_minimalPrimes_chartAlgInf_map_le_of_mem_range_comp (solution)
