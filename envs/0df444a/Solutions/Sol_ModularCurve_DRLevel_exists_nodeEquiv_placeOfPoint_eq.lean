-- Prove2me | solution 1 for ModularCurve.DRLevel.exists_nodeEquiv_placeOfPoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/967e62ea-c94a-522d-be84-04d5fc8c6152

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_DRLevel_fst_pullback_comp_mem_range_iotaFin
import Theorems.Thm_ModularCurve_IgusaScheme_retraction_one_tmul_modularUnit_eq_prod_ssJSet_of_not_dvd
import Theorems.Thm_ModularCurve_DRLevel_isAffineGeomPlace_and_evalAt_jGeomGen_eq_of_chartPin
import Theorems.Thm_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint
import Theorems.Thm_ModularCurve_DRLevel_exists_retraction_chart_comp_zero_eq
import Theorems.Thm_ModularCurve_IgusaScheme_finite_minimalPrimes_tensor_chartAlgFin_mul_and_ncard_eq_two_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_isReduced_pullback_igusaTo_specMap_of_not_dvd
import Theorems.Thm_ModularCurve_DRModelPackageLevel_modularUnitSeries_mem_chartAlgFin_mul
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed
import Theorems.Thm_ModularCurve_IgusaScheme_retraction_one_tmul_iota_eq_pow_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_ker_comp_atkinLehner_le_comap_retraction_of_mem_ssJSet_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_exists_nodeEquiv_placeOfPoint_eq
p2m_attr_erase "instance" "ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine"
p2m_attr_erase "instance" "ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_baseChangeRingHom ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply"
p2m_attr_erase "simp" "HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
p2m_open "ModularCurve~nodeEquiv P2MW.S_ModularCurve_DRLevel_exists_nodeEquiv_placeOfPoint_eq.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel P2MW.S_ModularCurve_DRLevel_exists_nodeEquiv_placeOfPoint_eq.ModularCurve.DRLevel"
open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R DRLevel.X DRLevel.toBase DRLevel.toBase0 DRLevel.fibre DRLevel.fibre0 DRLevel.fibreMap DRLevel.fibreMap0 DRModelPackageLevel IgusaScheme.jFull IgusaScheme.chartAlgFin IgusaScheme.jChartFin IgusaScheme IgusaScheme.ιFin IgusaScheme.igusaTo IgusaScheme.ιFin_igusaTo qExpand jq modularFunctionFieldFull atkinLehnerInvolutionFull ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace modularFunctionFieldC ssJSet arithFrobC modularUnitSeries DRLevel.fst_pullback_comp_mem_range_iotaFin IgusaScheme.retraction_one_tmul_modularUnit_eq_prod_ssJSet_of_not_dvd DRLevel.isAffineGeomPlace_and_evalAt_jGeomGen_eq_of_chartPin DRLevel.mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint DRLevel.exists_retraction_chart_comp_zero_eq IgusaScheme.isReduced_pullback_igusaTo_specMap_of_not_dvd DRModelPackageLevel.modularUnitSeries_mem_chartAlgFin_mul modularUnitSeries_mem_modularFunctionFieldFull arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf IgusaScheme.isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed IgusaScheme.ker_comp_atkinLehner_le_comap_retraction_of_mem_ssJSet_of_not_dvd"
namespace DRLevel
p2m_export "ModularCurve.DRLevel" "R X toBase toBase0 fibre fibre0 fibreMap fibreMap0 fst_pullback_comp_mem_range_iotaFin isAffineGeomPlace_and_evalAt_jGeomGen_eq_of_chartPin mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint exists_retraction_chart_comp_zero_eq"
namespace NodeEnum
p2m_open "ModularCurve.DRLevel ModularCurve~nodeEquiv"

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

noncomputable def chartN (N : ℕ) [NeZero N] (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q))) ⟶
      pullback (IgusaScheme.igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ))) :=
  pullback.lift _ _ (chart_comm (q := q) N κ)

noncomputable abbrev chart0 (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) ⟶
      DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) :=
  chartN (q := q) N₀ κ

noncomputable abbrev chart (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ⟶
      DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ) :=
  chartN (q := q) (N₀ * q) κ

theorem chartN_fst (N : ℕ) [NeZero N] (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    chartN (q := q) N κ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N q))).toRingHom) ≫ IgusaScheme.ιFin N q :=
  pullback.lift_fst _ _ _

theorem chartN_snd (N : ℕ) [NeZero N] (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    chartN (q := q) N κ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N q)))) :=
  pullback.lift_snd _ _ _

theorem chart_fibreMap (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ]
    (φ : DRLevel.X N₀ q ⟶ DRLevel.X N₀ q) (hφ : φ ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (θ : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hchart : IgusaScheme.ιFin (N₀ * q) q ≫ φ = Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q) :
    chart (N₀ := N₀) (q := q) κ ≫ DRLevel.fibreMap φ hφ (algebraMap (DRLevel.R q) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) θ).toRingHom) ≫ chart (N₀ := N₀) (q := q) κ := by
  apply pullback.hom_ext
  · simp only [chart, chartN, DRLevel.fibreMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [hchart, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
  · simp only [chart, chartN, DRLevel.fibreMap, Category.assoc, pullback.lift_snd, Category.comp_id]
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
  · simp only [chart, chart0, chartN, DRLevel.fibreMap0, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [hchart, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
  · simp only [chart, chart0, chartN, DRLevel.fibreMap0, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp [Algebra.TensorProduct.includeLeftRingHom_apply]

attribute [reassoc] chart_fibreMap chart_fibreMap0

noncomputable def chartN' (N : ℕ) [NeZero N] (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q))) ⟶
      pullback (IgusaScheme.igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ))) :=
  Spec.map (Algebra.TensorProduct.comm (DRLevel.R q) ↥(IgusaScheme.chartAlgFin N q) κ).toRingEquiv.toCommRingCatIso.hom ≫
    (pullbackSpecIso (DRLevel.R q) ↥(IgusaScheme.chartAlgFin N q) κ).inv ≫
      (pullback.congrHom (IgusaScheme.ιFin_igusaTo N q) rfl).inv ≫
        (pullbackRightPullbackFstIso (IgusaScheme.igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))
          (IgusaScheme.ιFin N q)).inv ≫
          pullback.snd (IgusaScheme.ιFin N q) (pullback.fst _ _)

scoped instance isOpenImmersion_chartN' (N : ℕ) [NeZero N] (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    IsOpenImmersion (chartN' (q := q) N κ) := by
  unfold chartN'; infer_instance

theorem chartN'_eq (N : ℕ) [NeZero N] (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    chartN' (q := q) N κ = chartN (q := q) N κ := by
  apply pullback.hom_ext
  · simp only [chartN', chartN, Category.assoc, pullback.lift_fst]
    rw [← pullback.condition, pullbackRightPullbackFstIso_inv_fst_assoc, pullback.congrHom_inv, pullback.lift_fst_assoc,
      Category.comp_id, pullbackSpecIso_inv_fst_assoc, RingEquiv.toCommRingCatIso_hom, ← Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp]
    congr 3
  · simp only [chartN', chartN, Category.assoc, pullback.lift_snd]
    rw [pullbackRightPullbackFstIso_inv_snd_snd, pullback.congrHom_inv, pullback.lift_snd, Category.comp_id,
      pullbackSpecIso_inv_snd, RingEquiv.toCommRingCatIso_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

scoped instance isOpenImmersion_chartN (N : ℕ) [NeZero N] (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    IsOpenImmersion (chartN (q := q) N κ) := by
  rw [← chartN'_eq]; infer_instance

theorem range_chartN (N : ℕ) [NeZero N] (κ : Type) [CommRing κ] [Algebra (DRLevel.R q) κ] :
    Set.range (chartN (q := q) N κ).base =
      (pullback.fst (IgusaScheme.igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))).base ⁻¹'
        Set.range (IgusaScheme.ιFin N q).base := by
  have h : (chartN' (q := q) N κ).opensRange =
      (pullback.fst (IgusaScheme.igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) ⁻¹ᵁ
        (IgusaScheme.ιFin N q).opensRange := by
    unfold chartN'
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp_of_isIso,
      Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackSnd]
  rw [← chartN'_eq]
  ext y
  have := congrArg (fun U : TopologicalSpace.Opens _ => y ∈ U) h
  simpa using this

section Ring

variable (N : ℕ) [NeZero N] (κ : Type) [Field κ] [Algebra (DRLevel.R q) κ]

noncomputable abbrev aevalJ : Polynomial κ →ₐ[κ] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q) :=
  Polynomial.aeval ((1 : κ) ⊗ₜ[DRLevel.R q] IgusaScheme.jChartFin N q)

theorem isIntegralElem_aevalJ (s : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q)) :
    (aevalJ (q := q) N κ).toRingHom.IsIntegralElem s := by
  set f := (aevalJ (q := q) N κ).toRingHom with hf
  induction s using TensorProduct.induction_on with
  | zero => simpa using f.isIntegralElem_map (x := 0)
  | add x y hx hy => exact hx.add f hy
  | tmul x b =>
    have hxb : x ⊗ₜ[DRLevel.R q] b = (x ⊗ₜ[DRLevel.R q] (1 : ↥(IgusaScheme.chartAlgFin N q))) * ((1 : κ) ⊗ₜ[DRLevel.R q] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hxb]
    refine RingHom.IsIntegralElem.mul f ?_ ?_
    · have : f (Polynomial.C x) = x ⊗ₜ[DRLevel.R q] (1 : ↥(IgusaScheme.chartAlgFin N q)) := by
        simp [hf, aevalJ, Polynomial.aeval_C, Algebra.TensorProduct.algebraMap_apply]
      simpa [this] using f.isIntegralElem_map (x := Polynomial.C x)
    ·
      set A := Algebra.adjoin (DRLevel.R q) ({IgusaScheme.jFull N} : Set ↥(modularFunctionFieldFull N)) with hA
      have hb : IsIntegral ↥A (b : ↥(modularFunctionFieldFull N)) := b.2
      obtain ⟨p, hpm, hp0⟩ := hb

      let ψ : Polynomial (DRLevel.R q) →ₐ[DRLevel.R q] ↥A :=
        (Polynomial.aeval (IgusaScheme.jFull N)).codRestrict A (fun r => by
          rw [hA]; exact Polynomial.aeval_mem_adjoin_singleton _ _)
      have hψ : Function.Surjective ψ := by
        rintro ⟨c, hc⟩
        rw [hA, Algebra.adjoin_singleton_eq_range_aeval] at hc
        obtain ⟨r, rfl⟩ := hc
        exact ⟨r, rfl⟩
      have hψval : ∀ r, ((ψ r : ↥A) : ↥(modularFunctionFieldFull N)) = Polynomial.aeval (IgusaScheme.jFull N) r := fun r => rfl
      obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
        ((Polynomial.mem_lifts _).mpr (Polynomial.map_surjective ψ.toRingHom hψ p)) hpm

      have hPO : Polynomial.eval₂ (Polynomial.aeval (IgusaScheme.jChartFin N q) :
          Polynomial (DRLevel.R q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q)).toRingHom b P = 0 := by
        apply Subtype.ext
        have h1 : (((IgusaScheme.chartAlgFin N q).val).toRingHom.comp
            (Polynomial.aeval (IgusaScheme.jChartFin N q) :
              Polynomial (DRLevel.R q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q)).toRingHom) =
            (algebraMap ↥A ↥(modularFunctionFieldFull N)).comp ψ.toRingHom := by
          apply Polynomial.ringHom_ext
          · intro r
            simp [ψ, Polynomial.aeval_C]
          · simp [ψ]
        have h2 := Polynomial.hom_eval₂ P
          (Polynomial.aeval (IgusaScheme.jChartFin N q) :
            Polynomial (DRLevel.R q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q)).toRingHom
          ((IgusaScheme.chartAlgFin N q).val).toRingHom b
        rw [h1, ← Polynomial.eval₂_map, hPmap] at h2
        change ((IgusaScheme.chartAlgFin N q).val) _ = _
        rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
        rw [h2]
        simpa using hp0

      have h3 : f.comp (Polynomial.mapRingHom (algebraMap (DRLevel.R q) κ)) =
          (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N q))).toRingHom.comp
            (Polynomial.aeval (IgusaScheme.jChartFin N q) :
              Polynomial (DRLevel.R q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q)).toRingHom := by
        apply Polynomial.ringHom_ext
        · intro r
          simp [hf, aevalJ, Polynomial.aeval_C, Algebra.TensorProduct.includeRight_apply, Algebra.algebraMap_eq_smul_one,
            Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
        · simp [hf, aevalJ, Algebra.TensorProduct.includeRight_apply]
      refine ⟨P.map (Polynomial.mapRingHom (algebraMap (DRLevel.R q) κ)), hPm.map _, ?_⟩
      rw [Polynomial.eval₂_map, h3]
      have h4 := Polynomial.hom_eval₂ P
        (Polynomial.aeval (IgusaScheme.jChartFin N q) :
          Polynomial (DRLevel.R q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q)).toRingHom
        (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N q))).toRingHom b
      rw [hPO, map_zero] at h4
      simpa [Algebra.TensorProduct.includeRight_apply] using h4.symm

theorem isMaximal_of_ne_bot [IsDomain (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q))]
    (𝔪 : Ideal (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q))) [𝔪.IsPrime] (h : 𝔪 ≠ ⊥) : 𝔪.IsMaximal := by
  letI : Algebra (Polynomial κ) (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q)) := (aevalJ (q := q) N κ).toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (Polynomial κ) (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q)) :=
    ⟨fun s => isIntegralElem_aevalJ (q := q) N κ s⟩
  have h1 : Ideal.comap (algebraMap (Polynomial κ) (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q))) 𝔪 ≠ ⊥ :=
    fun h0 => h (Ideal.eq_bot_of_comap_eq_bot h0)
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔪 (IsPrime.to_maximal_ideal h1)

theorem exists_algHom_ker_eq [IsAlgClosed κ] (𝔪 : Ideal (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q))) [𝔪.IsMaximal] :
    ∃ ψ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q) →ₐ[κ] κ, RingHom.ker ψ = 𝔪 := by
  set S := κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N q)
  letI : Field (S ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Algebra.FiniteType (DRLevel.R q) ↥(IgusaScheme.chartAlgFin N q) :=
    (IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf N q).1
  haveI : Algebra.FiniteType κ S := Algebra.FiniteType.baseChange κ
  haveI : Algebra.FiniteType κ (S ⧸ 𝔪) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ κ 𝔪) Ideal.Quotient.mk_surjective
  haveI : Module.Finite κ (S ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing κ (S ⧸ 𝔪)
  haveI : Algebra.IsIntegral κ (S ⧸ 𝔪) := ⟨fun x => IsIntegral.of_finite κ x⟩
  have hinj : Function.Injective (algebraMap κ (S ⧸ 𝔪)) := (algebraMap κ (S ⧸ 𝔪)).injective
  have hsurj : Function.Surjective (algebraMap κ (S ⧸ 𝔪)) := IsSepClosed.algebraMap_surjective κ (S ⧸ 𝔪)
  let ε : κ ≃ₐ[κ] S ⧸ 𝔪 := AlgEquiv.ofBijective (Algebra.ofId κ (S ⧸ 𝔪)) ⟨hinj, hsurj⟩
  refine ⟨(ε.symm : S ⧸ 𝔪 →ₐ[κ] κ).comp (Ideal.Quotient.mkₐ κ 𝔪), ?_⟩
  ext s
  simp only [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_algHom,
    EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end Ring

section Geo

theorem Spec_map_base_apply {R S : CommRingCat} (f : R ⟶ S) (x : PrimeSpectrum S) :
    (Spec.map f).base x = PrimeSpectrum.comap f.hom x := by
  rw [Spec.map_base]; rfl

theorem fibreMap_comp {κ : Type} [CommRing κ] (toκ : DRLevel.R q →+* κ)
    (φ φ' : DRLevel.X N₀ q ⟶ DRLevel.X N₀ q) (hφ : φ ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (hφ' : φ' ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q) :
    DRLevel.fibreMap φ hφ toκ ≫ DRLevel.fibreMap φ' hφ' toκ =
      DRLevel.fibreMap (N₀ := N₀) (φ ≫ φ') (by rw [Category.assoc, hφ', hφ]) toκ := by
  apply pullback.hom_ext <;>
    simp only [DRLevel.fibreMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.comp_id]

theorem fibreMap_id {κ : Type} [CommRing κ] (toκ : DRLevel.R q →+* κ) :
    DRLevel.fibreMap (N₀ := N₀) (𝟙 _) (Category.id_comp _) toκ = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp only [DRLevel.fibreMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id,
      Category.id_comp]

theorem inv_chart (w : DRLevel.X N₀ q ≅ DRLevel.X N₀ q)
    (theta : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ≃ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hwchart : IgusaScheme.ιFin (N₀ * q) q ≫ w.hom =
      Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q) :
    IgusaScheme.ιFin (N₀ * q) q ≫ w.inv =
      Spec.map (CommRingCat.ofHom theta.symm.toAlgHom.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q := by
  have h1 : Spec.map (CommRingCat.ofHom theta.symm.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : theta.symm.toAlgHom.toRingHom.comp theta.toRingEquiv.toRingHom = RingHom.id _ := by
      ext b
      simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  rw [← cancel_mono w.hom, Category.assoc, w.inv_hom_id, Category.comp_id, Category.assoc, hwchart, ← Category.assoc, h1,
    Category.id_comp]

variable (N₀ q) in

theorem crossing_chart (hqN : ¬ q ∣ N₀)
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
    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) ⟶ DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ)))
    (hcomp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hcomp_ci : ∀ i, IsClosedImmersion (comp i))
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) = 𝟙 _)
    (hcomp_w : comp 0 ≫ DRLevel.fibreMap w.hom hw (algebraMap (DRLevel.R q) κ) = comp 1)
    (σ₀ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[κ] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))
    (hsq0 : chart0 (N₀ := N₀) (q := q) κ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ chart (N₀ := N₀) (q := q) κ)
    (n : ↥(pullback (comp 0) (comp 1))) :
    ∃ 𝔪 𝔪' : PrimeSpectrum (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)),
      (pullback.fst (comp 0) (comp 1)).base n = (chart0 (N₀ := N₀) (q := q) κ).base 𝔪 ∧
      (pullback.snd (comp 0) (comp 1)).base n = (chart0 (N₀ := N₀) (q := q) κ).base 𝔪' ∧
      (comp 0).base ((chart0 (N₀ := N₀) (q := q) κ).base 𝔪) = (chart (N₀ := N₀) (q := q) κ).base (PrimeSpectrum.comap σ₀.toRingHom 𝔪) ∧
      PrimeSpectrum.comap σ₀.toRingHom 𝔪 =
        PrimeSpectrum.comap (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom 𝔪' := by

  have hfin := ModularCurve.DRLevel.fst_pullback_comp_mem_range_iotaFin N₀ q hqN w hw theta htheta hwchart π iota0 hiota hpichart
    κ (algebraMap (DRLevel.R q) κ) comp hcomp_over hcomp_ci hcomp_pi hcomp_w n
  have hrange := range_chartN (q := q) N₀ κ
  obtain ⟨𝔪, h𝔪⟩ : (pullback.fst (comp 0) (comp 1)).base n ∈ Set.range (chart0 (N₀ := N₀) (q := q) κ).base := by
    change _ ∈ Set.range (chartN (q := q) N₀ κ).base
    rw [hrange, Set.mem_preimage]
    simpa [Scheme.Hom.comp_apply] using hfin

  have hy : ∀ 𝔫, (comp 0).base ((chart0 (N₀ := N₀) (q := q) κ).base 𝔫) =
      (chart (N₀ := N₀) (q := q) κ).base (PrimeSpectrum.comap σ₀.toRingHom 𝔫) := fun 𝔫 => by
    have := congrArg (fun f => f.base 𝔫) hsq0
    simpa [Scheme.Hom.comp_apply, Spec_map_base_apply] using this

  set x' := (pullback.snd (comp 0) (comp 1)).base n with hx'
  have hwinv : w.inv ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q := by
    rw [← cancel_epi w.hom, w.hom_inv_id_assoc, hw]
  have hc0 : comp 0 = comp 1 ≫ DRLevel.fibreMap w.inv hwinv (algebraMap (DRLevel.R q) κ) := by
    rw [← hcomp_w, Category.assoc, fibreMap_comp]
    have : DRLevel.fibreMap (N₀ := N₀) (w.hom ≫ w.inv) (by rw [Category.assoc, hwinv, hw]) (algebraMap (DRLevel.R q) κ) = 𝟙 _ := by
      have h := fibreMap_id (N₀ := N₀) (q := q) (algebraMap (DRLevel.R q) κ)
      convert h using 2 <;> simp
    rw [this, Category.comp_id]
  have hcond : (comp 0).base ((pullback.fst (comp 0) (comp 1)).base n) = (comp 1).base x' := by
    have := congrArg (fun f => f.base n) (pullback.condition (f := comp 0) (g := comp 1))
    simpa [Scheme.Hom.comp_apply] using this
  set 𝔮 := PrimeSpectrum.comap σ₀.toRingHom 𝔪 with h𝔮
  have h1x' : (comp 1).base x' = (chart (N₀ := N₀) (q := q) κ).base 𝔮 := by rw [← hcond, ← h𝔪, hy]

  have h0x' : (comp 0).base x' = (chart (N₀ := N₀) (q := q) κ).base
      (PrimeSpectrum.comap (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.symm.toAlgHom).toRingHom 𝔮) := by
    have e1 : (comp 0).base x' = (DRLevel.fibreMap w.inv hwinv (algebraMap (DRLevel.R q) κ)).base ((comp 1).base x') := by
      conv_lhs => rw [hc0]
      simp [Scheme.Hom.comp_apply]
    rw [e1, h1x']
    have := congrArg (fun f => f.base 𝔮) (chart_fibreMap (N₀ := N₀) (q := q) κ w.inv hwinv theta.symm.toAlgHom (inv_chart w theta hwchart))
    simpa [Scheme.Hom.comp_apply, Spec_map_base_apply] using this

  set 𝔪' : PrimeSpectrum (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)) :=
    PrimeSpectrum.comap (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom
      (PrimeSpectrum.comap (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.symm.toAlgHom).toRingHom 𝔮) with h𝔪'
  have hx'chart : x' = (chart0 (N₀ := N₀) (q := q) κ).base 𝔪' := by
    have e2 : x' = (DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ)).base ((comp 0).base x') := by
      have := congrArg (fun f => f.base x') hcomp_pi
      simpa [Scheme.Hom.comp_apply] using this.symm
    rw [e2, h0x']
    have := congrArg (fun f => f.base (PrimeSpectrum.comap (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.symm.toAlgHom).toRingHom 𝔮))
      (chart_fibreMap0 (N₀ := N₀) (q := q) κ π iota0 hpichart)
    simp [Scheme.Hom.comp_apply, Spec_map_base_apply] at this
    exact this

  have hsq1 : chart0 (N₀ := N₀) (q := q) κ ≫ comp 1 =
      Spec.map (CommRingCat.ofHom (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom) ≫
        chart (N₀ := N₀) (q := q) κ := by
    rw [← hcomp_w, reassoc_of% hsq0, chart_fibreMap (N₀ := N₀) (q := q) κ w.hom hw theta.toAlgHom hwchart,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    rfl
  have h1𝔪' : (comp 1).base ((chart0 (N₀ := N₀) (q := q) κ).base 𝔪') = (chart (N₀ := N₀) (q := q) κ).base
      (PrimeSpectrum.comap (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom 𝔪') := by
    have := congrArg (fun f => f.base 𝔪') hsq1
    simpa [Scheme.Hom.comp_apply, Spec_map_base_apply] using this
  refine ⟨𝔪, 𝔪', h𝔪.symm, hx'chart, hy 𝔪, ?_⟩
  apply (chart (N₀ := N₀) (q := q) κ).isOpenEmbedding.injective
  rw [← h1𝔪', ← hx'chart, h1x']

end Geo

theorem closed_and_read (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] [Algebra (DRLevel.R q) κ]
    (M : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ)) [IsIso e]
    (heM : e ≫ pullback.snd _ _ = M.toBase)
    [hMne : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) ⁻¹ᵁ
      ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))]
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
    (𝔪 : PrimeSpectrum (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)))
    (ψ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[κ] κ) (hψ : RingHom.ker ψ = 𝔪.asIdeal) :
    ∃ h : (inv e).base ((chart0 (N₀ := N₀) (q := q) κ).base 𝔪) ∈ closedPoints M.C,
      (M.placeOfPoint ⟨_, h⟩).IsRational ∧ IsAffineGeomPlace κ N₀ (M.placeOfPoint ⟨_, h⟩) ∧
      (M.placeOfPoint ⟨_, h⟩).evalAt (jGeomGen κ N₀) = ψ ((1 : κ) ⊗ₜ[DRLevel.R q] IgusaScheme.jChartFin N₀ q) := by

  have hleft : ψ.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom
      (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))) = RingHom.id κ := by
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, RingHom.id_apply]
    rw [show a ⊗ₜ[DRLevel.R q] (1 : ↥(IgusaScheme.chartAlgFin N₀ q)) =
          a • ((1 : κ) ⊗ₜ[DRLevel.R q] (1 : ↥(IgusaScheme.chartAlgFin N₀ q))) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      map_smul, ← Algebra.TensorProduct.one_def, map_one, smul_eq_mul, mul_one]
  have hpt_snd : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ chart0 (N₀ := N₀) (q := q) κ) ≫ pullback.snd _ _ = 𝟙 _ := by
    rw [Category.assoc, chartN_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hleft, CommRingCat.ofHom_id, Spec.map_id]
  have hpt_fst : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ chart0 (N₀ := N₀) (q := q) κ) ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom)) ≫ IgusaScheme.ιFin N₀ q := by
    rw [Category.assoc, chartN_fst, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

  have hbase : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ chart0 (N₀ := N₀) (q := q) κ).base (IsLocalRing.closedPoint κ) =
      (chart0 (N₀ := N₀) (q := q) κ).base 𝔪 := by
    rw [Scheme.Hom.comp_apply]
    congr 1
    have hbot : (IsLocalRing.closedPoint κ).asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top (IsLocalRing.closedPoint κ).asIdeal).resolve_right (IsLocalRing.closedPoint κ).isPrime.ne_top
    rw [Spec_map_base_apply]
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal, hbot, ← RingHom.ker_eq_comap_bot, ← hψ, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe,
      RingHom.ker_coe_toRingHom]
  have H := ModularCurve.DRLevel.isAffineGeomPlace_and_evalAt_jGeomGen_eq_of_chartPin N₀ q hqN κ (algebraMap (DRLevel.R q) κ)
    M e heM hMpin (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ chart0 (N₀ := N₀) (q := q) κ) hpt_snd _ hpt_fst
  rw [hbase] at H
  obtain ⟨h, hrat, haff, hval⟩ := H
  exact ⟨h, hrat, haff, hval⟩

theorem comp_one_fibreMap0_snd_eq_fst (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] {κ : Type} [CommRing κ] (toκ : DRLevel.R q →+* κ)
    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    {Y : Scheme.{0}} (e : Y ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) [IsIso e]
    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ))
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π toκ = 𝟙 _) (n : ↥(pullback (comp 0) (comp 1))) :
    (e ≫ comp 1 ≫ DRLevel.fibreMap0 π toκ).base ((inv e).base ((pullback.snd (comp 0) (comp 1)).base n)) =
      (pullback.fst (comp 0) (comp 1)).base n := by
  rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc, ← Scheme.Hom.comp_apply, ← Category.assoc,
    ← pullback.condition, Category.assoc, hcomp_pi, Category.comp_id]

theorem placeOfPoint_eq_arithFrobC_smul (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ]
    (M : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (P₁ P₂ : closedPoints M.C)
    (ν : Place κ ↥(modularFunctionFieldC κ N₀)) (hν : ν ∈ ssPlaces q N₀ κ)
    (h₁ : M.placeOfPoint P₁ = ν) (hfrob : M.placeOfPoint P₁ = arithFrobC q κ N₀ • M.placeOfPoint P₂) :
    M.placeOfPoint P₂ = arithFrobC q κ N₀ • ν := by
  have hinv := ModularCurve.arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q N₀ hqN κ ν hν
  rw [← h₁] at hinv ⊢
  exact MulAction.injective (arithFrobC q κ N₀) (hinv.trans hfrob).symm

theorem frob_conjunct (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
    (M : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) [IsIso e]
    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ))
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π toκ = 𝟙 _)
    (hfrob : ∀ P : closedPoints M.C,
      ∃ h : (inv e).base ((e ≫ comp 1 ≫ DRLevel.fibreMap0 π toκ).base P.1) ∈ closedPoints M.C,
        M.placeOfPoint ⟨_, h⟩ = arithFrobC q κ N₀ • M.placeOfPoint P)
    (n : ↥(pullback (comp 0) (comp 1))) (ν : Place κ ↥(modularFunctionFieldC κ N₀)) (hν : ν ∈ ssPlaces q N₀ κ)
    (h₁ : ∃ h : (inv e).base ((pullback.fst (comp 0) (comp 1)).base n) ∈ closedPoints M.C, M.placeOfPoint ⟨_, h⟩ = ν)
    (h₂ : (inv e).base ((pullback.snd (comp 0) (comp 1)).base n) ∈ closedPoints M.C) :
    ∃ h : (inv e).base ((pullback.snd (comp 0) (comp 1)).base n) ∈ closedPoints M.C,
      M.placeOfPoint ⟨_, h⟩ = arithFrobC q κ N₀ • ν := by
  obtain ⟨h₁, hpl⟩ := h₁
  obtain ⟨h', hfr⟩ := hfrob ⟨_, h₂⟩
  have hpt := comp_one_fibreMap0_snd_eq_fst N₀ q toκ π e comp hcomp_pi n
  have hfst : M.placeOfPoint ⟨_, h₁⟩ = arithFrobC q κ N₀ • M.placeOfPoint ⟨_, h₂⟩ := by
    rw [← hfr]
    congr 1
    exact Subtype.ext (congrArg (inv e).base hpt).symm
  exact ⟨h₂, placeOfPoint_eq_arithFrobC_smul N₀ q hqN κ M ⟨_, h₁⟩ ⟨_, h₂⟩ ν hν hpl hfst⟩

theorem comp_one_chart {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]
    (w : DRLevel.X N₀ q ≅ DRLevel.X N₀ q) (hw : w.hom ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (theta : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ≃ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hwchart : IgusaScheme.ιFin (N₀ * q) q ≫ w.hom =
      Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (κ : Type) [Field κ] [Algebra (DRLevel.R q) κ]
    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) ⟶ DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ)))
    (hcomp_w : comp 0 ≫ DRLevel.fibreMap w.hom hw (algebraMap (DRLevel.R q) κ) = comp 1)
    (σ₀ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[κ] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))
    (hsq0 : chart0 (N₀ := N₀) (q := q) κ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ chart (N₀ := N₀) (q := q) κ) :
    chart0 (N₀ := N₀) (q := q) κ ≫ comp 1 =
      Spec.map (CommRingCat.ofHom (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom) ≫
        chart (N₀ := N₀) (q := q) κ := by
  rw [← hcomp_w, reassoc_of% hsq0, chart_fibreMap (N₀ := N₀) (q := q) κ w.hom hw theta.toAlgHom hwchart,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  rfl

theorem comp_base_chart {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] (κ : Type) [Field κ] [Algebra (DRLevel.R q) κ]
    {f : DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) ⟶ DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ)}
    {τ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →+* κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)}
    (hsq : chart0 (N₀ := N₀) (q := q) κ ≫ f = Spec.map (CommRingCat.ofHom τ) ≫ chart (N₀ := N₀) (q := q) κ)
    (𝔫 : PrimeSpectrum (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) :
    f.base ((chart0 (N₀ := N₀) (q := q) κ).base 𝔫) = (chart (N₀ := N₀) (q := q) κ).base (PrimeSpectrum.comap τ 𝔫) := by
  have := congrArg (fun g => g.base 𝔫) hsq
  simpa [Scheme.Hom.comp_apply, Spec_map_base_apply] using this

set_option maxHeartbeats 6400000 in
theorem node_step
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
    (M : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ)) [IsIso e]
    (heM : e ≫ pullback.snd _ _ = M.toBase)
    [hMne : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) ⁻¹ᵁ
      ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))]
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
    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) ⟶ DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ)))
    (hcomp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hcomp_ci : ∀ i, IsClosedImmersion (comp i))
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) = 𝟙 _)
    (hcomp_w : comp 0 ≫ DRLevel.fibreMap w.hom hw (algebraMap (DRLevel.R q) κ) = comp 1)
    (σ₀ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[κ] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))
    (hσ₀ : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z)
    (hsq0 : chart0 (N₀ := N₀) (q := q) κ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ chart (N₀ := N₀) (q := q) κ)
    (n : ↥(pullback (comp 0) (comp 1))) :
    ∃ (h₁ : (inv e).base ((pullback.fst (comp 0) (comp 1)).base n) ∈ closedPoints M.C)
      (_ : (inv e).base ((pullback.snd (comp 0) (comp 1)).base n) ∈ closedPoints M.C),
      M.placeOfPoint ⟨_, h₁⟩ ∈ ssPlaces q N₀ κ := by
  haveI hSdom : IsDomain (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)) :=
    (IgusaScheme.isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed N₀ q hqN κ).1

  have hle : modularFunctionFieldFull q ≤ modularFunctionFieldFull (N₀ * q) := by
    apply IntermediateField.adjoin.mono
    rintro x ⟨d, hd, hdq, rfl⟩
    exact ⟨d, hd, hdq.trans (dvd_mul_left q N₀), rfl⟩
  have hmem : modularUnitSeries q ∈ modularFunctionFieldFull (N₀ * q) :=
    hle (ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull q)
  obtain ⟨hvA, -⟩ := ModularCurve.DRModelPackageLevel.modularUnitSeries_mem_chartAlgFin_mul N₀ q hqN hmem
  let v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := ⟨⟨modularUnitSeries q, hmem⟩, hvA⟩
  have hv : ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = modularUnitSeries q := rfl
  obtain ⟨hOa, -, hOc, hOd, hOe₀, hOe₁, hOne⟩ :=
    ModularCurve.IgusaScheme.retraction_one_tmul_modularUnit_eq_prod_ssJSet_of_not_dvd N₀ q hqN κ iota0 hiota theta htheta
      σ₀ hσ₀ v hv
  have hψ_tmul : ∀ (ψ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[κ] κ) (a : κ),
      (1 : κ) ⊗ₜ[DRLevel.R q] IgusaScheme.jChartFin N₀ q - a ⊗ₜ[DRLevel.R q] (1 : ↥(IgusaScheme.chartAlgFin N₀ q)) ∈ RingHom.ker ψ ↔
        ψ ((1 : κ) ⊗ₜ[DRLevel.R q] IgusaScheme.jChartFin N₀ q) = a := by
    intro ψ a
    have h2 : ψ (a ⊗ₜ[DRLevel.R q] (1 : ↥(IgusaScheme.chartAlgFin N₀ q))) = a := by
      have : algebraMap κ (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)) a =
          a ⊗ₜ[DRLevel.R q] (1 : ↥(IgusaScheme.chartAlgFin N₀ q)) := by
        rw [Algebra.TensorProduct.algebraMap_apply]; rfl
      rw [← this, AlgHom.commutes]; rfl
    rw [RingHom.mem_ker, map_sub, h2, sub_eq_zero]
  have hv1 : (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)) ((1 : κ) ⊗ₜ[DRLevel.R q] v) = 0 := by
    rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]
    simpa using hOa
  obtain ⟨𝔪, 𝔪', hfst, hsnd, hy, hqq⟩ := crossing_chart N₀ q hqN w hw theta htheta hwchart π iota0 hiota hpichart κ
    comp hcomp_over hcomp_ci hcomp_pi hcomp_w σ₀ hsq0 n

  have hqq' : ∀ z, σ₀ z ∈ 𝔪.asIdeal ↔ (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)) z ∈ 𝔪'.asIdeal := fun z => by
    have h := congrArg (fun I : PrimeSpectrum (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) => z ∈ I.asIdeal) hqq
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, eq_iff_iff] at h
    exact h
  have hvm : σ₀ ((1 : κ) ⊗ₜ[DRLevel.R q] v) ∈ 𝔪.asIdeal := by
    rw [hqq', hv1]; exact zero_mem _
  obtain ⟨a, ha, hja⟩ := (hOc 𝔪.asIdeal 𝔪.isPrime).mp hvm

  have hk01 : ¬ (RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)) ≤ RingHom.ker σ₀) := fun hle' =>
    hOne (le_antisymm (hOe₀.2 ⟨hOe₁.1.1, bot_le⟩ hle') hle')
  have hk10 : ¬ (RingHom.ker σ₀ ≤ RingHom.ker (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom))) := fun hle' =>
    hOne (le_antisymm hle' (hOe₁.2 ⟨hOe₀.1.1, bot_le⟩ hle'))
  have h𝔪ne : 𝔪.asIdeal ≠ ⊥ := by
    intro h0
    refine hk01 fun z hz => ?_
    have hz' : (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)) z = 0 := hz
    have h2 : σ₀ z ∈ 𝔪.asIdeal := (hqq' z).mpr (by rw [hz']; exact zero_mem _)
    have h3 : σ₀ z ∈ (⊥ : Ideal (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) := h0 ▸ h2
    exact Ideal.mem_bot.mp h3
  have h𝔪'ne : 𝔪'.asIdeal ≠ ⊥ := by
    intro h0
    refine hk10 fun z hz => ?_
    have hz' : σ₀ z = 0 := hz
    have h2 : (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)) z ∈ 𝔪'.asIdeal := (hqq' z).mp (by rw [hz']; exact zero_mem _)
    have h3 : (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)) z ∈ (⊥ : Ideal (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) := h0 ▸ h2
    exact Ideal.mem_bot.mp h3
  haveI : 𝔪.asIdeal.IsMaximal := isMaximal_of_ne_bot (q := q) N₀ κ 𝔪.asIdeal h𝔪ne
  haveI : 𝔪'.asIdeal.IsMaximal := isMaximal_of_ne_bot (q := q) N₀ κ 𝔪'.asIdeal h𝔪'ne
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker_eq (q := q) N₀ κ 𝔪.asIdeal
  obtain ⟨ψ', hψ'⟩ := exists_algHom_ker_eq (q := q) N₀ κ 𝔪'.asIdeal
  obtain ⟨h₁, hrat, haff, hev⟩ := closed_and_read N₀ q hqN κ M e heM hMpin 𝔪 ψ hψ
  obtain ⟨h₂, -, -, -⟩ := closed_and_read N₀ q hqN κ M e heM hMpin 𝔪' ψ' hψ'
  have hψa : ψ ((1 : κ) ⊗ₜ[DRLevel.R q] IgusaScheme.jChartFin N₀ q) = a := (hψ_tmul ψ a).mp (hψ ▸ hja)
  simp only [hfst, hsnd]
  exact ⟨h₁, h₂, ⟨hrat, haff, by rw [hev, hψa]; exact ha⟩⟩

set_option maxHeartbeats 6400000 in
theorem surj_step
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
    (M : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ)) [IsIso e]
    (heM : e ≫ pullback.snd _ _ = M.toBase)
    [hMne : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) ⁻¹ᵁ
      ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))]
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
    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) ⟶ DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ)))
    (hcomp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hcomp_ci : ∀ i, IsClosedImmersion (comp i))
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) = 𝟙 _)
    (hcomp_w : comp 0 ≫ DRLevel.fibreMap w.hom hw (algebraMap (DRLevel.R q) κ) = comp 1)
    (σ₀ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[κ] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))
    (hσ₀ : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z)
    (hsq0 : chart0 (N₀ := N₀) (q := q) κ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ chart (N₀ := N₀) (q := q) κ)
    [_root_.IsReduced (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))]
    (P : Place κ ↥(modularFunctionFieldC κ N₀)) (hP : P ∈ ssPlaces q N₀ κ) :
    ∃ (n : ↥(pullback (comp 0) (comp 1))) (h₁ : (inv e).base ((pullback.fst (comp 0) (comp 1)).base n) ∈ closedPoints M.C),
      M.placeOfPoint ⟨_, h₁⟩ = P := by

  have hle : modularFunctionFieldFull q ≤ modularFunctionFieldFull (N₀ * q) := by
    apply IntermediateField.adjoin.mono
    rintro x ⟨d, hd, hdq, rfl⟩
    exact ⟨d, hd, hdq.trans (dvd_mul_left q N₀), rfl⟩
  have hmem : modularUnitSeries q ∈ modularFunctionFieldFull (N₀ * q) :=
    hle (ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull q)
  obtain ⟨hvA, -⟩ := ModularCurve.DRModelPackageLevel.modularUnitSeries_mem_chartAlgFin_mul N₀ q hqN hmem
  let v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := ⟨⟨modularUnitSeries q, hmem⟩, hvA⟩
  have hv : ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = modularUnitSeries q := rfl
  obtain ⟨hOa, -, hOc, hOd, hOe₀, hOe₁, hOne⟩ :=
    ModularCurve.IgusaScheme.retraction_one_tmul_modularUnit_eq_prod_ssJSet_of_not_dvd N₀ q hqN κ iota0 hiota theta htheta
      σ₀ hσ₀ v hv
  have hψ_tmul : ∀ (ψ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[κ] κ) (a : κ),
      (1 : κ) ⊗ₜ[DRLevel.R q] IgusaScheme.jChartFin N₀ q - a ⊗ₜ[DRLevel.R q] (1 : ↥(IgusaScheme.chartAlgFin N₀ q)) ∈ RingHom.ker ψ ↔
        ψ ((1 : κ) ⊗ₜ[DRLevel.R q] IgusaScheme.jChartFin N₀ q) = a := by
    intro ψ a
    have h2 : ψ (a ⊗ₜ[DRLevel.R q] (1 : ↥(IgusaScheme.chartAlgFin N₀ q))) = a := by
      have : algebraMap κ (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)) a =
          a ⊗ₜ[DRLevel.R q] (1 : ↥(IgusaScheme.chartAlgFin N₀ q)) := by
        rw [Algebra.TensorProduct.algebraMap_apply]; rfl
      rw [← this, AlgHom.commutes]; rfl
    rw [RingHom.mem_ker, map_sub, h2, sub_eq_zero]
  obtain ⟨-, hB⟩ :=
    ModularCurve.IgusaScheme.ker_comp_atkinLehner_le_comap_retraction_of_mem_ssJSet_of_not_dvd N₀ q hqN κ iota0 hiota theta htheta
      σ₀ hσ₀ v hv
  have hsq1 := comp_one_chart w hw theta hwchart κ comp hcomp_w σ₀ hsq0
  obtain ⟨z, hz⟩ := M.placeOfPoint_bijective.2 P
  have hj : jGeomGen κ N₀ ∈ (M.placeOfPoint z).toValuationSubring := by rw [hz]; exact hP.2.1.1
  have hzr := ModularCurve.DRLevel.mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint N₀ q κ (algebraMap (DRLevel.R q) κ)
    M e hMpin z hj
  obtain ⟨𝔫, h𝔫⟩ : e.base z.1 ∈ Set.range (chart0 (N₀ := N₀) (q := q) κ).base := by
    change _ ∈ Set.range (chartN (q := q) N₀ κ).base
    rw [range_chartN, Set.mem_preimage]
    simpa [Scheme.Hom.comp_apply] using hzr

  have h𝔫cl : IsClosed ({𝔫} : Set (PrimeSpectrum (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)))) := by
    have hecl : IsClosed ({e.base z.1} : Set ↥(DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ))) := by
      have himg : (Scheme.homeoOfIso (asIso e)) '' {z.1} = {e.base z.1} := by
        rw [Set.image_singleton]; rfl
      rw [← himg, Homeomorph.isClosed_image]
      exact z.2
    have hpre : ({𝔫} : Set _) = (chart0 (N₀ := N₀) (q := q) κ).base ⁻¹' {e.base z.1} := by
      ext 𝔫₁
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl; exact h𝔫
      · intro h1; exact (chart0 (N₀ := N₀) (q := q) κ).isOpenEmbedding.injective (h1.trans h𝔫.symm)
    have hcl2 := hecl.preimage (chart0 (N₀ := N₀) (q := q) κ).continuous
    rw [← hpre] at hcl2
    exact hcl2
  haveI : 𝔫.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal 𝔫).mp h𝔫cl
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker_eq (q := q) N₀ κ 𝔫.asIdeal
  obtain ⟨h₃, -, -, hev⟩ := closed_and_read N₀ q hqN κ M e heM hMpin 𝔫 ψ hψ
  have hz' : (inv e).base ((chart0 (N₀ := N₀) (q := q) κ).base 𝔫) = z.1 := by rw [h𝔫, inv_apply_apply]
  have hP3 : M.placeOfPoint ⟨_, h₃⟩ = P := by
    rw [← hz]; congr 1; exact Subtype.ext hz'
  have ha : ψ ((1 : κ) ⊗ₜ[DRLevel.R q] IgusaScheme.jChartFin N₀ q) ∈ ssJSet q κ := by
    rw [← hev, hP3]; exact hP.2.2
  have hja := (hψ_tmul ψ _).mpr rfl
  rw [hψ] at hja
  obtain ⟨𝔫₁, h𝔫₁max, hcomap⟩ := hB 𝔫.asIdeal inferInstance ⟨_, ha, hja⟩

  let 𝔫₁' : PrimeSpectrum (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)) := ⟨𝔫₁, h𝔫₁max.isPrime⟩
  have e0 := comp_base_chart (N₀ := N₀) (q := q) κ hsq0 𝔫
  have e1 := comp_base_chart (N₀ := N₀) (q := q) κ hsq1 𝔫₁'
  have e01 : PrimeSpectrum.comap σ₀.toRingHom 𝔫 = PrimeSpectrum.comap (σ₀.comp (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom)).toRingHom 𝔫₁' := by
    ext1; (have h__af := hcomap.symm; simp [PrimeSpectrum.comap_asIdeal] at h__af; exact h__af)
  obtain ⟨n, hn1, -⟩ := Scheme.Pullback.exists_preimage_pullback ((chart0 (N₀ := N₀) (q := q) κ).base 𝔫)
    ((chart0 (N₀ := N₀) (q := q) κ).base 𝔫₁') (by rw [e0, e1, e01])
  have hfst : (inv e).base ((pullback.fst (comp 0) (comp 1)).base n) = z.1 := by rw [hn1, hz']
  refine ⟨n, hfst ▸ z.2, ?_⟩
  rw [← hz]; congr 1; exact Subtype.ext hfst

theorem main
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
    ∃ nodeEquiv : ↥(pullback (comp 0) (comp 1)) ≃ ↥(ssPlaces q N₀ κ),
      ∀ n : ↥(pullback (comp 0) (comp 1)),
        (∃ h : (inv e).base ((pullback.fst (comp 0) (comp 1)).base n) ∈ closedPoints M.C,
            M.placeOfPoint ⟨_, h⟩ = ((nodeEquiv n : ↥(ssPlaces q N₀ κ)) : Place κ ↥(modularFunctionFieldC κ N₀))) ∧
        (inv e).base ((pullback.snd (comp 0) (comp 1)).base n) ∈ closedPoints M.C := by

  obtain ⟨_inst, rfl⟩ : ∃ _i : Algebra (DRLevel.R q) κ, @algebraMap (DRLevel.R q) κ _ _ _i = toκ := ⟨toκ.toAlgebra, rfl⟩

  haveI hTred : _root_.IsReduced (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) := by
    haveI : AlgebraicGeometry.IsReduced (DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ)) :=
      IgusaScheme.isReduced_pullback_igusaTo_specMap_of_not_dvd N₀ q hqN κ
    haveI := AlgebraicGeometry.isReduced_of_isOpenImmersion (chart (N₀ := N₀) (q := q) κ)
    exact (AlgebraicGeometry.affine_isReduced_iff _).mp this

  haveI := hcomp_ci 1
  haveI : IsClosedImmersion (pullback.fst (comp 0) (comp 1)) := inferInstance
  have hinj_fst : Function.Injective (pullback.fst (comp 0) (comp 1)).base :=
    (pullback.fst (comp 0) (comp 1)).isClosedEmbedding.injective
  have hinj_e : Function.Injective (inv e).base := (inv e).isOpenEmbedding.injective

  obtain ⟨σ₀, hσ₀, hsq0⟩ := ModularCurve.DRLevel.exists_retraction_chart_comp_zero_eq N₀ q hqN π iota0 hiota hpichart κ
    (chart0 (N₀ := N₀) (q := q) κ) (chartN_fst (q := q) N₀ κ) (chartN_snd (q := q) N₀ κ)
    (chart (N₀ := N₀) (q := q) κ) (chartN_fst (q := q) (N₀ * q) κ) (chartN_snd (q := q) (N₀ * q) κ)
    comp hcomp_over hcomp_ci hcomp_pi
  have node := node_step N₀ q hqN w hw theta htheta hwchart π iota0 hiota hpichart κ M e heM hMpin comp hcomp_over hcomp_ci
    hcomp_pi hcomp_w σ₀ hσ₀ hsq0

  let ν : ↥(pullback (comp 0) (comp 1)) → ↥(ssPlaces q N₀ κ) := fun n =>
    ⟨M.placeOfPoint ⟨_, (node n).choose⟩, (node n).choose_spec.choose_spec⟩
  have hν : ∀ n, (ν n : Place κ ↥(modularFunctionFieldC κ N₀)) = M.placeOfPoint ⟨_, (node n).choose⟩ := fun n => rfl
  have hν_inj : Function.Injective ν := by
    intro n n' h
    have h1 : M.placeOfPoint ⟨_, (node n).choose⟩ = M.placeOfPoint ⟨_, (node n').choose⟩ := by
      rw [← hν, ← hν, h]
    have h2 := congrArg Subtype.val (M.placeOfPoint_bijective.1 h1)
    exact hinj_fst (hinj_e h2)

  have hν_surj : Function.Surjective ν := by
    rintro ⟨P, hP⟩
    obtain ⟨n, h₁, hn⟩ := surj_step N₀ q hqN w hw theta htheta hwchart π iota0 hiota hpichart κ M e heM hMpin comp hcomp_over hcomp_ci
      hcomp_pi hcomp_w σ₀ hσ₀ hsq0 P hP
    exact ⟨n, Subtype.ext (by rw [hν]; exact hn)⟩
  exact ⟨Equiv.ofBijective ν ⟨hν_inj, hν_surj⟩, fun n => ⟨⟨(node n).choose, rfl⟩, (node n).choose_spec.choose⟩⟩

end ModularCurve.DRLevel.NodeEnum
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_exists_nodeEquiv_placeOfPoint_eq.ModularCurve P2MW.S_ModularCurve_DRLevel_exists_nodeEquiv_placeOfPoint_eq.ModularCurve.DRLevel P2MW.S_ModularCurve_DRLevel_exists_nodeEquiv_placeOfPoint_eq.ModularCurve.DRLevel.NodeEnum"
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_exists_nodeEquiv_placeOfPoint_eq.ModularCurve P2MW.S_ModularCurve_DRLevel_exists_nodeEquiv_placeOfPoint_eq.ModularCurve.DRLevel"
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_exists_nodeEquiv_placeOfPoint_eq.ModularCurve"

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
    (hcomp_w : comp 0 ≫ DRLevel.fibreMap w.hom hw toκ = comp 1)

    (hfrob : ∀ P : closedPoints M.C,
      ∃ h : (inv e).base ((e ≫ comp 1 ≫ DRLevel.fibreMap0 π toκ).base P.1) ∈ closedPoints M.C,
        M.placeOfPoint ⟨_, h⟩ = arithFrobC q κ N₀ • M.placeOfPoint P) :
    ∃ nodeEquiv : ↥(pullback (comp 0) (comp 1)) ≃ ↥(ssPlaces q N₀ κ),
      ∀ n : ↥(pullback (comp 0) (comp 1)),
        (∃ h : (inv e).base ((pullback.fst (comp 0) (comp 1)).base n) ∈ closedPoints M.C,
            M.placeOfPoint ⟨_, h⟩ = ((nodeEquiv n : ↥(ssPlaces q N₀ κ)) : Place κ ↥(modularFunctionFieldC κ N₀))) ∧
        (∃ h : (inv e).base ((pullback.snd (comp 0) (comp 1)).base n) ∈ closedPoints M.C,
            M.placeOfPoint ⟨_, h⟩ =
              arithFrobC q κ N₀ • ((nodeEquiv n : ↥(ssPlaces q N₀ κ)) : Place κ ↥(modularFunctionFieldC κ N₀))) := by
  obtain ⟨ν, hν⟩ := ModularCurve.DRLevel.NodeEnum.main N₀ q hqN w hw theta htheta hwchart π iota0 hiota hpichart κ toκ M e heM hMpin
    comp hcomp_over hcomp_ci hcomp_pi hcomp_w
  refine ⟨ν, fun n => ⟨(hν n).1, ?_⟩⟩
  exact ModularCurve.DRLevel.NodeEnum.frob_conjunct N₀ q hqN π κ toκ M e comp hcomp_pi hfrob n _ (ν n).2 (hν n).1 (hν n).2

end S_ModularCurve_DRLevel_exists_nodeEquiv_placeOfPoint_eq
end P2MW
export P2MW.S_ModularCurve_DRLevel_exists_nodeEquiv_placeOfPoint_eq (solution)
