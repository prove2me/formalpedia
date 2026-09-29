-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_oneSidedPool_baseChange_of_levelPolynomials
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/af33a501-268a-55ad-80d5-5c2bdaa6377e

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Theorems.Thm_ModularCurve_DRModelPackageLevel_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top
import Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_connectedComponentIn_baseChange_of_fst_eq_iotaFin
import Theorems.Thm_ModularCurve_DRModelPackageLevel_iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top
import Theorems.Thm_ModularCurve_DRModelPackageLevel_range_cuspInf_inter_range_iotaFin_eq_empty_and_range_cuspZero_inter_range_iotaFin_eq_empty
import Theorems.Thm_Algebra_Etale_exists_faithfullyFlat_forall_nonempty_algEquiv_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_oneSidedPool_baseChange_of_levelPolynomials
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure"
p2m_attr_erase "instance" "instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian"
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve TensorProduct
p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel"
p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel.neZero_mul DRModelPackageLevel IgusaScheme.chartAlgFin IgusaScheme IgusaScheme.ιFin IgusaScheme.ιFin_igusaTo"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "neZero_mul isProper εzero εinf mk w comp w_over theta smoothLocus iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top mem_connectedComponentIn_baseChange_of_fst_eq_iotaFin iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top range_cuspInf_inter_range_iotaFin_eq_empty_and_range_cuspZero_inter_range_iotaFin_eq_empty"
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

namespace NearGeomAux

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔓 : DRModelPackageLevel N₀ q hqN) (f : R q)

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

scoped instance instCommRingChart : CommRing ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := Subalgebra.toCommRing (IgusaScheme.chartAlgFin (N₀ * q) q)

section Chart

variable (I : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q))

def ζ : Spec (CommRingCat.of (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)) ⟶ X N₀ q :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ IgusaScheme.ιFin (N₀ * q) q

theorem ζ_toBase : ζ I ≫ toBase N₀ q = Spec.map (CommRingCat.ofHom (algebraMap (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I))) := by
  unfold ζ; rw [Category.assoc]
  erw [IgusaScheme.ιFin_igusaTo]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem range_ζ : Set.range (ζ I).base =
    (IgusaScheme.ιFin (N₀ * q) q).base '' (PrimeSpectrum.zeroLocus (I : Set ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) := by
  unfold ζ
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  congr 1
  change Set.range (PrimeSpectrum.comap (R := ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (S := ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I) (Ideal.Quotient.mk I)) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

theorem range_ζ_subset_range_ιFin : Set.range (ζ I).base ⊆ Set.range (IgusaScheme.ιFin (N₀ * q) q).base := by
  rw [range_ζ]; exact Set.image_subset_range _ _

theorem exists_eq_ιFin_of_mem_range_ζ {x : ↥(X N₀ q)} (hx : x ∈ Set.range (ζ I).base) :
    ∃ 𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q), I ≤ 𝔮.asIdeal ∧ x = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 := by
  rw [range_ζ] at hx
  obtain ⟨𝔮, h𝔮, rfl⟩ := hx
  exact ⟨𝔮, fun a ha => h𝔮 ha, rfl⟩

theorem disjoint_range_ζ {I J : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q)} (h : I ⊔ J = ⊤) : Disjoint (Set.range (ζ I).base) (Set.range (ζ J).base) := by
  rw [Set.disjoint_iff]
  rintro x ⟨hxI, hxJ⟩
  obtain ⟨𝔮, hI, rfl⟩ := exists_eq_ιFin_of_mem_range_ζ I hxI
  obtain ⟨𝔮', hJ, he⟩ := exists_eq_ιFin_of_mem_range_ζ J hxJ
  have hinj := (IgusaScheme.ιFin (N₀ * q) q).isOpenEmbedding.injective he
  subst hinj
  exact 𝔮.isPrime.ne_top (top_le_iff.1 (h ▸ sup_le hI hJ))

include 𝔓 in

theorem isClosedImmersion_ζ [Module.Finite (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)] : IsClosedImmersion (ζ I) := by
  haveI :=
    @IsClosedImmersion.spec_of_surjective (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (CommRingCat.of (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I))
      (CommRingCat.ofHom (Ideal.Quotient.mk I)) (Ideal.Quotient.mk_surjective (I := I))
  haveI : IsPreimmersion (ζ I) := by unfold ζ; infer_instance
  haveI := 𝔓.isProper
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)))) := by
    rw [IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := R q) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)).mpr inferInstance
  haveI : UniversallyClosed (ζ I ≫ toBase N₀ q) := by rw [ζ_toBase]; infer_instance
  haveI : UniversallyClosed (ζ I) := .of_comp_of_isSeparated _ (toBase N₀ q)
  exact .of_isPreimmersion _ (ζ I).isClosedMap.isClosed_range

end Chart

section BaseChangeL

variable (I : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q))

theorem ζ_toBase' : specMap (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I) = ζ I ≫ toBase N₀ q := (ζ_toBase I).symm

def zL : Spec (CommRingCat.of (TensorProduct (R q) (Localization.Away f) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I))) ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)) :=
  (pullbackSpecIso (R q) (Localization.Away f) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)).inv ≫
    (pullbackSymmetry _ _).hom ≫
    pullback.map (specMap (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)) (specMap (R q) (Localization.Away f)) (toBase N₀ q)
      (specMap (R q) (Localization.Away f)) (ζ I) (𝟙 _) (𝟙 _)
      ((Category.comp_id _).trans (ζ_toBase' I)) ((Category.comp_id _).trans (Category.id_comp _).symm)

theorem zL_snd : zL f I ≫ baseChange (R q) (toBase N₀ q) (Localization.Away f) =
    specMap (Localization.Away f) (TensorProduct (R q) (Localization.Away f) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)) := by
  unfold zL
  rw [Category.assoc, Category.assoc]
  erw [pullback.lift_snd]
  rw [Category.comp_id, pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst']

theorem zL_fst : zL f I ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f)) =
    ((pullbackSpecIso (R q) (Localization.Away f) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)).inv ≫ pullback.snd _ _) ≫ ζ I := by
  unfold zL
  rw [Category.assoc, Category.assoc, Category.assoc]
  erw [pullback.lift_fst]
  rw [pullbackSymmetry_hom_comp_fst_assoc]

theorem fst_mem_range_ζ_of_mem_range_zL {x : ↥(pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)))}
    (hx : x ∈ Set.range (zL f I).base) :
    (pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))).base x ∈ Set.range (ζ I).base := by
  obtain ⟨t, rfl⟩ := hx
  rw [← Scheme.Hom.comp_apply, zL_fst, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

include 𝔓 in
theorem isClosedImmersion_zL [Module.Finite (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)] : IsClosedImmersion (zL f I) := by
  haveI := isClosedImmersion_ζ 𝔓 I
  have h := MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (f := specMap (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)) (g := specMap (R q) (Localization.Away f)) (f' := toBase N₀ q)
    (g' := specMap (R q) (Localization.Away f)) (i₁ := ζ I) (i₂ := 𝟙 _)
    inferInstance inferInstance (ζ_toBase' I) (Category.id_comp _).symm
  unfold zL
  infer_instance

end BaseChangeL

section Disjoint

variable (I J : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q))

theorem exists_eq_ιFin_of_mem_range_zL {x : ↥(pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)))}
    (hx : x ∈ Set.range (zL f I).base) :
    ∃ 𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q), I ≤ 𝔮.asIdeal ∧
      (pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))).base x = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 :=
  exists_eq_ιFin_of_mem_range_ζ I (fst_mem_range_ζ_of_mem_range_zL f I hx)

theorem disjoint_range_zL {I J : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q)} (h : I ⊔ J = ⊤) :
    Disjoint (Set.range (zL f I).base) (Set.range (zL f J).base) := by
  rw [Set.disjoint_iff]
  rintro x ⟨hxI, hxJ⟩
  exact Set.disjoint_iff.1 (disjoint_range_ζ h) ⟨fst_mem_range_ζ_of_mem_range_zL f I hxI, fst_mem_range_ζ_of_mem_range_zL f J hxJ⟩

theorem disjoint_range_zL_range_sectionBaseChange (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q))
    (hε : Set.range ε.1.base ∩ Set.range (IgusaScheme.ιFin (N₀ * q) q).base = ∅) :
    Disjoint (Set.range (zL f I).base) (Set.range (sectionBaseChange (Localization.Away f) ε).1.base) := by
  rw [Set.disjoint_iff]
  rintro x ⟨hxI, ⟨t, rfl⟩⟩
  have h1 := range_ζ_subset_range_ιFin I (fst_mem_range_ζ_of_mem_range_zL f I hxI)
  have h2 : (pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))).base
      ((sectionBaseChange (Localization.Away f) ε).1.base t) ∈ Set.range ε.1.base := by
    rw [← Scheme.Hom.comp_apply, sectionBaseChange_coe_fst, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have : _ ∈ Set.range ε.1.base ∩ Set.range (IgusaScheme.ιFin (N₀ * q) q).base := ⟨h2, h1⟩
  rw [hε] at this
  exact this

abbrev wL : pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)) ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)) :=
  curveChange 𝔓.w.hom 𝔓.w_over (specMap (R q) (Localization.Away f))

theorem wL_fst : wL 𝔓 f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔓.w.hom := by
  unfold wL curveChange; rw [pullback.lift_fst]

theorem disjoint_range_zL_range_zL_wL {I J : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q)}
    (h : ∀ 𝔮 𝔮' : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q), I ≤ 𝔮.asIdeal → J ≤ 𝔮'.asIdeal →
      (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 ≠ 𝔓.w.hom.base ((IgusaScheme.ιFin (N₀ * q) q).base 𝔮')) :
    Disjoint (Set.range (zL f I).base) (Set.range (zL f J ≫ wL 𝔓 f).base) := by
  rw [Set.disjoint_iff]
  rintro x ⟨hxI, ⟨t, rfl⟩⟩
  obtain ⟨𝔮, hI, h𝔮⟩ := exists_eq_ιFin_of_mem_range_zL f I hxI
  obtain ⟨𝔮', hJ, h𝔮'⟩ := exists_eq_ιFin_of_mem_range_zL f J (x := (zL f J).base t) ⟨t, rfl⟩
  apply h 𝔮 𝔮' hI hJ
  rw [← h𝔮, ← h𝔮', Scheme.Hom.comp_apply]
  erw [← Scheme.Hom.comp_apply (wL 𝔓 f) (pullback.fst _ _), wL_fst, Scheme.Hom.comp_apply]

end Disjoint

section Data

abbrev lev (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (p : ℤ[X]) : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q) :=
  Ideal.span {Polynomial.aeval v p}

theorem theta_aeval (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (p : ℤ[X]) :
    𝔓.theta (Polynomial.aeval v p) = Polynomial.aeval (𝔓.theta v) p :=
  (Polynomial.aeval_algHom_apply (𝔓.theta.toAlgHom.toRingHom.toIntAlgHom) v p).symm

theorem not_mem_of_sup_span_singleton_eq_top {I : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q)} {v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)}
    (h : I ⊔ Ideal.span {v} = ⊤) (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (hI : I ≤ 𝔮.asIdeal) :
    v ∉ 𝔮.asIdeal := fun hv =>
  𝔮.isPrime.ne_top (top_le_iff.1 (h ▸ sup_le hI ((Ideal.span_singleton_le_iff_mem _).2 hv)))

variable (I : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q))

abbrev BL : Type := TensorProduct (R q) (Localization.Away f) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ I)

end Data

section Generic

variable (S T M : Type) [CommRing S] [CommRing T] [Algebra S T] [CommRing M] [Algebra S M]

theorem finite_bc [Module.Finite S M] : Module.Finite T (TensorProduct S T M) := inferInstance

theorem etale_bc [Algebra.Etale S M] : Algebra.Etale T (TensorProduct S T M) := inferInstance

theorem rankAtStalk_bc [Module.Free S M] [Module.Finite S M] [Nontrivial S] (n : ℕ) (hn : Module.finrank S M = n) :
    Module.rankAtStalk (R := T) (TensorProduct S T M) = n := by
  rw [Module.rankAtStalk_eq_finrank_of_free]
  funext p
  haveI : Nontrivial T := by
    by_contra hT
    rw [not_nontrivial_iff_subsingleton] at hT
    exact p.isPrime.ne_top (Subsingleton.elim _ _)
  change Module.finrank T (TensorProduct S T M) = n
  rw [Module.finrank_baseChange, hn]

end Generic

section Family
variable (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) {M : ℕ} (g : Fin M → ℤ[X])

abbrev famB (i : Fin M) : Type := BL f (lev v (g i))

end Family

end NearGeomAux
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve.DRModelPackageLevel.NearGeomAux"

end ModularCurve.DRModelPackageLevel
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve.DRModelPackageLevel.NearGeomAux P2MW.S_ModularCurve_DRModelPackageLevel_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve.DRModelPackageLevel"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve.DRModelPackageLevel.NearGeomAux P2MW.S_ModularCurve_DRModelPackageLevel_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve.DRModelPackageLevel.NearGeomAux P2MW.S_ModularCurve_DRModelPackageLevel_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve.DRModelPackageLevel"

open _root_.ModularCurve.DRModelPackageLevel _root_.P2MW.S_ModularCurve_DRModelPackageLevel_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve.DRModelPackageLevel ModularCurve.DRModelPackageLevel.NearGeomAux in
attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) (f : R q)
    (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hdict : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ)
      (y : ↥(fibre (N₀ := N₀) toκ)) (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)),
      (pullback.fst (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base y = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 →
      v ∉ 𝔮.asIdeal → y ∈ Set.range (𝔓.comp κ toκ 0).base ∧ y ∉ Set.range (𝔓.comp κ toκ 1).base)
    (b M : ℕ) (g : Fin M → ℤ[X]) (rk : Fin M → ℕ)
    (hmonic : ∀ i, (g i).Monic)
    (hfin : ∀ i, Module.Finite (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)})) (het : ∀ i, Algebra.Etale (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)}))
    (hfree : ∀ i, Module.Free (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)})) (hrk : ∀ i, Module.finrank (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)}) = rk i)
    (hrk1 : ∀ i, 1 ≤ rk i) (hrkb : ∀ i, rk i ≤ b)
    (hcop : Pairwise fun i j => Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {Polynomial.aeval v (g j)} = (⊤ : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q)))
    (hcopw : ∀ i j, Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {Polynomial.aeval (𝔓.theta v) (g j)} = (⊤ : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q)))
    (hcopv : ∀ i, Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {v} = (⊤ : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra (R q) R') (_ : Algebra (Localization.Away f) R')
      (_ : IsScalarTower (R q) (Localization.Away f) R')
      (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
      (_ : Module.FaithfullyFlat (Localization.Away f) R')
      (B : Fin M → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
      (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
      (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
      (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z i)),
      (∀ i, z i ≫ baseChange (R q) (toBase N₀ q) (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
      (∀ i, Set.range (z i).base ⊆
      ((pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f)) ⁻¹ᵁ 𝔓.smoothLocus : (pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))).Opens) :
        Set ↥(pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
              (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εinf) s).1).base (IsLocalRing.closedPoint k))) ∧
      (∀ i, Disjoint (Set.range (z i).base) (Set.range (sectionBaseChange (Localization.Away f) 𝔓.εinf).1.base)) ∧
      (∀ i, Disjoint (Set.range (z i).base) (Set.range (sectionBaseChange (Localization.Away f) 𝔓.εzero).1.base)) ∧
      (∀ i j, Disjoint (Set.range (z i).base)
      (Set.range (z j ≫ curveChange 𝔓.w.hom 𝔓.w_over (specMap (R q) (Localization.Away f))).base))  := by
  classical
  haveI : ∀ i, Module.Finite (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ lev v (g i)) := hfin
  haveI : ∀ i, Algebra.Etale (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ lev v (g i)) := het
  haveI : ∀ i, Module.Free (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ lev v (g i)) := hfree
  obtain ⟨R', _, _, hR'fin, hR'et, hR'ff, hφ⟩ :=
    @Algebra.Etale.exists_faithfullyFlat_forall_nonempty_algEquiv_pi (Localization.Away f) _ (Fin M) _ (famB f v g) _ _
      (fun i => finite_bc (R q) (Localization.Away f) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ lev v (g i)))
      (fun i => etale_bc (R q) (Localization.Away f) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ lev v (g i)))
      rk (fun i => rankAtStalk_bc (R q) (Localization.Away f) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ lev v (g i)) (rk i) (hrk i))
  letI : Algebra (R q) R' := ((algebraMap (Localization.Away f) R').comp (algebraMap (R q) (Localization.Away f))).toAlgebra
  haveI : IsScalarTower (R q) (Localization.Away f) R' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hN6 := range_cuspInf_inter_range_iotaFin_eq_empty_and_range_cuspZero_inter_range_iotaFin_eq_empty N₀ q hqN 𝔓
  refine ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, hR'fin, hR'et, hR'ff,
    famB f v g, inferInstance, inferInstance,
    fun i => finite_bc (R q) (Localization.Away f) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ lev v (g i)),
    fun i => etale_bc (R q) (Localization.Away f) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ lev v (g i)), rk, hrk1, hrkb,
    fun i => (hφ i).some, fun i => zL f (lev v (g i)), fun i => isClosedImmersion_zL 𝔓 f (lev v (g i)),
    fun i => zL_snd f (lev v (g i)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i x hx
    obtain ⟨𝔮, hI, hq⟩ := exists_eq_ιFin_of_mem_range_zL f (lev v (g i)) hx
    show (pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))).base x ∈ (𝔓.smoothLocus : Set ↥(X N₀ q))
    rw [hq]
    exact iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top N₀ q hqN 𝔓 v hdict (lev v (g i)) (hcopv i) 𝔮 hI
  ·
    intro i j hij
    exact disjoint_range_zL f (hcop hij)
  ·
    intro k _ _ s i y hy
    obtain ⟨𝔮, hI, hq⟩ := exists_eq_ιFin_of_mem_range_zL f (lev v (g i)) hy
    exact mem_connectedComponentIn_baseChange_of_fst_eq_iotaFin N₀ q hqN 𝔓 f v hdict k s y 𝔮
      (not_mem_of_sup_span_singleton_eq_top (hcopv i) 𝔮 hI)
      (iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top N₀ q hqN 𝔓 v hdict (lev v (g i)) (hcopv i) 𝔮 hI)
      (by rw [Scheme.Hom.comp_apply]; exact hq)
  ·
    intro i
    exact disjoint_range_zL_range_sectionBaseChange f (lev v (g i)) 𝔓.εinf hN6.1
  ·
    intro i
    exact disjoint_range_zL_range_sectionBaseChange f (lev v (g i)) 𝔓.εzero hN6.2
  ·
    intro i j
    refine disjoint_range_zL_range_zL_wL 𝔓 f (fun 𝔮 𝔮' hI hJ => ?_)
    have hab : Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {𝔓.theta (Polynomial.aeval v (g j))} = ⊤ := by
      rw [theta_aeval]; exact hcopw i j
    exact iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top N₀ q hqN 𝔓 _ _ hab 𝔮 𝔮'
      ((Ideal.span_singleton_le_iff_mem _).1 hI) ((Ideal.span_singleton_le_iff_mem _).1 hJ)

end S_ModularCurve_DRModelPackageLevel_exists_oneSidedPool_baseChange_of_levelPolynomials
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_oneSidedPool_baseChange_of_levelPolynomials (solution)
