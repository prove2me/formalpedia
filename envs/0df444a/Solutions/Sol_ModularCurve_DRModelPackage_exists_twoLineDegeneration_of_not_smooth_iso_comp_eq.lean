-- Prove2me | solution 1 for ModularCurve.DRModelPackage.exists_twoLineDegeneration_of_not_smooth_iso_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9847ddb0-dbfb-5967-833d-6b0f02967922

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_ModularCurve_DRModelLegTwoInputV2
import Theorems.Thm_ModularCurve_IgusaScheme_smooth_pullback_snd_toBase_int_of_isUnit_natCast
import Theorems.Thm_ModularCurve_DRModelPackage_mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero
import Theorems.Thm_ModularCurve_DRModelPackage_isOpenImmersion_restrict_compInf_compl_range_compZero
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_ssJSet_nonempty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_exists_algEquiv_congrRingEquiv_placeInfty_eq_placeOfPoint_zero_eq
import Theorems.Thm_connectedComponentIn_compl_inter_eq_of_isClosed_of_union_eq_univ
import Theorems.Thm_AlgebraicGeometry_exists_fin_eq_of_isClosedImmersion_of_finite_pullback
import Theorems.Thm_ModularCurve_DRModelPackage_exists_twoAffineOpenCover_compl_eq_pair_compInf_compZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_exists_twoLineDegeneration_of_not_smooth_iso_comp_eq
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.toRingAut_coeffSemilinearAut"
p2m_attr_erase "simp" "ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

namespace HbadV5Asm

theorem exists_units_nodes
    {k : Type} [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
    (M : CurveModel k (RatFunc k)) {X : Scheme.{0}}
    (Cinf Czero : M.C ⟶ X) [IsClosedImmersion Cinf] [IsClosedImmersion Czero]
    [Finite ↥(pullback Cinf Czero)]
    (e₁ e₂ : M.C ≅ M.C) (x₁ y₁ x₂ y₂ : closedPoints M.C)
    (he₁x : e₁.hom.base (M.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = x₁.1)
    (he₁y : e₁.hom.base (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1 = y₁.1)
    (he₂x : e₂.hom.base (M.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = x₂.1)
    (he₂y : e₂.hom.base (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1 = y₂.1)
    (hx₁ : Cinf.base x₁.1 ∉ Set.range Czero.base) (hy₁ : Cinf.base y₁.1 ∉ Set.range Czero.base)
    (hx₂ : Czero.base x₂.1 ∉ Set.range Cinf.base) (hy₂ : Czero.base y₂.1 ∉ Set.range Cinf.base) :
    ∃ (n : ℕ) (a b : Fin n → kˣ), Function.Injective a ∧
      (∀ i, (e₁.hom ≫ Cinf).base (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
        (e₂.hom ≫ Czero).base (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
      (∀ (P₁ : M.C) (Q₂ : M.C), (e₁.hom ≫ Cinf).base P₁ = (e₂.hom ≫ Czero).base Q₂ →
        ∃ i, P₁ = (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
          Q₂ = (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) := by
  classical

  haveI : JacobsonSpace ↥(pullback Cinf Czero) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.fst Cinf Czero ≫ M.toBase)
  haveI : DiscreteTopology ↥(pullback Cinf Czero) := inferInstance
  have hclosed : ∀ (P Q : M.C), Cinf.base P = Czero.base Q → IsClosed ({P} : Set M.C) ∧ IsClosed ({Q} : Set M.C) := by
    intro P Q h
    obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := Cinf) (g := Czero) P Q h
    refine ⟨?_, ?_⟩
    · have := (pullback.fst Cinf Czero).isClosedEmbedding.isClosedMap _ (isClosed_discrete ({t} : Set _))
      rwa [Set.image_singleton, show (pullback.fst Cinf Czero).base t = P from ht₁] at this
    · have := (pullback.snd Cinf Czero).isClosedEmbedding.isClosedMap _ (isClosed_discrete ({t} : Set _))
      rwa [Set.image_singleton, show (pullback.snd Cinf Czero).base t = Q from ht₂] at this

  obtain ⟨n, y, z, hy, hyz, honly⟩ :=
    AlgebraicGeometry.exists_fin_eq_of_isClosedImmersion_of_finite_pullback Cinf Czero

  have hunit : ∀ (P : M.C) (hP : IsClosed ({P} : Set M.C)),
      P ≠ (M.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 →
      P ≠ (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1 →
      ∃ c : kˣ, (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k (c : k))).1 = P := by
    intro P hP hinf h0
    rcases AlgebraicCurve.RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty k (M.placeEquiv ⟨P, hP⟩) with ⟨c, hc⟩ | hc
    · have hc0 : c ≠ 0 := by
        rintro rfl
        apply h0
        rw [← hc, Equiv.symm_apply_apply]
      refine ⟨Units.mk0 c hc0, ?_⟩
      rw [Units.val_mk0, ← hc, Equiv.symm_apply_apply]
    · exact absurd (by rw [← hc, Equiv.symm_apply_apply]) hinf

  let P : Fin n → M.C := fun r => e₁.inv.base (y r)
  let Q : Fin n → M.C := fun r => e₂.inv.base (z r)
  have hPclosed : ∀ r, IsClosed ({P r} : Set M.C) := fun r => by
    have := (Scheme.homeoOfIso e₁.symm).isClosedMap _ (hclosed (y r) (z r) (hyz r)).1
    rwa [Set.image_singleton] at this
  have hQclosed : ∀ r, IsClosed ({Q r} : Set M.C) := fun r => by
    have := (Scheme.homeoOfIso e₂.symm).isClosedMap _ (hclosed (y r) (z r) (hyz r)).2
    rwa [Set.image_singleton] at this
  have he₁P : ∀ r, e₁.hom.base (P r) = y r := fun r => Scheme.inv_hom_apply e₁ (y r)
  have he₂Q : ∀ r, e₂.hom.base (Q r) = z r := fun r => Scheme.inv_hom_apply e₂ (z r)
  have hPinf : ∀ r, P r ≠ (M.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 := by
    intro r h
    apply hx₁
    refine ⟨z r, ?_⟩
    rw [← he₁x, ← h, he₁P, hyz]
  have hP0 : ∀ r, P r ≠ (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1 := by
    intro r h
    apply hy₁
    refine ⟨z r, ?_⟩
    rw [← he₁y, ← h, he₁P, hyz]
  have hQinf : ∀ r, Q r ≠ (M.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 := by
    intro r h
    apply hx₂
    refine ⟨y r, ?_⟩
    rw [← he₂x, ← h, he₂Q, hyz]
  have hQ0 : ∀ r, Q r ≠ (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1 := by
    intro r h
    apply hy₂
    refine ⟨y r, ?_⟩
    rw [← he₂y, ← h, he₂Q, hyz]
  choose a ha using fun r => hunit (P r) (hPclosed r) (hPinf r) (hP0 r)
  choose b hb using fun r => hunit (Q r) (hQclosed r) (hQinf r) (hQ0 r)
  refine ⟨n, a, b, ?_, ?_, ?_⟩
  ·
    intro r r' h
    apply hy
    have hPP : P r = P r' := by rw [← ha r, ← ha r', h]
    have := congrArg e₁.hom.base hPP
    rwa [he₁P, he₁P] at this
  · intro r
    rw [ha, hb, Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.comp_app, TopCat.comp_app, he₁P, he₂Q, hyz]
  · intro P₁ Q₂ h
    rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.comp_app, TopCat.comp_app] at h
    obtain ⟨r, hr₁, hr₂⟩ := honly _ _ h
    refine ⟨r, ?_, ?_⟩
    · rw [ha]
      have := congrArg e₁.inv.base hr₁
      rwa [Scheme.hom_inv_apply] at this
    · rw [hb]
      have := congrArg e₂.inv.base hr₂
      rwa [Scheme.hom_inv_apply] at this

theorem exists_iso_placeInfty_placeOfPoint_zero
    {k : Type} [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
    (M : CurveModel k (RatFunc k)) (x y : closedPoints M.C) (hxy : x ≠ y) :
    ∃ e : M.C ≅ M.C, e.hom ≫ M.toBase = M.toBase ∧
      e.hom.base (M.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = x.1 ∧
      e.hom.base (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1 = y.1 := by
  classical
  have hvw : M.placeEquiv x ≠ M.placeEquiv y := fun h => hxy (M.placeEquiv.injective h)
  have hrat : ∀ v : Place k (RatFunc k),
      v = RationalFunctionField.placeInfty k ∨ ∃ c : k, v = RationalFunctionField.placeOfPoint k c := fun v => by
    rcases AlgebraicCurve.RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty k v with h | h
    · exact Or.inr h
    · exact Or.inl h
  obtain ⟨φ, hφinf, hφ0⟩ :=
    AlgebraicCurve.RationalFunctionField.exists_algEquiv_congrRingEquiv_placeInfty_eq_placeOfPoint_zero_eq k
      (M.placeEquiv x) (M.placeEquiv y) hvw (hrat _) (hrat _)
  obtain ⟨e, he, hplace⟩ := AlgebraicCurve.CurveModel.exists_iso_comp_toBase_eq_placeOfPoint_congr_eq φ M M
  refine ⟨e, he, ?_, ?_⟩
  · have h := hplace (M.placeEquiv.symm (RationalFunctionField.placeInfty k))
    rw [← CurveModel.placeEquiv_apply, ← CurveModel.placeEquiv_apply, Equiv.apply_symm_apply, hφinf] at h
    exact congrArg Subtype.val (M.placeEquiv.injective h)
  · have h := hplace (M.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0))
    rw [← CurveModel.placeEquiv_apply, ← CurveModel.placeEquiv_apply, Equiv.apply_symm_apply, hφ0] at h
    exact congrArg Subtype.val (M.placeEquiv.injective h)

variable {k : Type} [Field k]

theorem coe_preimage_comp_eq_compl_singleton
    (M : CurveModel k (RatFunc k)) {X : Scheme.{0}} (f : M.C ⟶ X) (hf : Function.Injective f.base)
    (e : M.C ≅ M.C) (U : X.Opens) (x : M.C) (q : X) (t : M.C)
    (hU : ((U : Set X))ᶜ = {f.base x, q}) (hq : q ∉ Set.range f.base) (hex : e.hom.base t = x) :
    (((e.hom ≫ f) ⁻¹ᵁ U : M.C.Opens) : Set M.C) = {t}ᶜ := by
  ext P
  change (e.hom ≫ f).base P ∈ (U : Set X) ↔ P ∈ ({t} : Set M.C)ᶜ
  rw [Scheme.Hom.comp_base, TopCat.comp_app, Set.mem_compl_iff, Set.mem_singleton_iff]
  have hU' : (U : Set X) = ({f.base x, q} : Set X)ᶜ := by rw [← hU, compl_compl]
  rw [hU', Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨h1, -⟩ rfl
    exact h1 (by rw [hex])
  · intro hP
    refine ⟨fun h => hP ?_, fun h => hq ⟨_, h⟩⟩
    have : e.hom.base P = e.hom.base t := by rw [hex]; exact hf h
    simpa using congrArg e.inv.base this

theorem ne_of_twoAffineOpenCover
    (M : CurveModel k (RatFunc k)) {X : Scheme.{0}} (𝒲 : X.TwoAffineOpenCover) (f : M.C ⟶ X)
    (x y : closedPoints M.C) (qx qy : X)
    (hU0 : ((𝒲.U0 : Set X))ᶜ = {f.base x.1, qx}) (hU1 : ((𝒲.U1 : Set X))ᶜ = {f.base y.1, qy}) :
    x ≠ y := by
  rintro rfl
  have hmem : f.base x.1 ∈ ((𝒲.U0 ⊔ 𝒲.U1 : X.Opens) : Set X) := by
    rw [𝒲.sup_eq_top]; trivial
  rw [TopologicalSpace.Opens.coe_sup] at hmem
  rcases hmem with h | h
  · have : f.base x.1 ∈ ((𝒲.U0 : Set X))ᶜ := by rw [hU0]; exact Set.mem_insert _ _
    exact this h
  · have : f.base x.1 ∈ ((𝒲.U1 : Set X))ᶜ := by rw [hU1]; exact Set.mem_insert _ _
    exact this h

end HbadV5Asm

p2m_open "CategoryTheory.MonoidalCategory AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing"

theorem solution (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)] [CharP k p],
    ¬ Smooth (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) →
    ∃ (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) (i₂ : M₂.C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))
      (_ : IsClosedImmersion i₁) (_ : IsClosedImmersion i₂)
      (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).TwoAffineOpenCover),
      i₁ ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) = M₁.toBase ∧ i₂ ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) = M₂.toBase ∧
      Set.range i₁.base ∪ Set.range i₂.base = Set.univ ∧
      Function.Injective a ∧
      (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
        i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
      (∀ (P₁ : M₁.C) (Q₂ : M₂.C), i₁.base P₁ = i₂.base Q₂ →
        ∃ i, P₁ = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
          Q₂ = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
      IsReduced (pullback i₁ i₂) ∧
      ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
        {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
      ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
        {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
      ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
        {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
      ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
        {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
      i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).1).base (IsLocalRing.closedPoint k) ∧
      Set.range i₁.base ∩ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) =
        connectedComponentIn ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) (((sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).1).base (IsLocalRing.closedPoint k)) ∧
      (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
        (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens)) ∧
      (∀ y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))),
        (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
          y ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens)) ∧
      (∃ W₁ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens, (W₁ : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) = (Set.range i₂.base)ᶜ ∧
        IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)) ∧
      (∃ (e₁ : M₁.C ≅ (𝔛.ratModel k).C) (e₂ : M₂.C ≅ (𝔛.ratModel k).C),
        e₁.hom ≫ 𝔛.compInf k = i₁ ∧ e₂.hom ≫ 𝔛.compZero k = i₂) ∧
      Set.range i₁.base = Set.range (𝔛.compInf k).base ∧
      Set.range i₂.base = Set.range (𝔛.compZero k).base := by
  intro k _ _ _ _ hs
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Flat (DRModel.toBase p) := 𝔛.flat
  haveI : IsProper (DRModel.toBase p) := 𝔛.isProper

  have hpk : ¬ IsUnit ((p : ℕ) : k) := fun h =>
    hs (ModularCurve.IgusaScheme.smooth_pullback_snd_toBase_int_of_isUnit_natCast p k h)
  have hp0 : ((p : ℕ) : k) = 0 := by
    by_contra h
    exact hpk (Ne.isUnit h)
  haveI : IsClosedImmersion (𝔛.compInf k) := 𝔛.compInf_isClosedImmersion k
  haveI : IsClosedImmersion (𝔛.compZero k) := 𝔛.compZero_isClosedImmersion k

  have he_range : ((sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).1).base (IsLocalRing.closedPoint k) ∈ Set.range (𝔛.compInf k).base :=
    𝔛.εinf_mem_compInf k ⟨IsLocalRing.closedPoint k, rfl⟩

  have hSLF : ∀ y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))),
      y ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus) ↔
        ¬ (y ∈ Set.range (𝔛.compInf k).base ∧ y ∈ Set.range (𝔛.compZero k).base) :=
    ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛 k
  have hUs : ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus :
      (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) = (Set.range (𝔛.compInf k).base ∩ Set.range (𝔛.compZero k).base)ᶜ := by
    ext y
    exact hSLF y

  have hC16 := ModularCurve.DRModelPackage.isOpenImmersion_restrict_compInf_compl_range_compZero p 𝔛 k

  haveI hfin : Finite ↥(pullback (𝔛.compInf k) (𝔛.compZero k)) := by
    apply Nat.finite_of_card_ne_zero
    rw [𝔛.crossing_card k]
    haveI : Finite ↥(ssJSet p k) := (ModularCurve.ssJSet_finite p k).to_subtype
    haveI : Nonempty ↥(ssJSet p k) := (ModularCurve.ssJSet_nonempty (q := p) (k := k)).to_subtype
    exact Nat.card_pos.ne'

  obtain ⟨𝒲₀, x₁, y₁, x₂, y₂, hx₁e', hU0, hU1, hx₁, hx₂, hy₁, hy₂⟩ :=
    ModularCurve.DRModelPackage.exists_twoAffineOpenCover_compl_eq_pair_compInf_compZero p 𝔛 k
  have hx₁e : (𝔛.compInf k).base x₁.1 =
      ((sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).1).base (IsLocalRing.closedPoint k) := hx₁e'

  have hU0' : ((𝒲₀.U0 : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))))ᶜ = {(𝔛.compZero k).base x₂.1, (𝔛.compInf k).base x₁.1} := by rw [hU0, Set.pair_comm]
  have hU1' : ((𝒲₀.U1 : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))))ᶜ = {(𝔛.compZero k).base y₂.1, (𝔛.compInf k).base y₁.1} := by rw [hU1, Set.pair_comm]
  obtain ⟨e₁, he₁, he₁x, he₁y⟩ := HbadV5Asm.exists_iso_placeInfty_placeOfPoint_zero (𝔛.ratModel k) x₁ y₁
    (HbadV5Asm.ne_of_twoAffineOpenCover (𝔛.ratModel k) 𝒲₀ (𝔛.compInf k) x₁ y₁ _ _ hU0 hU1)
  obtain ⟨e₂, he₂, he₂x, he₂y⟩ := HbadV5Asm.exists_iso_placeInfty_placeOfPoint_zero (𝔛.ratModel k) x₂ y₂
    (HbadV5Asm.ne_of_twoAffineOpenCover (𝔛.ratModel k) 𝒲₀ (𝔛.compZero k) x₂ y₂ _ _ hU0' hU1')
  haveI : IsClosedImmersion (e₁.hom ≫ 𝔛.compInf k) := inferInstance
  haveI : IsClosedImmersion (e₂.hom ≫ 𝔛.compZero k) := inferInstance
  have hinj₁ : Function.Injective (𝔛.compInf k).base := (𝔛.compInf k).isClosedEmbedding.injective
  have hinj₂ : Function.Injective (𝔛.compZero k).base := (𝔛.compZero k).isClosedEmbedding.injective
  have hr₁ : Set.range (e₁.hom ≫ 𝔛.compInf k).base = Set.range (𝔛.compInf k).base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]; exact (Scheme.homeoOfIso e₁).surjective.range_comp _
  have hr₂ : Set.range (e₂.hom ≫ 𝔛.compZero k).base = Set.range (𝔛.compZero k).base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]; exact (Scheme.homeoOfIso e₂).surjective.range_comp _

  obtain ⟨n, a, b, ha, hcross, honly⟩ := HbadV5Asm.exists_units_nodes (𝔛.ratModel k) (𝔛.compInf k) (𝔛.compZero k)
    e₁ e₂ x₁ y₁ x₂ y₂ he₁x he₁y he₂x he₂y hx₁ hy₁ hx₂ hy₂
  refine ⟨𝔛.ratModel k, 𝔛.ratModel k, e₁.hom ≫ 𝔛.compInf k, e₂.hom ≫ 𝔛.compZero k, inferInstance, inferInstance,
    n, a, b, 𝒲₀, ?_, ?_, ?_, ha, hcross, honly, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨e₁, e₂, rfl, rfl⟩, hr₁, hr₂⟩
  ·
    rw [Category.assoc, 𝔛.compInf_over k, he₁]
  ·
    rw [Category.assoc, 𝔛.compZero_over k, he₂]
  ·
    rw [hr₁, hr₂, Set.eq_univ_iff_forall]
    exact fun x => 𝔛.comp_jointly_surjective k x
  ·
    haveI : IsReduced (pullback (𝔛.compInf k) (𝔛.compZero k)) := 𝔛.crossing_reduced k
    exact isReduced_of_isOpenImmersion
      (pullback.map (e₁.hom ≫ 𝔛.compInf k) (e₂.hom ≫ 𝔛.compZero k) (𝔛.compInf k) (𝔛.compZero k) e₁.hom e₂.hom (𝟙 _)
        (by simp) (by simp))
  ·
    exact HbadV5Asm.coe_preimage_comp_eq_compl_singleton (𝔛.ratModel k) (𝔛.compInf k) hinj₁ e₁ 𝒲₀.U0 x₁.1 _ _ hU0 hx₂ he₁x
  ·
    exact HbadV5Asm.coe_preimage_comp_eq_compl_singleton (𝔛.ratModel k) (𝔛.compZero k) hinj₂ e₂ 𝒲₀.U0 x₂.1 _ _ hU0' hx₁ he₂x
  ·
    exact HbadV5Asm.coe_preimage_comp_eq_compl_singleton (𝔛.ratModel k) (𝔛.compInf k) hinj₁ e₁ 𝒲₀.U1 y₁.1 _ _ hU1 hy₂ he₁y
  ·
    exact HbadV5Asm.coe_preimage_comp_eq_compl_singleton (𝔛.ratModel k) (𝔛.compZero k) hinj₂ e₂ 𝒲₀.U1 y₂.1 _ _ hU1' hy₁ he₂y
  ·
    rw [Scheme.Hom.comp_base, TopCat.comp_app, he₁x, hx₁e]
  ·
    rw [hUs, hr₁]
    symm
    refine connectedComponentIn_compl_inter_eq_of_isClosed_of_union_eq_univ
      (𝔛.compInf k).isClosedEmbedding.isClosed_range (𝔛.compZero k).isClosedEmbedding.isClosed_range ?_ ?_ ?_
    · rw [Set.eq_univ_iff_forall]
      exact fun x => 𝔛.comp_jointly_surjective k x
    ·
      have hopen : IsOpen ((𝔛.compInf k).base ⁻¹' Set.range (𝔛.compZero k).base)ᶜ :=
        ((𝔛.compZero k).isClosedEmbedding.isClosed_range.preimage (𝔛.compInf k).base.hom.continuous).isOpen_compl
      have himg : Set.range (𝔛.compInf k).base \ Set.range (𝔛.compZero k).base =
          (𝔛.compInf k).base '' ((𝔛.compInf k).base ⁻¹' Set.range (𝔛.compZero k).base)ᶜ := by
        ext z
        constructor
        · rintro ⟨⟨P, rfl⟩, hz⟩
          exact ⟨P, hz, rfl⟩
        · rintro ⟨P, hP, rfl⟩
          exact ⟨⟨P, rfl⟩, hP⟩
      rw [himg]
      exact ((IrreducibleSpace.isIrreducible_univ _).isPreirreducible.open_subset hopen (Set.subset_univ _)).image _
        (𝔛.compInf k).base.hom.continuous.continuousOn |>.isPreconnected
    · exact ⟨he_range, fun h => hx₁ (hx₁e ▸ h)⟩
  ·
    intro i
    rw [hSLF, not_not]
    refine ⟨?_, ?_⟩
    · rw [← hr₁]; exact ⟨_, rfl⟩
    · rw [hcross i, ← hr₂]; exact ⟨_, rfl⟩
  ·
    intro y hy
    rw [hSLF]
    rintro ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩
    obtain ⟨i, hi, -⟩ := honly (e₁.inv.base P) (e₂.inv.base Q) (by
      rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.comp_app, TopCat.comp_app,
        Scheme.inv_hom_apply, Scheme.inv_hom_apply, hP, hQ])
    apply hy i
    rw [← hi, Scheme.Hom.comp_base, TopCat.comp_app, Scheme.inv_hom_apply, hP]
  ·
    refine ⟨⟨(Set.range (e₂.hom ≫ 𝔛.compZero k).base)ᶜ, ?_⟩, rfl, ?_⟩
    · rw [hr₂]; exact (𝔛.compZero k).isClosedEmbedding.isClosed_range.isOpen_compl
    · have hW₁ : (⟨(Set.range (e₂.hom ≫ 𝔛.compZero k).base)ᶜ, by rw [hr₂]; exact (𝔛.compZero k).isClosedEmbedding.isClosed_range.isOpen_compl⟩ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) =
          ⟨(Set.range (𝔛.compZero k).base)ᶜ, (𝔛.compZero k).isClosedEmbedding.isClosed_range.isOpen_compl⟩ := by
        ext1; exact congrArg compl hr₂
      rw [hW₁]
      have hfac : ((e₁.hom ≫ 𝔛.compInf k) ⁻¹ᵁ (⟨(Set.range (𝔛.compZero k).base)ᶜ, (𝔛.compZero k).isClosedEmbedding.isClosed_range.isOpen_compl⟩ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens)).ι ≫ (e₁.hom ≫ 𝔛.compInf k) =
          (e₁.hom ∣_ ((𝔛.compInf k) ⁻¹ᵁ (⟨(Set.range (𝔛.compZero k).base)ᶜ, (𝔛.compZero k).isClosedEmbedding.isClosed_range.isOpen_compl⟩ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens))) ≫ ((((𝔛.compInf k) ⁻¹ᵁ (⟨(Set.range (𝔛.compZero k).base)ᶜ, (𝔛.compZero k).isClosedEmbedding.isClosed_range.isOpen_compl⟩ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens))).ι ≫ 𝔛.compInf k) := by
        rw [morphismRestrict_ι_assoc]; rfl
      rw [hfac]
      haveI hiso : IsIso (e₁.hom ∣_ ((𝔛.compInf k) ⁻¹ᵁ (⟨(Set.range (𝔛.compZero k).base)ᶜ, (𝔛.compZero k).isClosedEmbedding.isClosed_range.isOpen_compl⟩ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens))) := inferInstance
      exact (@MorphismProperty.cancel_left_of_respectsIso _ _ @IsOpenImmersion inferInstance _ _ _ _ _ hiso).mpr hC16

end S_ModularCurve_DRModelPackage_exists_twoLineDegeneration_of_not_smooth_iso_comp_eq
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_exists_twoLineDegeneration_of_not_smooth_iso_comp_eq (solution)
