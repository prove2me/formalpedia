-- Prove2me | solution 1 for ModularCurve.DRModelPackage.exists_locallySplitPools_of_le_span_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/719e2b38-366b-5ded-aaed-432971c3f8e7

import Mathlib
import Theorems.Thm_ModularCurve_HpoolLevelRing_exists_finite_etale_levelRing_jChartFin
import Theorems.Thm_Polynomial_exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime
import Theorems.Thm_Algebra_Etale_exists_faithfullyFlat_forall_nonempty_algEquiv_pi
import Theorems.Thm_ModularCurve_IgusaScheme_geometricallyConnected_toBase_int
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_of_ne
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.CharPModel.FibreModel.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub"
p2m_attr_erase "simp" "CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_of_ne.ModularCurve AlgebraicCurve IsLocalRing"

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

universe u

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_of_ne.ModularCurve AlgebraicCurve"
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard

namespace ModularCurve
p2m_export "ModularCurve" "HpoolLevelRing.exists_finite_etale_levelRing_jChartFin HpoolLevelRing.neZero_of_fact_prime HpoolLevelRing.Afin HpoolLevelRing.AfinAway HpoolLevelRing.levelRing modularFunctionFieldFull IgusaScheme.jFull IgusaScheme IgusaScheme.geometricallyConnected_toBase_int DRModel DRModel.toBase DRModelPackage"
namespace HpoolGeo
p2m_open "ModularCurve"

variable (p : ℕ) [Fact p.Prime] (f : ℤ)

attribute [local instance] HpoolLevelRing.neZero_of_fact_prime

set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldFull p)
set_option quotPrecheck false in
local notation "jj" => IgusaScheme.jFull p
set_option quotPrecheck false in
local notation "LL" => Localization.Away f
set_option quotPrecheck false in
local notation "AA" => HpoolLevelRing.Afin p
set_option quotPrecheck false in
local notation "AF" => HpoolLevelRing.AfinAway p f

theorem algebraMap_comp_eq :
    (algebraMap LL AF).comp (algebraMap ℤ LL) = (algebraMap AA AF).comp (algebraMap ℤ AA) :=
  RingHom.ext_int _ _

noncomputable def ιL : Spec (CommRingCat.of AF) ⟶ pullback (DRModel.toBase p) (specMap ℤ LL) :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (algebraMap AA AF)) ≫ TwoChartIntegralModel.ιFin ℤ FF jj)
    (Spec.map (CommRingCat.ofHom (algebraMap LL AF)))
    (by
      rw [Category.assoc]
      erw [TwoChartIntegralModel.ιFin_toBase]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        algebraMap_comp_eq])

@[scoped simp] theorem ιL_fst :
    ιL p f ≫ pullback.fst (DRModel.toBase p) (specMap ℤ LL) =
      Spec.map (CommRingCat.ofHom (algebraMap AA AF)) ≫ TwoChartIntegralModel.ιFin ℤ FF jj :=
  pullback.lift_fst _ _ _

@[scoped simp] theorem ιL_snd :
    ιL p f ≫ pullback.snd (DRModel.toBase p) (specMap ℤ LL) = Spec.map (CommRingCat.ofHom (algebraMap LL AF)) :=
  pullback.lift_snd _ _ _

theorem ιL_baseChange :
    ιL p f ≫ baseChange ℤ (DRModel.toBase p) LL = Spec.map (CommRingCat.ofHom (algebraMap LL AF)) :=
  ιL_snd p f

scoped instance isOpenImmersion_specMap_away : IsOpenImmersion (specMap ℤ LL) :=
  IsOpenImmersion.of_isLocalization f

scoped instance isOpenImmersion_ιL : IsOpenImmersion (ιL p f) := by
  have h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap AA AF))) :=
    IsOpenImmersion.of_isLocalization (algebraMap ℤ AA f)
  have h2 : IsOpenImmersion (ιL p f ≫ pullback.fst (DRModel.toBase p) (specMap ℤ LL)) := by
    rw [ιL_fst]; infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst (DRModel.toBase p) (specMap ℤ LL))

noncomputable def zOf (I : Ideal AF) : Spec (CommRingCat.of (AF ⧸ I)) ⟶ pullback (DRModel.toBase p) (specMap ℤ LL) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ ιL p f

theorem zOf_baseChange (I : Ideal AF) :
    zOf p f I ≫ baseChange ℤ (DRModel.toBase p) LL = specMap LL (AF ⧸ I) := by
  rw [zOf, Category.assoc, ιL_baseChange, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem isClosedImmersion_zOf (I : Ideal AF) [Module.Finite LL (AF ⧸ I)]
    [IsSeparated (DRModel.toBase p)] : IsClosedImmersion (zOf p f I) := by
  have hmono : Mono (zOf p f I) := by
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    unfold zOf; infer_instance
  have hfin : IsFinite (specMap LL (AF ⧸ I)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hproper : IsProper (zOf p f I) := by
    have : IsProper (zOf p f I ≫ baseChange ℤ (DRModel.toBase p) LL) := by
      rw [zOf_baseChange]; infer_instance
    exact IsProper.of_comp _ (baseChange ℤ (DRModel.toBase p) LL)
  exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨hproper, hmono⟩

theorem disjoint_range_zOf {I J : Ideal AF} (hIJ : I ⊔ J = ⊤) :
    Disjoint (Set.range (zOf p f I).base) (Set.range (zOf p f J).base) := by
  have hinj : Function.Injective (ιL p f).base := (ιL p f).isOpenEmbedding.injective
  have hr : ∀ K : Ideal AF, Set.range (zOf p f K).base =
      (ιL p f).base '' (PrimeSpectrum.zeroLocus (K : Set AF)) := by
    intro K
    have hc : ⇑(zOf p f K) = ⇑(ιL p f) ∘ ⇑(Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) := rfl
    rw [hc, Set.range_comp]
    congr 1
    have := range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := K))
    rw [Ideal.mk_ker] at this
    exact this
  rw [hr, hr, Set.disjoint_image_iff hinj]
  refine Set.disjoint_iff_inter_eq_empty.mpr ?_
  rw [← PrimeSpectrum.zeroLocus_sup, hIJ]
  exact PrimeSpectrum.zeroLocus_empty_of_one_mem (show (1 : AF) ∈ ((⊤ : Ideal AF) : Set AF) from trivial)

theorem mem_smoothLocus_of_not_mem (𝔛 : DRModelPackage p) (x : ↥(DRModel p))
    (hx : ((DRModel.toBase p).base x) ∈ PrimeSpectrum.basicOpen (p : ℤ)) : x ∈ 𝔛.smoothLocus := by

  let ιp : Spec (CommRingCat.of (Localization.Away (p : ℤ))) ⟶ Spec (CommRingCat.of ℤ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ))))
  haveI : IsOpenImmersion ιp := IsOpenImmersion.of_isLocalization (p : ℤ)
  let g := pullback.fst (DRModel.toBase p) ιp
  let U : (DRModel p).Opens := Scheme.Hom.opensRange g
  have hsm : Smooth (U.ι ≫ DRModel.toBase p) := by

    haveI : Smooth (pullback.snd (DRModel.toBase p) ιp) := 𝔛.smooth_away
    have hU : U.ι = (Scheme.Hom.isoOpensRange g).inv ≫ g :=
      (Iso.eq_inv_comp _).mpr (Scheme.Hom.isoOpensRange_hom_ι g)
    have hfac : U.ι ≫ DRModel.toBase p = (Scheme.Hom.isoOpensRange g).inv ≫ pullback.snd (DRModel.toBase p) ιp ≫ ιp := by
      rw [hU, Category.assoc]
      congr 1
      exact pullback.condition
    rw [hfac]
    infer_instance
  have hU : U ≤ 𝔛.smoothLocus := 𝔛.smoothLocus_maximal U hsm
  apply hU

  show x ∈ Set.range g.base
  rw [Scheme.Pullback.range_fst]
  show (DRModel.toBase p).base x ∈ Set.range ιp.base
  have : Set.range ιp.base = (PrimeSpectrum.basicOpen (p : ℤ) : Set (PrimeSpectrum ℤ)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away (p : ℤ)) (p : ℤ)
  rw [this]
  exact hx

theorem sup_span_aeval_eq_top (v : AA) {g₁ g₂ : Polynomial ℤ}
    (h : IsCoprime (g₁.map (algebraMap ℤ LL)) (g₂.map (algebraMap ℤ LL))) :
    Ideal.span {Polynomial.aeval (algebraMap AA AF v) g₁} ⊔ Ideal.span {Polynomial.aeval (algebraMap AA AF v) g₂} =
      (⊤ : Ideal AF) := by
  set x := algebraMap AA AF v
  have key : ∀ g : Polynomial ℤ, Polynomial.aeval x (g.map (algebraMap ℤ LL)) = Polynomial.aeval x g := by
    intro g
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.aeval_def]
    congr 1
    exact RingHom.ext_int _ _
  have hc := h.map (Polynomial.aeval x : Polynomial LL →ₐ[LL] AF).toRingHom
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, key] at hc
  exact Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_span_singleton_iff _ _).mpr hc)

omit [Fact p.Prime] in

theorem specMap_point_mem_basicOpen (k : Type) [Field k] (hk : (p : k) ≠ 0)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ)) (t : ↥(Spec (CommRingCat.of k))) :
    s.base t ∈ PrimeSpectrum.basicOpen (p : ℤ) := by
  rw [← Spec.map_preimage s]
  show (p : ℤ) ∉ (PrimeSpectrum.comap (Spec.preimage s).hom t).asIdeal
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, eq_intCast]
  intro h
  apply hk
  have : t.asIdeal = ⊥ := by
    haveI : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
    rw [Subsingleton.elim t (⊥ : PrimeSpectrum k)]
    rfl
  rw [this] at h
  simpa using h

theorem mem_smoothLocus_and_mem_connectedComponentIn_of_cast_ne_zero (𝔛 : DRModelPackage p)
    (k : Type) [Field k] (hk : (p : k) ≠ 0) (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ))
    (y x₀ : ↥(pullback (DRModel.toBase p) s)) :
    (pullback.fst (DRModel.toBase p) s).base y ∈ 𝔛.smoothLocus ∧
      y ∈ connectedComponentIn
        ((pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens) :
          Set ↥(pullback (DRModel.toBase p) s)) x₀ := by
  have hall : ∀ z : ↥(pullback (DRModel.toBase p) s), (pullback.fst (DRModel.toBase p) s).base z ∈ 𝔛.smoothLocus := by
    intro z
    apply mem_smoothLocus_of_not_mem p 𝔛
    have : (DRModel.toBase p).base ((pullback.fst (DRModel.toBase p) s).base z) =
        s.base ((pullback.snd (DRModel.toBase p) s).base z) := by
      change (pullback.fst (DRModel.toBase p) s ≫ DRModel.toBase p).base z = (pullback.snd (DRModel.toBase p) s ≫ s).base z
      rw [pullback.condition]
    rw [this]
    exact specMap_point_mem_basicOpen p k hk s _
  refine ⟨hall y, ?_⟩
  have htop : ((pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens) :
      Set ↥(pullback (DRModel.toBase p) s)) = Set.univ :=
    Set.eq_univ_of_forall fun z => hall z
  rw [htop, connectedComponentIn_univ]
  haveI : GeometricallyConnected (DRModel.toBase p) := ModularCurve.IgusaScheme.geometricallyConnected_toBase_int p
  haveI : ConnectedSpace ↥(pullback (DRModel.toBase p) s) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd (DRModel.toBase p) s)
  rw [PreconnectedSpace.connectedComponent_eq_univ]
  exact Set.mem_univ y

omit [Fact p.Prime] in

theorem mem_basicOpen_of_dvd {f : ℤ} (hpf : (p : ℤ) ∣ f) (x : PrimeSpectrum ℤ)
    (hx : x ∈ PrimeSpectrum.basicOpen f) : x ∈ PrimeSpectrum.basicOpen (p : ℤ) :=
  fun h => hx (by
    obtain ⟨c, rfl⟩ := hpf
    exact x.asIdeal.mul_mem_right c h)

theorem connectedComponentIn_smoothLocus_eq_univ_of_dvd (𝔛 : DRModelPackage p) (f : ℤ) (hpf : (p : ℤ) ∣ f)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))) :
    connectedComponentIn
      (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
          (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
      (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k)) = Set.univ := by
  set g := pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫
    pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f)) with hg
  have hall : ∀ y, g.base y ∈ 𝔛.smoothLocus := by
    intro y
    apply mem_smoothLocus_of_not_mem p 𝔛
    have hfac : g ≫ DRModel.toBase p =
        (pullback.snd (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ s) ≫ specMap ℤ (Localization.Away f) := by
      rw [hg, Category.assoc, pullback.condition, ← Category.assoc, pullback.condition]
    have : (DRModel.toBase p).base (g.base y) =
        (specMap ℤ (Localization.Away f)).base ((pullback.snd _ s ≫ s).base y) := by
      change (g ≫ DRModel.toBase p).base y = _
      rw [hfac]
      rfl
    rw [this]
    apply mem_basicOpen_of_dvd p hpf
    have hr : Set.range (specMap ℤ (Localization.Away f)).base = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum ℤ)) :=
      PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
    have hm := Set.mem_range_self (f := (specMap ℤ (Localization.Away f)).base) ((pullback.snd _ s ≫ s).base y)
    rw [hr] at hm
    exact hm
  have htop : (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
          (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s)) = Set.univ :=
    Set.eq_univ_of_forall fun y => hall y
  rw [htop, connectedComponentIn_univ]
  haveI : GeometricallyConnected (DRModel.toBase p) := ModularCurve.IgusaScheme.geometricallyConnected_toBase_int p
  haveI : ConnectedSpace ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s)
  exact PreconnectedSpace.connectedComponent_eq_univ _

end ModularCurve.HpoolGeo
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_of_ne.ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_of_ne.ModularCurve.HpoolGeo"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_of_ne.ModularCurve"

namespace HpoolAsm

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem not_dvd_resultant_and_isCoprime_map (p : ℕ) [Fact p.Prime] {D : ℕ} {g₁ g₂ : ℤ[X]}
    (hg₁ : g₁.Monic) (hg₂ : g₂.Monic) (hD₁ : g₁.natDegree = D) (hD₂ : g₂.natDegree = D)
    (hcop : IsCoprime (g₁.map (Int.castRingHom (ZMod p))) (g₂.map (Int.castRingHom (ZMod p)))) :
    ¬ (p : ℤ) ∣ Polynomial.resultant g₁ g₂ D D ∧
    ∀ (R : Type) [CommRing R] [Algebra ℤ R], IsUnit (algebraMap ℤ R (Polynomial.resultant g₁ g₂ D D)) →
      IsCoprime (g₁.map (algebraMap ℤ R)) (g₂.map (algebraMap ℤ R)) := by
  have hp : p.Prime := Fact.out
  constructor
  · intro hdvd
    have hu : IsUnit (Polynomial.resultant (g₁.map (Int.castRingHom (ZMod p))) (g₂.map (Int.castRingHom (ZMod p)))) :=
      (isUnit_resultant_iff_isCoprime (hg₁.map _)).mpr hcop
    rw [hg₁.natDegree_map (Int.castRingHom (ZMod p)), hg₂.natDegree_map (Int.castRingHom (ZMod p)),
      hD₁, hD₂, resultant_map_map] at hu
    exact hu.ne_zero ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd)
  · intro R _ _ hunit
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact ⟨0, 0, Subsingleton.elim _ _⟩
    have key := (isUnit_resultant_iff_isCoprime (g := g₂.map (algebraMap ℤ R)) (hg₁.map (algebraMap ℤ R)))
    rw [hg₁.natDegree_map (algebraMap ℤ R), hg₂.natDegree_map (algebraMap ℤ R), hD₁, hD₂,
      resultant_map_map] at key
    exact key.mp hunit

end HpoolAsm
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_of_ne.ModularCurve P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_of_ne.ModularCurve.HpoolGeo"

theorem HpoolAsm.tail (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (𝔭 : PrimeSpectrum ℤ) (A₀ B₀ n₀ : ℕ)
    (f : ℤ) (hf𝔭 : f ∉ 𝔭.asIdeal) (v : HpoolLevelRing.Afin p) (cdeg D M : ℕ) (g : Fin M → Polynomial ℤ)
    (hM : A₀ * (cdeg * D) ^ n₀ + B₀ < M) (hdeg1 : 1 ≤ cdeg * D)
    (hfin : ∀ i, Module.Finite (Localization.Away f) (HpoolLevelRing.levelRing p f v (g i)))
    (het : ∀ i, Algebra.Etale (Localization.Away f) (HpoolLevelRing.levelRing p f v (g i)))
    (hrank : ∀ i (𝔮 : PrimeSpectrum (Localization.Away f)),
      Module.rankAtStalk (R := Localization.Away f) (HpoolLevelRing.levelRing p f v (g i)) 𝔮 = cdeg * D)
    (z : ∀ i, Spec (CommRingCat.of (HpoolLevelRing.levelRing p f v (g i))) ⟶
      pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)))
    (hzci : ∀ i, IsClosedImmersion (z i))
    (hzbase : ∀ i, z i ≫ baseChange ℤ (DRModel.toBase p) (Localization.Away f) =
      specMap (Localization.Away f) (HpoolLevelRing.levelRing p f v (g i)))
    (hsmooth : ∀ i, Set.range (z i).base ⊆
      ((pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus :
        (pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))).Opens) :
        Set ↥(pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)))))
    (hdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hcomp : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
              (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k))) :
    ∃ (f : ℤ) (_ : f ∉ 𝔭.asIdeal) (b M : ℕ) (_ : A₀ * b ^ n₀ + B₀ < M)
    (R' : Type) (_ : CommRing R') (aZ : Algebra ℤ R')
    (aL : Algebra (Localization.Away f) R')

    (_ : @IsScalarTower ℤ (Localization.Away f) R' OreLocalization.instSMulOfIsScalarTower aL.toSMul aZ.toSMul)
    (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
    (_ : Module.FaithfullyFlat (Localization.Away f) R')
    (B : Fin M → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
    (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
    (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
    (_φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)))
    (_ : ∀ i, IsClosedImmersion (z i)),
    (∀ i, z i ≫ baseChange ℤ (DRModel.toBase p) (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
    (∀ i, Set.range (z i).base ⊆
      ((pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))).Opens) :
        Set ↥(pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))))) ∧
    (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
              (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k))) := by
  classical
  haveI := hfin; haveI := het
  let deg : Fin M → ℕ := fun _ => cdeg * D
  have hdeg : ∀ i, Module.rankAtStalk (R := Localization.Away f) (HpoolLevelRing.levelRing p f v (g i)) = deg i :=
    fun i => funext (hrank i)
  obtain ⟨R', _, _, finR, etR, ffR, hφ⟩ :=
    Algebra.Etale.exists_faithfullyFlat_forall_nonempty_algEquiv_pi (Localization.Away f)
      (fun i => HpoolLevelRing.levelRing p f v (g i)) deg hdeg
  refine ⟨f, hf𝔭, cdeg * D, M, hM, R', inferInstance, inferInstance, ‹Algebra (Localization.Away f) R'›, ?_,
    finR, etR, ffR, fun i => HpoolLevelRing.levelRing p f v (g i), inferInstance, inferInstance, hfin, het, deg,
    fun _ => hdeg1, fun _ => le_refl _, fun i => (hφ i).some, z, hzci, hzbase, hsmooth, hdisj, hcomp⟩
  exact IsScalarTower.of_algebraMap_eq fun x =>
    (RingHom.congr_fun (Subsingleton.elim ((algebraMap (Localization.Away f) R').comp
      (algebraMap ℤ (Localization.Away f))) (algebraMap ℤ R')) x).symm

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial ModularCurve.HpoolGeo in
theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (𝔭 : PrimeSpectrum ℤ) (A₀ B₀ n₀ : ℕ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (h𝔭ℓ : 𝔭.asIdeal ≤ Ideal.span {(ℓ : ℤ)}) :
    ∃ (f : ℤ) (_ : f ∉ 𝔭.asIdeal) (b M : ℕ) (_ : A₀ * b ^ n₀ + B₀ < M)
    (R' : Type) (_ : CommRing R') (aZ : Algebra ℤ R')
    (aL : Algebra (Localization.Away f) R')

    (_ : @IsScalarTower ℤ (Localization.Away f) R' OreLocalization.instSMulOfIsScalarTower aL.toSMul aZ.toSMul)
    (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
    (_ : Module.FaithfullyFlat (Localization.Away f) R')
    (B : Fin M → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
    (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
    (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
    (_φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)))
    (_ : ∀ i, IsClosedImmersion (z i)),
    (∀ i, z i ≫ baseChange ℤ (DRModel.toBase p) (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
    (∀ i, Set.range (z i).base ⊆
      ((pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))).Opens) :
        Set ↥(pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))))) ∧
    (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
              (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k))) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hℓP : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp Fact.out

  obtain ⟨avoid, havoid, c₀, hc₀, hLEVEL⟩ :=
    ModularCurve.HpoolLevelRing.exists_finite_etale_levelRing_jChartFin p ℓ hℓp

  obtain ⟨D, M, g, h2D, hND, hM, hgmon, hgirr, -, hgcop, hgav, -⟩ :=
    Polynomial.exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime ℓ n₀ A₀ B₀ (p + 1) (c₀.natDegree + 1)
      avoid havoid
  have hndvd : ∀ i, ¬ g i ∣ c₀ := fun i hdvd => by
    have := Polynomial.natDegree_le_of_dvd hdvd hc₀
    rw [(hgmon i).2] at this
    omega
  have hLi : ∀ i, ∃ c : ℤ, ¬ (ℓ : ℤ) ∣ c ∧ c ≠ 0 ∧ ∀ f : ℤ, f ≠ 0 → c ∣ f →
      Module.Finite (Localization.Away f) (HpoolLevelRing.levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (g i)) ∧
      Algebra.Etale (Localization.Away f) (HpoolLevelRing.levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (g i)) ∧
      Module.Free (Localization.Away f) (HpoolLevelRing.levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (g i)) ∧
      Module.finrank (Localization.Away f) (HpoolLevelRing.levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (g i)) = (p + 1) * (g i).natDegree ∧
      ∀ 𝔮 : PrimeSpectrum (Localization.Away f),
        Module.rankAtStalk (R := Localization.Away f) (HpoolLevelRing.levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (g i)) 𝔮 = (p + 1) * (g i).natDegree :=
    fun i => hLEVEL (g i) (hgmon i).1 (by rw [(hgmon i).2]; omega) (hgirr i) (hgav i) (hndvd i)
  choose c hcℓ hc0 hcprop using hLi

  have hRij : ∀ ij : Fin M × Fin M, ∃ r : ℤ, ¬ (ℓ : ℤ) ∣ r ∧ r ≠ 0 ∧ (ij.1 ≠ ij.2 →
      ∀ (R : Type) [CommRing R] [Algebra ℤ R],
        IsUnit (algebraMap ℤ R r) → IsCoprime ((g ij.1).map (algebraMap ℤ R)) ((g ij.2).map (algebraMap ℤ R))) := by
    rintro ⟨i, j⟩
    by_cases hij : i = j
    · exact ⟨1, fun h => hℓP.not_unit (isUnit_of_dvd_one h), one_ne_zero, fun h => absurd hij h⟩
    · obtain ⟨hr1, hr3⟩ := HpoolAsm.not_dvd_resultant_and_isCoprime_map ℓ (hgmon i).1 (hgmon j).1
        (hgmon i).2 (hgmon j).2 (hgcop i j hij)
      exact ⟨_, hr1, fun h0 => hr1 (h0 ▸ dvd_zero _), fun _ => hr3⟩
  choose r hrℓ hr0 hrcop using hRij

  obtain ⟨f, hfdef⟩ : ∃ f : ℤ, f = (p : ℤ) * ((∏ i, c i) * ∏ ij, r ij) := ⟨_, rfl⟩
  have hpf : (p : ℤ) ∣ f := hfdef ▸ Dvd.intro _ rfl
  have hcf : ∀ i, c i ∣ f := fun i =>
    hfdef ▸ Dvd.dvd.mul_left (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem c (Finset.mem_univ i)) _) _
  have hrf : ∀ ij, r ij ∣ f := fun ij =>
    hfdef ▸ Dvd.dvd.mul_left (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem r (Finset.mem_univ ij)) _) _
  have hf0 : f ≠ 0 := by
    rw [hfdef]
    refine mul_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero) (mul_ne_zero ?_ ?_)
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => hc0 i
    · exact Finset.prod_ne_zero_iff.mpr fun ij _ => hr0 ij
  have hℓf : ¬ (ℓ : ℤ) ∣ f := by
    intro h
    rw [hfdef] at h
    rcases hℓP.dvd_or_dvd h with h1 | h23
    · exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp (Int.natCast_dvd_natCast.mp h1))
    · rcases hℓP.dvd_or_dvd h23 with h2 | h3
      · obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hℓP _).mp h2
        exact hcℓ i hi
      · obtain ⟨ij, -, hij⟩ := (Prime.dvd_finsetProd_iff hℓP _).mp h3
        exact hrℓ ij hij
  have hf𝔭 : f ∉ 𝔭.asIdeal := fun h => hℓf (Ideal.mem_span_singleton.mp (h𝔭ℓ h))

  have hprop := fun i => hcprop i f hf0 (hcf i)
  have hfin : ∀ i, Module.Finite (Localization.Away f) (HpoolLevelRing.levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (g i)) := fun i => (hprop i).1
  have het : ∀ i, Algebra.Etale (Localization.Away f) (HpoolLevelRing.levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (g i)) := fun i => (hprop i).2.1
  have hrank : ∀ i (𝔮 : PrimeSpectrum (Localization.Away f)),
      Module.rankAtStalk (R := Localization.Away f) (HpoolLevelRing.levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (g i)) 𝔮 = (p + 1) * D := fun i 𝔮 => by
    rw [(hprop i).2.2.2.2 𝔮, (hgmon i).2]

  haveI : IsSeparated (DRModel.toBase p) := by haveI := 𝔛.isProper; infer_instance
  haveI := hfin
  let z : ∀ i, Spec (CommRingCat.of (HpoolLevelRing.levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (g i))) ⟶ pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)) :=
    fun i => zOf p f (Ideal.span {Polynomial.aeval (algebraMap _ (HpoolLevelRing.AfinAway p f) (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (g i)})
  have hzci : ∀ i, IsClosedImmersion (z i) := fun i => isClosedImmersion_zOf p f _
  have hzbase : ∀ i, z i ≫ baseChange ℤ (DRModel.toBase p) (Localization.Away f) = specMap (Localization.Away f) (HpoolLevelRing.levelRing p f (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (g i)) :=
    fun i => zOf_baseChange p f _

  have hunitf : IsUnit (algebraMap ℤ (HpoolLevelRing.AfinAway p f) f) := by
    have h1 : IsUnit (algebraMap ℤ (Localization.Away f) f) := IsLocalization.Away.algebraMap_isUnit f
    have h2 := h1.map (algebraMap (Localization.Away f) (HpoolLevelRing.AfinAway p f))
    have h3 : (algebraMap (Localization.Away f) (HpoolLevelRing.AfinAway p f)) (algebraMap ℤ (Localization.Away f) f) = algebraMap ℤ (HpoolLevelRing.AfinAway p f) f :=
      RingHom.congr_fun (RingHom.ext_int ((algebraMap (Localization.Away f) (HpoolLevelRing.AfinAway p f)).comp (algebraMap ℤ (Localization.Away f))) (algebraMap ℤ (HpoolLevelRing.AfinAway p f))) f
    rwa [h3] at h2
  have hdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base) := by
    intro i j hij
    apply disjoint_range_zOf p f
    have hcop : IsCoprime ((g i).map (algebraMap ℤ (HpoolLevelRing.AfinAway p f))) ((g j).map (algebraMap ℤ (HpoolLevelRing.AfinAway p f))) :=
      hrcop (i, j) hij (HpoolLevelRing.AfinAway p f) (isUnit_of_dvd_unit (map_dvd _ (hrf (i, j))) hunitf)
    have hcop' := hcop.map (Polynomial.evalRingHom (algebraMap (HpoolLevelRing.Afin p) (HpoolLevelRing.AfinAway p f) (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))
    rw [Polynomial.coe_evalRingHom, Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap] at hcop'
    rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
    exact hcop'

  have hsmooth : ∀ i, Set.range (z i).base ⊆
      ((pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))).Opens) : Set ↥(pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)))) := by
    intro i
    rintro _ ⟨y, rfl⟩
    show (pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))).base ((z i).base y) ∈ 𝔛.smoothLocus
    apply mem_smoothLocus_of_not_mem p 𝔛
    have hcond : (DRModel.toBase p).base ((pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))).base ((z i).base y)) =
        (specMap ℤ (Localization.Away f)).base ((pullback.snd (DRModel.toBase p) (specMap ℤ (Localization.Away f))).base ((z i).base y)) := by
      have := pullback.condition (f := DRModel.toBase p) (g := specMap ℤ (Localization.Away f))
      exact congrArg (fun φ => φ.base ((z i).base y)) this
    rw [hcond]
    have hq : (specMap ℤ (Localization.Away f)).base ((pullback.snd (DRModel.toBase p) (specMap ℤ (Localization.Away f))).base ((z i).base y)) ∈
        (PrimeSpectrum.basicOpen (f : ℤ) : Set (PrimeSpectrum ℤ)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact ⟨_, rfl⟩
    intro hpmem
    exact hq (Ideal.mem_of_dvd _ hpf hpmem)

  have hcomp : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
              (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k)) := by
    intro k _ _ s i
    rw [connectedComponentIn_smoothLocus_eq_univ_of_dvd p 𝔛 f hpf k s]
    exact Set.subset_univ _
  have hdeg1 : 1 ≤ (p + 1) * D := by nlinarith
  exact HpoolAsm.tail p 𝔛 𝔭 A₀ B₀ n₀ f hf𝔭 (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (p + 1) D M g hM hdeg1 hfin het hrank z hzci hzbase hsmooth
    hdisj hcomp

end S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_of_ne
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_exists_locallySplitPools_of_le_span_of_ne (solution)
