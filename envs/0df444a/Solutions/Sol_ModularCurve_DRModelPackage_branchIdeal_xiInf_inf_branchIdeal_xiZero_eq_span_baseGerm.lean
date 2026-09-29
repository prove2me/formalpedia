-- Prove2me | solution 1 for ModularCurve.DRModelPackage.branchIdeal_xiInf_inf_branchIdeal_xiZero_eq_span_baseGerm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b2c5e3c3-0f68-5b25-91e9-0d98897a6724

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Theorems.Thm_ModularCurve_DRModel_isReduced_pullback_toBase_of_charP
import Theorems.Thm_ModularCurve_DRModelPackage_eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes
import Theorems.Thm_ModularCurve_DRModel_isIntegral_pullback_toBase
import Theorems.Thm_ModularCurve_DRModelPackage_locallyOfFinitePresentation_toBase
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_branchIdeal_xiInf_inf_branchIdeal_xiZero_eq_span_baseGerm
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve TopologicalSpace IsLocalRing

noncomputable section

namespace FUNION

variable (p : ℕ) [hp : Fact p.Prime]

section MapLemmas
universe v u
variable {C : Type u} [Category.{v} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
  (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
  (e₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (e₂ : f₂ ≫ i₃ = i₂ ≫ g₂)

@[reassoc]
theorem map_fst' : pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.fst g₁ g₂ = pullback.fst f₁ f₂ ≫ i₁ :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem map_snd' : pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.snd g₁ g₂ = pullback.snd f₁ f₂ ≫ i₂ :=
  pullback.lift_snd _ _ _

end MapLemmas

section SpecialFibre

variable (O : Type) [CommRing O] [IsLocalRing O] (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})

theorem isReduced_pullback_snd_of_charP (κ : Type) [Field κ] [CharP κ p] (toκ : O →+* κ) :
    IsReduced (pullback
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
      (Spec.map (CommRingCat.ofHom toκ))) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h : Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ O)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext_int _ _
  haveI : IsReduced (pullback (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := by
    rw [h]; exact ModularCurve.DRModel.isReduced_pullback_toBase_of_charP p κ
  exact isReduced_of_isOpenImmersion (pullbackLeftPullbackSndIso (DRModel.toBase p)
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) (Spec.map (CommRingCat.ofHom toκ))).hom

include hϖ in

theorem ker_Spec_map_mk :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})))).ker =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {((p : ℕ) : Γ(Spec (CommRingCat.of O), ⊤))}) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ofIdealTop_ideal]
  have htop : (homOfLE le_top : ((⊤ : (Spec (CommRingCat.of O)).Opens) ⟶ ⊤)) = 𝟙 _ := Subsingleton.elim _ _
  simp only [htop, op_id, CategoryTheory.Functor.map_id]
  rw [show CommRingCat.Hom.hom (𝟙 ((Spec (CommRingCat.of O)).presheaf.obj (Opposite.op ⊤))) =
      RingHom.id _ from rfl, Ideal.map_id]

  have hnat := AlgebraicGeometry.Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})))

  have happ : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})))).app ⊤ =
      (Scheme.ΓSpecIso (CommRingCat.of O)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (O ⧸ Ideal.span {((p : ℕ) : O)}))).inv := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [happ]
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (O ⧸ Ideal.span {((p : ℕ) : O)}))).inv.hom := by
    intro a b h
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (O ⧸ Ideal.span {((p : ℕ) : O)}))).hom.hom h
    simpa only [CategoryTheory.Iso.inv_hom_id_apply] using this
  ext a
  rw [RingHom.mem_ker]
  change (Scheme.ΓSpecIso (CommRingCat.of (O ⧸ Ideal.span {((p : ℕ) : O)}))).inv.hom
      (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}) ((Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom a)) = 0 ↔ _
  rw [map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]

  let e : Γ(Spec (CommRingCat.of O), ⊤) ≃+* O := (Scheme.ΓSpecIso (CommRingCat.of O)).commRingCatIsoToRingEquiv
  change e a ∈ Ideal.span {((p : ℕ) : O)} ↔ a ∈ Ideal.span {((p : ℕ) : Γ(Spec (CommRingCat.of O), ⊤))}
  rw [Ideal.mem_span_singleton', Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, e.injective ?_⟩
    rw [map_mul, map_natCast, RingEquiv.apply_symm_apply, hc]
  · rintro ⟨c, rfl⟩
    exact ⟨e c, by rw [map_mul, map_natCast]⟩

end SpecialFibre

section Radical

variable (O : Type) [CommRing O] [IsLocalRing O] (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})

include hϖ in

theorem comap_radical_eq :
    ((Scheme.IdealSheafData.ofIdealTop (Ideal.span {((p : ℕ) : Γ(Spec (CommRingCat.of O), ⊤))})).comap
        (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))).radical =
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {((p : ℕ) : Γ(Spec (CommRingCat.of O), ⊤))})).comap
        (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := by
  set πO := pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) with hπO
  set I : (Spec (CommRingCat.of O)).IdealSheafData :=
    Scheme.IdealSheafData.ofIdealTop (Ideal.span {((p : ℕ) : Γ(Spec (CommRingCat.of O), ⊤))}) with hI
  let fZ := pullback.fst πO I.subschemeι
  have hJ : I.comap πO = fZ.ker := rfl

  haveI : IsReduced (pullback πO I.subschemeι) := by
    haveI hmax : (Ideal.span {((p : ℕ) : O)}).IsMaximal := by rw [← hϖ]; exact maximalIdeal.isMaximal O
    letI : Field (O ⧸ Ideal.span {((p : ℕ) : O)}) := Ideal.Quotient.field _
    haveI : CharP (O ⧸ Ideal.span {((p : ℕ) : O)}) p := by
      refine (CharP.charP_iff_prime_eq_zero hp.out).mpr ?_
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    let i₂ : Spec (CommRingCat.of (O ⧸ Ideal.span {((p : ℕ) : O)})) ⟶ Spec (CommRingCat.of O) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})))
    haveI : IsClosedImmersion i₂ := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    haveI hP₂ : IsReduced (pullback πO i₂) :=
      isReduced_pullback_snd_of_charP p O _ (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}))
    have hker : I.subschemeι.ker = i₂.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, hI, ← ker_Spec_map_mk p O hϖ]
    let e := IsClosedImmersion.lift I.subschemeι i₂ hker.le
    haveI : IsIso e := IsClosedImmersion.isIso_lift I.subschemeι i₂ hker
    have he : e ≫ I.subschemeι = i₂ := IsClosedImmersion.lift_fac _ _ _
    let m : pullback πO i₂ ⟶ pullback πO I.subschemeι :=
      pullback.map πO i₂ πO I.subschemeι (𝟙 _) e (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, he])
    haveI : IsIso m := by
      refine ⟨⟨pullback.map πO I.subschemeι πO i₂ (𝟙 _) (inv e) (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, ← he, IsIso.inv_hom_id_assoc]), ?_, ?_⟩⟩
      · apply pullback.hom_ext <;> simp [m, map_fst', map_snd', map_snd'_assoc]
      · apply pullback.hom_ext <;> simp [m, map_fst', map_snd', map_snd'_assoc]
    exact isReduced_of_isOpenImmersion (inv m)

  apply le_antisymm _ (Scheme.IdealSheafData.le_radical _)
  rw [hJ, ← Scheme.IdealSheafData.map_bot, ← (Scheme.IdealSheafData.map_gc fZ).le_iff_le, le_bot_iff,
    ← Scheme.IdealSheafData.support_eq_top_iff, Scheme.IdealSheafData.support_comap,
    Scheme.IdealSheafData.support_radical]
  ext z
  simp only [Closeds.coe_top, Set.mem_univ, iff_true]
  rw [Scheme.IdealSheafData.map_bot]
  show fZ.base z ∈ (fZ.ker.support : Set _)
  rw [Scheme.Hom.support_ker]
  exact subset_closure ⟨z, rfl⟩

theorem comap_eq_ofIdealTop :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span {((p : ℕ) : Γ(Spec (CommRingCat.of O), ⊤))})).comap
        (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {((p : ℕ) : Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), ⊤))}) := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton, map_natCast]

include hϖ in

theorem radical_span_natCast_sections (U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).affineOpens) :
    (Ideal.span {((p : ℕ) : Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U))}).radical =
      Ideal.span {((p : ℕ) : Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U))} := by
  have h := congrArg (fun J : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).IdealSheafData => J.ideal U)
    (comap_radical_eq p O hϖ)
  simp only [Scheme.IdealSheafData.radical_ideal] at h
  rw [comap_eq_ofIdealTop, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton, map_natCast] at h
  exact h

end Radical

section Stalk

variable (O : Type) [CommRing O] [IsLocalRing O] (hϖ : maximalIdeal O = Ideal.span {((p : ℕ) : O)})

include hϖ in

theorem radical_span_natCast_stalk (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) :
    (Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)}).radical =
      Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)} := by

  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  letI := (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.algebra_section_stalk ⟨x, hxU⟩
  haveI hloc := hU.isLocalization_stalk ⟨x, hxU⟩
  have hrad := radical_span_natCast_sections p O hϖ ⟨U, hU⟩
  have hmap : (Ideal.span {((p : ℕ) : Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U))}).map
      (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)) =
      Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have h := congrArg (Ideal.map (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x))) hrad
  simp only at h
  rw [IsLocalization.map_radical (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x), hmap] at h
  exact h

end Stalk

theorem main (hp5 : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)))
    (hinf : 𝔛.ξinf O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) (hzero : 𝔛.ξzero O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) :
    Scheme.branchIdeal hinf ⊓ Scheme.branchIdeal hzero =
      Ideal.span {DRModelPackage.baseGerm O (𝔛.crossingPt O κ toκ n) ((p : ℕ) : O)} := by
  set X := pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) with hX
  set x := 𝔛.crossingPt O κ toκ n with hx

  haveI : IsIntegral X := ModularCurve.DRModel.isIntegral_pullback_toBase p O hϖ
  haveI : LocallyOfFinitePresentation (DRModel.toBase p) := ModularCurve.DRModelPackage.locallyOfFinitePresentation_toBase p 𝔛
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))

  have hgen : DRModelPackage.baseGerm O x ((p : ℕ) : O) = ((p : ℕ) : X.presheaf.stalk x) := by
    simp only [DRModelPackage.baseGerm, map_natCast]
  rw [hgen]
  obtain ⟨-, hpP, -, hpQ, hmin, -⟩ :=
    ModularCurve.DRModelPackage.eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes p hp5 𝔛 O hϖ toκ x hinf hzero
  apply le_antisymm
  ·
    intro a ha
    rw [← radical_span_natCast_stalk p O hϖ x, ← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro 𝔮 h𝔮
    rcases hmin 𝔮 h𝔮 with rfl | rfl
    · exact ha.1
    · exact ha.2
  ·
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ⟨hpP, hpQ⟩

end FUNION

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.DRModelPackage in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)))
    (hinf : 𝔛.ξinf O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) (hzero : 𝔛.ξzero O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) :
    Scheme.branchIdeal hinf ⊓ Scheme.branchIdeal hzero =
      Ideal.span {baseGerm O (𝔛.crossingPt O κ toκ n) ((p : ℕ) : O)} :=
  FUNION.main p hp 𝔛 O hϖ κ toκ n hinf hzero

end S_ModularCurve_DRModelPackage_branchIdeal_xiInf_inf_branchIdeal_xiZero_eq_span_baseGerm
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_branchIdeal_xiInf_inf_branchIdeal_xiZero_eq_span_baseGerm (solution)
