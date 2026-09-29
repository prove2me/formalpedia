-- Prove2me | solution 1 for ModularCurve.coeffEmb_mem_chartAlgFin_of_forall_coeff_of_isIntegral_adjoin_jq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/5d299407-e9ee-5251-92bc-855be259206e

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_Ideal_isPrime_span_algebraMap_of_isDomain_tensor
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffEmb_mem_chartAlgFin_of_forall_coeff_of_isIntegral_adjoin_jq
p2m_attr_erase "instance" "instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply"
p2m_attr_erase "simp" "NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open scoped TensorProduct MatrixGroups Polynomial
p2m_open "ModularCurve P2MW.S_ModularCurve_coeffEmb_mem_chartAlgFin_of_forall_coeff_of_isIntegral_adjoin_jq.ModularCurve AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "jq modularFunctionFieldFull coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb IgusaScheme.igusaAlgebra IgusaScheme.jFull IgusaScheme XHDRLevel.jAt qExpFunctionFieldC intFormRatiosC_subset jqModC IgusaScheme.isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull XHDRLevel.exists_valuationSubring_gauss_qExpFunctionFieldC jqModC_mem_intFormRatiosC"
namespace IntClAux
p2m_open "ModularCurve"

theorem igusaAlgebra_eq (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    (IgusaScheme.igusaAlgebra N ℓ :
      Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N)) = Algebra.ofSubsemiring _ :=
  Algebra.algebra_ext _ _ fun _ => rfl

def DomFin (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type) [Field k] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) k]
    (inst : Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N)) : Prop :=
  IsDomain (k ⊗[↥(GaloisRep.ratLocalizedAt ℓ)]
    ↥(@TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) _ ↥(modularFunctionFieldFull N) _ inst
        {IgusaScheme.jFull N}))

def FTFin (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (inst : Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N)) : Prop :=
  @Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ)
    ↥(@TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) _ ↥(modularFunctionFieldFull N) _ inst
        {IgusaScheme.jFull N}) _ _ (Subalgebra.algebra _)

theorem isDomain_tensor_chartAlg_jFull (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (k : Type) [Field k] [IsAlgClosed k] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) k] :
    IsDomain (k ⊗[↥(GaloisRep.ratLocalizedAt ℓ)]
      ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N)
        {IgusaScheme.jFull N})) := by
  have h1 : DomFin N ℓ k (IgusaScheme.igusaAlgebra N ℓ) :=
    (ModularCurve.IgusaScheme.isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed N ℓ hℓN k).1
  rw [igusaAlgebra_eq] at h1
  exact h1

theorem finiteType_chartAlg_jFull (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ)
      ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N)
        {IgusaScheme.jFull N}) := by
  have h1 : FTFin N ℓ (IgusaScheme.igusaAlgebra N ℓ) :=
    (ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf N ℓ).1
  rw [igusaAlgebra_eq] at h1
  exact h1

theorem maximalIdeal_ratLocalizedAt (q : ℕ) [Fact q.Prime] :
    haveI : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt q) :=
      GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out
    IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt q) =
      Ideal.span {((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q))} :=
  haveI : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt q) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out
  (GaloisRep.irreducible_natCast_ratLocalizedAt q Fact.out).maximalIdeal_eq

theorem isPrime_span_natCast_chartAlg (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime] (hqN : ¬ q ∣ N) :
    (Ideal.span {algebraMap ↥(GaloisRep.ratLocalizedAt q)
      ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull N)
        {IgusaScheme.jFull N}) ((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q))}).IsPrime := by
  haveI : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt q) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out
  let Ω : Type := AlgebraicClosure (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt q))
  haveI := isDomain_tensor_chartAlg_jFull N q hqN Ω
  have hmax := maximalIdeal_ratLocalizedAt q
  have hker : RingHom.ker (algebraMap ↥(GaloisRep.ratLocalizedAt q) Ω) =
      Ideal.span {((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q))} := by
    rw [← hmax]
    have : algebraMap ↥(GaloisRep.ratLocalizedAt q) Ω =
        (algebraMap (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt q)) Ω).comp
          (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt q)) := rfl
    have hinj : RingHom.ker (algebraMap (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt q)) Ω) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp
        (algebraMap (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt q)) Ω).injective
    rw [this, ← RingHom.comap_ker, hinj, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
  have hm : (Ideal.span {((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q))} : Ideal _).IsMaximal := by
    rw [← hmax]; exact IsLocalRing.maximalIdeal.isMaximal _
  exact Ideal.isPrime_span_algebraMap_of_isDomain_tensor (κ := Ω) _ hker hm

theorem exists_gauss (M' : ℕ) [NeZero M'] (q : ℕ) [Fact q.Prime] :
    ∃ W : ValuationSubring ↥(modularFunctionFieldFull M'),
      (∀ f : ↥(modularFunctionFieldFull M'), f ∈ W ↔
        ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt q), a'.map (GaloisRep.ratLocalizedAtResidue q) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt q).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt q).subtype)) ∧
      (∀ a : ↥(GaloisRep.ratLocalizedAt q),
        algebraMap ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull M') a ∈ W) ∧
      (algebraMap ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull M')
          ((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q)) ∈ W.nonunits) ∧
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt q), Q.map (GaloisRep.ratLocalizedAtResidue q) ≠ 0 →
        Polynomial.aeval (IgusaScheme.jFull M') Q ∈ W ∧ (Polynomial.aeval (IgusaScheme.jFull M') Q)⁻¹ ∈ W) := by
  have hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)) :=
    intFormRatiosC_subset ℚ ⊤ (ModularCurve.jqModC_mem_intFormRatiosC ℚ ⊤)

  suffices key : ∀ (F : IntermediateField ℚ (LaurentSeries ℚ)) (jF : ↥F),
      F = qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M') → (jF : LaurentSeries ℚ) = jqModC ℚ →
      ∃ W : ValuationSubring ↥F,
      (∀ f : ↥F, f ∈ W ↔
        ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt q), a'.map (GaloisRep.ratLocalizedAtResidue q) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt q).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt q).subtype)) ∧
      (∀ a : ↥(GaloisRep.ratLocalizedAt q), algebraMap ↥(GaloisRep.ratLocalizedAt q) ↥F a ∈ W) ∧
      (algebraMap ↥(GaloisRep.ratLocalizedAt q) ↥F ((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q)) ∈ W.nonunits) ∧
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt q), Q.map (GaloisRep.ratLocalizedAtResidue q) ≠ 0 →
        Polynomial.aeval jF Q ∈ W ∧ (Polynomial.aeval jF Q)⁻¹ ∈ W) from
    key _ _ (qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull M').symm rfl
  rintro F jF rfl hjF
  have hjAt : jF = XHDRLevel.jAt (CongruenceSubgroup.Gamma0 M') hj := Subtype.ext hjF
  subst hjAt
  obtain ⟨W, hpin, hR, hq, hQ, -⟩ :=
    ModularCurve.XHDRLevel.exists_valuationSubring_gauss_qExpFunctionFieldC q (CongruenceSubgroup.Gamma0 M') hj
  exact ⟨W, hpin, hR, hq _ (Ideal.mem_span_singleton_self _), hQ⟩

theorem charP_residueField_of_mem (q : ℕ) [Fact q.Prime]
    (A : Type) [CommRing A] [IsLocalRing A] (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) :
    CharP (IsLocalRing.ResidueField A) q := by
  have h0 : ((q : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    have := (IsLocalRing.residue_eq_zero_iff (q : A)).mpr hAq
    simpa using this
  have hdvd : ringChar (IsLocalRing.ResidueField A) ∣ q := (ringChar.spec _ q).mp h0
  rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | h2
  · exact absurd h1 (CharP.ringChar_ne_one)
  · exact h2 ▸ ringChar.charP _

theorem isUnit_natCast_of_not_dvd (q : ℕ) [Fact q.Prime]
    (A : Type) [CommRing A] [IsLocalRing A] (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (n : ℕ) (hn : ¬ q ∣ n) : IsUnit (n : A) := by
  haveI := charP_residueField_of_mem q A hAq
  by_contra h
  have hmem : (n : A) ∈ IsLocalRing.maximalIdeal A := h
  have h0 := (IsLocalRing.residue_eq_zero_iff (n : A)).mpr hmem
  rw [map_natCast] at h0
  exact hn ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) q n).mp h0)

theorem isUnit_intCast_of_not_dvd (q : ℕ) [Fact q.Prime]
    (A : Type) [CommRing A] [IsLocalRing A] (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (z : ℤ) (hz : ¬ (q : ℤ) ∣ z) : IsUnit (z : A) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · have hn : ¬ q ∣ n := fun h => hz (Int.natCast_dvd_natCast.mpr h)
    simpa using isUnit_natCast_of_not_dvd q A hAq n hn
  · have hn : ¬ q ∣ n := fun h => hz ((Int.natCast_dvd_natCast.mpr h).neg_right)
    simpa using (isUnit_natCast_of_not_dvd q A hAq n hn).neg

theorem mem_ratLocalizedAt_of_eq (q : ℕ) [Fact q.Prime]
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra A L] (hinj : Function.Injective (algebraMap A L))
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (r : ℚ) (a : A) (h : algebraMap A L a = algebraMap ℚ L r) :
    r ∈ GaloisRep.ratLocalizedAt q := by
  change r.den.Coprime q
  rw [Nat.coprime_comm, (Fact.out : q.Prime).coprime_iff_not_dvd]
  intro hdvd

  have hL : (r : L) * (r.den : L) = (r.num : L) := by exact_mod_cast Rat.mul_den_eq_num r
  have h' : algebraMap A L a = (r : L) := by rw [h, eq_ratCast]
  have hA : a * (r.den : A) = (r.num : A) := by
    apply hinj
    rw [map_mul, h', map_natCast, map_intCast, hL]

  have hnum : ¬ (q : ℤ) ∣ r.num := by
    intro hq
    have hcop : Nat.Coprime r.num.natAbs r.den := r.reduced
    have h1 : q ∣ r.num.natAbs := Int.natCast_dvd.mp hq
    have : q ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd h1 hdvd
    rw [hcop] at this
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp this)
  have hu : IsUnit (a * (r.den : A)) := hA ▸ isUnit_intCast_of_not_dvd q A hAq r.num hnum
  have hden : IsUnit ((r.den : ℕ) : A) := isUnit_of_mul_isUnit_right hu
  have hqU : IsUnit ((q : ℕ) : A) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hdvd) hden
  exact (IsLocalRing.mem_maximalIdeal _).mp hAq hqU

theorem exists_gaussPresentation (q : ℕ) [Fact q.Prime]
    (g : LaurentSeries ℚ) (hg : ∀ n : ℤ, g.coeff n ∈ GaloisRep.ratLocalizedAt q) :
    ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt q), a'.map (GaloisRep.ratLocalizedAtResidue q) ≠ 0 ∧
      g * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt q).subtype) =
        HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt q).subtype) := by
  classical

  let b : PowerSeries ↥(GaloisRep.ratLocalizedAt q) := PowerSeries.mk fun n => ⟨g.coeff (g.order + n), hg _⟩
  have hb : b.map (GaloisRep.ratLocalizedAt q).subtype = g.powerSeriesPart := by
    ext n
    simp [b, PowerSeries.coeff_mk, LaurentSeries.powerSeriesPart_coeff]

  set k : ℕ := (-g.order).toNat with hk
  set m : ℕ := (g.order + k).toNat with hm
  have hmk : ((m : ℕ) : ℤ) = g.order + k := by
    rw [hm, Int.toNat_of_nonneg]
    have : -g.order ≤ (k : ℤ) := by rw [hk]; exact Int.self_le_toNat _
    omega
  refine ⟨PowerSeries.X ^ m * b, PowerSeries.X ^ k, ?_, ?_⟩
  · rw [map_pow, PowerSeries.map_X]
    exact pow_ne_zero k PowerSeries.X_ne_zero
  · simp only [map_mul, map_pow, PowerSeries.map_X, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow,
      nsmul_eq_mul, mul_one, one_pow]
    rw [hb, LaurentSeries.ofPowerSeries_powerSeriesPart, ← mul_assoc, HahnSeries.single_mul_single, mul_one,
      mul_comm g, show ((m : ℤ) + -g.order) = (k : ℤ) by omega]

abbrev Rq (q : ℕ) : Type := ↥(GaloisRep.ratLocalizedAt q)

abbrev FF (M' : ℕ) [NeZero M'] : Type := ↥(modularFunctionFieldFull M')

noncomputable abbrev Bsub (M' : ℕ) [NeZero M'] (q : ℕ) : Subalgebra (Rq q) (FF M') :=
  TwoChartIntegralModel.chartAlg (Rq q) (FF M') {IgusaScheme.jFull M'}

noncomputable abbrev T0 (M' : ℕ) [NeZero M'] (q : ℕ) : Subalgebra (Rq q) (FF M') :=
  Algebra.adjoin (Rq q) {IgusaScheme.jFull M'}

theorem coe_mem_valuationSubring_of_mem_chartAlg (M' : ℕ) [NeZero M'] (q : ℕ) [Fact q.Prime]
    (W : ValuationSubring (FF M'))
    (hR : ∀ a : Rq q, algebraMap (Rq q) (FF M') a ∈ W)
    (hjW : IgusaScheme.jFull M' ∈ W)
    (x : FF M') (hx : x ∈ Bsub M' q) : x ∈ W := by

  let WA : Subalgebra (Rq q) (FF M') := { W.toSubring with algebraMap_mem' := hR }
  have hle : T0 M' q ≤ WA := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hjW)
  have hint : IsIntegral ↥(T0 M' q) x := hx

  have hint' : IsIntegral ↥W x := by
    refine hint.map_of_comp_eq (R := ↥(T0 M' q)) (T := ↥W)
      (Subring.inclusion (show (T0 M' q).toSubring ≤ W.toSubring from fun y hy => hle hy)) (RingHom.id _) ?_
    ext y; rfl
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := FF M')).mp hint'
  rw [← hy]; exact y.2

theorem isIntegral_T0 (M' : ℕ) [NeZero M'] (q : ℕ) [Fact q.Prime] (x : ↥(Bsub M' q)) :
    letI : Algebra ↥(T0 M' q) ↥(Bsub M' q) :=
      (Subalgebra.inclusion (TwoChartIntegralModel.adjoin_le_chartAlg (Rq q) (FF M') {IgusaScheme.jFull M'})).toAlgebra
    IsIntegral ↥(T0 M' q) x := by
  letI : Algebra ↥(T0 M' q) ↥(Bsub M' q) :=
    (Subalgebra.inclusion (TwoChartIntegralModel.adjoin_le_chartAlg (Rq q) (FF M') {IgusaScheme.jFull M'})).toAlgebra
  let f : ↥(Bsub M' q) →ₐ[↥(T0 M' q)] FF M' :=
    { (Bsub M' q).val.toRingHom with commutes' := fun _ => rfl }
  have hf : Function.Injective f := Subtype.val_injective
  exact (isIntegral_algHom_iff f hf).mp x.2

theorem dvd_of_residue_eq_zero (q : ℕ) [Fact q.Prime] (c : Rq q)
    (hc : GaloisRep.ratLocalizedAtResidue q c = 0) : ((q : ℕ) : Rq q) ∣ c := by
  haveI : IsDiscreteValuationRing (Rq q) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out
  have hne : RingHom.ker (GaloisRep.ratLocalizedAtResidue q) ≠ ⊤ := RingHom.ker_ne_top _
  have hle := IsLocalRing.le_maximalIdeal hne
  rw [maximalIdeal_ratLocalizedAt q] at hle
  exact Ideal.mem_span_singleton.mp (hle ((RingHom.mem_ker).mpr hc))

theorem inv_mem_of_not_mem_span (M' : ℕ) [NeZero M'] (q : ℕ) [Fact q.Prime] (hqM' : ¬ q ∣ M')
    (W : ValuationSubring (FF M'))
    (hR : ∀ a : Rq q, algebraMap (Rq q) (FF M') a ∈ W)
    (hq : algebraMap (Rq q) (FF M') ((q : ℕ) : Rq q) ∈ W.nonunits)
    (hQ : ∀ Q : Polynomial (Rq q), Q.map (GaloisRep.ratLocalizedAtResidue q) ≠ 0 →
      Polynomial.aeval (IgusaScheme.jFull M') Q ∈ W ∧ (Polynomial.aeval (IgusaScheme.jFull M') Q)⁻¹ ∈ W)
    (b : ↥(Bsub M' q))
    (hb : b ∉ Ideal.span {algebraMap (Rq q) ↥(Bsub M' q) ((q : ℕ) : Rq q)}) :
    ((b : FF M'))⁻¹ ∈ W := by
  classical
  have hjW : IgusaScheme.jFull M' ∈ W := by
    have := (hQ Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)).1
    simpa using this
  have hBW : ∀ x : ↥(Bsub M' q), (x : FF M') ∈ W := fun x =>
    coe_mem_valuationSubring_of_mem_chartAlg M' q W hR hjW x x.2

  let φ : ↥(Bsub M' q) →+* ↥W :=
    { toFun := fun x => ⟨x, hBW x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let P : Ideal ↥(Bsub M' q) := (IsLocalRing.maximalIdeal ↥W).comap φ
  haveI hP : P.IsPrime := Ideal.comap_isPrime φ _
  have hPmem : ∀ x : ↥(Bsub M' q), x ∈ P ↔ (x : FF M') ∈ W.nonunits := by
    intro x
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    exact ⟨fun h => ⟨hBW x, h⟩, fun ⟨_, h⟩ => h⟩
  let I : Ideal ↥(Bsub M' q) := Ideal.span {algebraMap (Rq q) ↥(Bsub M' q) ((q : ℕ) : Rq q)}
  haveI hIp : I.IsPrime := isPrime_span_natCast_chartAlg M' q hqM'
  have hIP : I ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem, hPmem]
    exact hq

  have hT₀B : T0 M' q ≤ Bsub M' q := TwoChartIntegralModel.adjoin_le_chartAlg _ _ _
  letI algT : Algebra ↥(T0 M' q) ↥(Bsub M' q) := (Subalgebra.inclusion hT₀B).toAlgebra
  have hintB : ∀ x : ↥(Bsub M' q), IsIntegral ↥(T0 M' q) x := isIntegral_T0 M' q

  have hcomap : P.comap (algebraMap ↥(T0 M' q) ↥(Bsub M' q)) ≤ I.comap (algebraMap ↥(T0 M' q) ↥(Bsub M' q)) := by
    intro t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · exact Ideal.zero_mem _
    have ht0' : (t : FF M') ≠ 0 := fun h => ht0 (Subtype.ext h)
    rw [Ideal.mem_comap] at ht ⊢
    have htP : ((algebraMap ↥(T0 M' q) ↥(Bsub M' q) t : ↥(Bsub M' q)) : FF M') ∈ W.nonunits := (hPmem _).mp ht
    have hcoe : ((algebraMap ↥(T0 M' q) ↥(Bsub M' q) t : ↥(Bsub M' q)) : FF M') = (t : FF M') := rfl
    rw [hcoe] at htP

    have htmem : (t : FF M') ∈ (Polynomial.aeval (R := Rq q) (IgusaScheme.jFull M')).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact t.2
    obtain ⟨Q, hQt⟩ := (AlgHom.mem_range _).mp htmem

    have hQ0 : Q.map (GaloisRep.ratLocalizedAtResidue q) = 0 := by
      by_contra hne
      have hinv := (hQ Q hne).2
      rw [hQt] at hinv
      have hlt := (ValuationSubring.mem_nonunits_iff _).mp htP
      have hle1 := (W.valuation_le_one_iff _).mpr hinv
      rw [map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).mpr ht0')] at hle1
      exact absurd hlt (not_lt.mpr hle1)

    have hdvd : Polynomial.C ((q : ℕ) : Rq q) ∣ Q := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      apply dvd_of_residue_eq_zero
      have := congrArg (fun P => P.coeff i) hQ0
      simpa [Polynomial.coeff_map] using this
    obtain ⟨Q', hQ'⟩ := hdvd
    have hmem' : Polynomial.aeval (IgusaScheme.jFull M') Q' ∈ Bsub M' q :=
      hT₀B (by
        change _ ∈ Algebra.adjoin (Rq q) {IgusaScheme.jFull M'}
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact ⟨Q', rfl⟩)
    have : algebraMap ↥(T0 M' q) ↥(Bsub M' q) t = algebraMap (Rq q) ↥(Bsub M' q) ((q : ℕ) : Rq q) * ⟨_, hmem'⟩ := by
      apply Subtype.ext
      change (t : FF M') = algebraMap (Rq q) (FF M') ((q : ℕ) : Rq q) * Polynomial.aeval _ Q'
      rw [← hQt, hQ', map_mul, Polynomial.aeval_C]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

  have hPI : P ≤ I := by
    by_contra hnot
    obtain ⟨x, hxP, hxI⟩ := Set.not_subset.mp hnot
    have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := ↥(T0 M' q)) hIP ⟨hxP, hxI⟩ (hintB x)
    exact absurd (le_antisymm hcomap (Ideal.comap_mono hIP)) hlt.ne'

  have hbP : b ∉ P := fun h => hb (hPI h)
  have hbu : IsUnit (φ b) := by
    by_contra h
    exact hbP ((IsLocalRing.mem_maximalIdeal _).mpr h)
  obtain ⟨u, hu⟩ := hbu
  have hval : ((u⁻¹ : (↥W)ˣ) : ↥W) * φ b = 1 := by rw [← hu, Units.inv_mul]
  have hval' : (((u⁻¹ : (↥W)ˣ) : ↥W) : FF M') * (b : FF M') = 1 := by
    have := congrArg (fun w : ↥W => (w : FF M')) hval
    first | exact this | simpa using this
  rw [inv_eq_of_mul_eq_one_left hval']
  exact SetLike.coe_mem _

theorem exists_pow_mul_ratCast_eq (q : ℕ) [Fact q.Prime] (r : ℚ) :
    ∃ (n : ℕ) (s : Rq q), (q : ℚ) ^ n * r = (s : ℚ) := by
  haveI : IsDiscreteValuationRing (Rq q) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out
  haveI : IsFractionRing (Rq q) ℚ := GaloisRep.isFractionRing_ratLocalizedAt q
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Rq q) r
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0
    (GaloisRep.irreducible_natCast_ratLocalizedAt q Fact.out)
  refine ⟨n, a * ↑u⁻¹, ?_⟩
  have hbQ : (algebraMap (Rq q) ℚ b) = (u : Rq q) * (q : ℚ) ^ n := by
    rw [hu, map_mul, map_pow, map_natCast]; rfl
  have hu0 : ((u : Rq q) : ℚ) ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.ext h)
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hui : (((u⁻¹ : (Rq q)ˣ) : Rq q) : ℚ) = (((u : Rq q)) : ℚ)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← Subring.coe_mul, Units.inv_mul]
    rfl
  rw [hbQ, show (algebraMap (Rq q) ℚ a) = (a : ℚ) from rfl, Subring.coe_mul, hui]
  field_simp

noncomputable abbrev T1 (M' : ℕ) [NeZero M'] : Subalgebra ℚ (FF M') :=
  Algebra.adjoin ℚ {IgusaScheme.jFull M'}

noncomputable abbrev qF (M' : ℕ) [NeZero M'] (q : ℕ) : FF M' := algebraMap (Rq q) (FF M') ((q : ℕ) : Rq q)

theorem qF_eq (M' : ℕ) [NeZero M'] (q : ℕ) : qF M' q = algebraMap ℚ (FF M') (q : ℚ) := by
  rw [qF, IsScalarTower.algebraMap_apply (Rq q) ℚ (FF M')]
  simp

theorem exists_pow_mul_mem_T0 (M' : ℕ) [NeZero M'] (q : ℕ) [Fact q.Prime]
    (c : FF M') (hc : c ∈ T1 M') : ∃ n : ℕ, qF M' q ^ n * c ∈ T0 M' q := by
  have hqT : qF M' q ∈ T0 M' q := Subalgebra.algebraMap_mem _ _
  refine Algebra.adjoin_induction (p := fun c _ => ∃ n : ℕ, qF M' q ^ n * c ∈ T0 M' q) ?_ ?_ ?_ ?_ hc
  · intro x hx
    refine ⟨0, ?_⟩
    rw [pow_zero, one_mul]
    exact Algebra.subset_adjoin hx
  · intro r
    obtain ⟨n, s, hs⟩ := exists_pow_mul_ratCast_eq q r
    refine ⟨n, ?_⟩
    have : qF M' q ^ n * algebraMap ℚ (FF M') r = algebraMap (Rq q) (FF M') s := by
      rw [qF_eq, ← map_pow, ← map_mul, hs, IsScalarTower.algebraMap_apply (Rq q) ℚ (FF M')]
      rfl
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  · rintro x y - - ⟨n₁, h₁⟩ ⟨n₂, h₂⟩
    refine ⟨n₁ + n₂, ?_⟩
    have : qF M' q ^ (n₁ + n₂) * (x + y) =
        qF M' q ^ n₂ * (qF M' q ^ n₁ * x) + qF M' q ^ n₁ * (qF M' q ^ n₂ * y) := by ring
    rw [this]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hqT _) h₁)
      (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hqT _) h₂)
  · rintro x y - - ⟨n₁, h₁⟩ ⟨n₂, h₂⟩
    refine ⟨n₁ + n₂, ?_⟩
    have : qF M' q ^ (n₁ + n₂) * (x * y) = (qF M' q ^ n₁ * x) * (qF M' q ^ n₂ * y) := by ring
    rw [this]
    exact Subalgebra.mul_mem _ h₁ h₂

theorem exists_pow_mul_isIntegral_T0 (M' : ℕ) [NeZero M'] (q : ℕ) [Fact q.Prime]
    (x : FF M') (hx : IsIntegral ↥(T1 M') x) :
    ∃ N : ℕ, IsIntegral ↥(T0 M' q) (qF M' q ^ N * x) := by
  classical
  obtain ⟨P, hPm, hPx⟩ := hx

  have hcoef : ∀ i : ℕ, ∃ n : ℕ, qF M' q ^ n * ((P.coeff i : ↥(T1 M')) : FF M') ∈ T0 M' q :=
    fun i => exists_pow_mul_mem_T0 M' q _ (P.coeff i).2
  choose nf hnf using hcoef
  have hqT : qF M' q ∈ T0 M' q := Subalgebra.algebraMap_mem _ _
  set N : ℕ := ∑ i ∈ Finset.range (P.natDegree + 1), nf i with hN
  have hle : ∀ i, i ≤ P.natDegree → nf i ≤ N := fun i hi =>
    Finset.single_le_sum (f := nf) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have hN' : ∀ i, i ≤ P.natDegree → qF M' q ^ N * ((P.coeff i : ↥(T1 M')) : FF M') ∈ T0 M' q := by
    intro i hi
    have : qF M' q ^ N * ((P.coeff i : ↥(T1 M')) : FF M') =
        qF M' q ^ (N - nf i) * (qF M' q ^ nf i * ((P.coeff i : ↥(T1 M')) : FF M')) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hle i hi)]
    rw [this]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hqT _) (hnf i)

  have hqT1 : qF M' q ^ N ∈ T1 M' := by
    rw [qF_eq, ← map_pow]; exact Subalgebra.algebraMap_mem _ _
  set sT : ↥(T1 M') := ⟨qF M' q ^ N, hqT1⟩ with hsT
  set P' : Polynomial ↥(T1 M') := P.scaleRoots sT with hP'
  have hP'm : P'.Monic := (Polynomial.monic_scaleRoots_iff sT).mpr hPm
  have hP'x : Polynomial.eval₂ (algebraMap ↥(T1 M') (FF M')) (qF M' q ^ N * x) P' = 0 := by
    have := Polynomial.scaleRoots_eval₂_eq_zero (algebraMap ↥(T1 M') (FF M')) (s := sT) hPx
    simpa [hsT, hP'] using this

  have hle01 : ∀ y : FF M', y ∈ T0 M' q → y ∈ T1 M' := fun y hy =>
    (Algebra.adjoin_le (S := (T1 M').restrictScalars (Rq q)) Algebra.subset_adjoin) hy
  let ι : ↥(T0 M' q) →+* ↥(T1 M') :=
    { toFun := fun y => ⟨y, hle01 y y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hlifts : P' ∈ Polynomial.lifts ι := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [hP', Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    ·
      obtain ⟨k, hk⟩ : ∃ k, P.natDegree - i = k + 1 := ⟨P.natDegree - i - 1, by omega⟩
      have hmem : ((P.coeff i * sT ^ (P.natDegree - i) : ↥(T1 M')) : FF M') ∈ T0 M' q := by
        rw [hk, pow_succ', ← mul_assoc, mul_comm (P.coeff i)]
        push_cast
        rw [hsT]
        exact Subalgebra.mul_mem _ (hN' i hi.le) (Subalgebra.pow_mem _ (Subalgebra.pow_mem _ hqT _) _)
      exact ⟨⟨_, hmem⟩, Subtype.ext rfl⟩
    · subst hi
      rw [Nat.sub_self, pow_zero, mul_one, Polynomial.Monic.coeff_natDegree hPm]
      exact ⟨1, rfl⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact ⟨0, rfl⟩
  obtain ⟨Q, hQP, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hP'm
  refine ⟨N, Q, hQm, ?_⟩
  have halg : algebraMap ↥(T0 M' q) (FF M') = (algebraMap ↥(T1 M') (FF M')).comp ι := by ext y; rfl
  rw [halg, ← Polynomial.eval₂_map, hQP]
  exact hP'x

theorem gaussLift
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    {K : Type*} [Field K] [Algebra B K] (hinj : Function.Injective (algebraMap B K))
    (V : ValuationSubring K) (ϖ : B)
    (hBV : ∀ b : B, algebraMap B K b ∈ V)
    (hϖ : (algebraMap B K ϖ)⁻¹ ∉ V)
    (hunit : ∀ b : B, b ∉ Ideal.span {ϖ} → (algebraMap B K b)⁻¹ ∈ V)
    (x : K) (hx : x ∈ V) (n : ℕ) (b : B) (hb : algebraMap B K ϖ ^ n * x = algebraMap B K b) :
    x ∈ Set.range (algebraMap B K) := by
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hϖ (by simp)
  have hϖK : algebraMap B K ϖ ≠ 0 := fun h => hϖ0 (hinj (by simpa using h))
  have hϖu : ¬ IsUnit ϖ := by
    intro hu
    obtain ⟨u, rfl⟩ := hu
    apply hϖ
    have : (algebraMap B K (u : B))⁻¹ = algebraMap B K (↑u⁻¹ : B) := by
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    rw [this]
    exact hBV _
  by_cases hb0 : b = 0
  · subst hb0
    have : x = 0 := by
      have h := hb
      rw [map_zero, mul_eq_zero] at h
      rcases h with h | h
      · exact absurd (eq_zero_of_pow_eq_zero h) hϖK
      · exact h
    exact ⟨0, by simp [this]⟩
  have hfm : FiniteMultiplicity ϖ b := FiniteMultiplicity.of_not_isUnit hϖu hb0
  set m := multiplicity ϖ b with hm
  obtain ⟨b', hb'⟩ : ϖ ^ m ∣ b := pow_multiplicity_dvd ϖ b
  have hndvd : ¬ ϖ ∣ b' := by
    intro h
    obtain ⟨c, rfl⟩ := h
    have : ϖ ^ (m + 1) ∣ b := ⟨c, by rw [hb']; ring⟩
    exact hfm.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self m) this
  have hb'span : b' ∉ Ideal.span {ϖ} := by
    rwa [Ideal.mem_span_singleton]
  have hb'0 : b' ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [hb', mul_zero])
  have hb'K : algebraMap B K b' ≠ 0 := fun h => hb'0 (hinj (by simpa using h))
  rcases le_or_gt n m with hnm | hnm
  · refine ⟨ϖ ^ (m - n) * b', ?_⟩
    have h1 : algebraMap B K ϖ ^ n * x =
        algebraMap B K ϖ ^ n * (algebraMap B K ϖ ^ (m - n) * algebraMap B K b') := by
      rw [hb, hb', map_mul, map_pow, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hnm]
    have h2 := mul_left_cancel₀ (pow_ne_zero n hϖK) h1
    rw [map_mul, map_pow, ← h2]
  · exfalso
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hnm
    have h1 : algebraMap B K ϖ ^ m * (algebraMap B K ϖ ^ (d + 1) * x) =
        algebraMap B K ϖ ^ m * algebraMap B K b' := by
      rw [← mul_assoc, ← pow_add, show m + (d + 1) = n by omega, hb, hb', map_mul, map_pow]
    have h2 : algebraMap B K ϖ ^ (d + 1) * x = algebraMap B K b' :=
      mul_left_cancel₀ (pow_ne_zero m hϖK) h1
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hb'K (by rw [← h2, mul_zero])
    have hxeq : x * (algebraMap B K b')⁻¹ * algebraMap B K ϖ ^ d = (algebraMap B K ϖ)⁻¹ := by
      rw [← h2, mul_inv, pow_succ, mul_inv]
      field_simp
    apply hϖ
    rw [← hxeq]
    exact V.toSubring.mul_mem (V.toSubring.mul_mem hx (hunit b' hb'span))
      (V.toSubring.pow_mem (hBV ϖ) d)

theorem isIntegral_transfer
    {R₁ R₂ S U' U : Type*} [CommRing R₁] [CommRing R₂] [CommRing S] [CommRing U'] [CommRing U]
    [Algebra R₁ S] [Algebra R₂ U']
    (C : Subalgebra R₁ S) (D : Subalgebra R₂ U')
    (ψ : S →+* U) (τ : U' →+* U) (hτ : Function.Injective τ)
    (hCD : ∀ c : S, c ∈ C → ∃ d ∈ D, τ d = ψ c)
    {x : S} (hx : IsIntegral ↥C x) {x' : U'} (hx' : τ x' = ψ x) : IsIntegral ↥D x' := by
  classical
  choose d hdmem hd using hCD
  let φ : ↥C →+* ↥D :=
    { toFun := fun c => ⟨d c.1 c.2, hdmem c.1 c.2⟩
      map_one' := Subtype.ext (hτ (by simp [hd]))
      map_mul' := fun a b => Subtype.ext (hτ (by simp [hd]))
      map_zero' := Subtype.ext (hτ (by simp [hd]))
      map_add' := fun a b => Subtype.ext (hτ (by simp [hd])) }
  letI : Algebra ↥D U := (τ.comp (algebraMap ↥D U')).toAlgebra
  have h1 : IsIntegral ↥D (ψ x) := by
    refine hx.map_of_comp_eq φ ψ ?_
    ext c
    change τ (d c.1 c.2) = ψ c
    exact hd c.1 c.2
  let f : U' →ₐ[↥D] U := { τ with commutes' := fun _ => rfl }
  rw [← hx'] at h1
  exact (isIntegral_algHom_iff f hτ).mp h1

theorem mem_Bsub_of_forall_coeff_mem_of_isIntegral (M' : ℕ) [NeZero M'] (q : ℕ) [Fact q.Prime] (hqM' : ¬ q ∣ M')
    (x : FF M') (hcoeff : ∀ n : ℤ, (x : LaurentSeries ℚ).coeff n ∈ GaloisRep.ratLocalizedAt q)
    (hint : IsIntegral ↥(T1 M') x) : x ∈ Bsub M' q := by
  classical
  haveI : IsDiscreteValuationRing (Rq q) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out

  obtain ⟨W, hpin, hR, hq, hQ⟩ := exists_gauss M' q
  have hxW : x ∈ W := (hpin x).mpr (exists_gaussPresentation q _ hcoeff)
  have hjW : IgusaScheme.jFull M' ∈ W := by
    have := (hQ Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)).1
    simpa using this

  obtain ⟨N, hN⟩ := exists_pow_mul_isIntegral_T0 M' q x hint
  have hyB : qF M' q ^ N * x ∈ Bsub M' q := hN

  haveI : IsNoetherianRing ↥(Bsub M' q) :=
    Algebra.FiniteType.isNoetherianRing (Rq q) _ (h := finiteType_chartAlg_jFull M' q)
  have hinj : Function.Injective (algebraMap ↥(Bsub M' q) (FF M')) := Subtype.val_injective
  have hBV : ∀ b : ↥(Bsub M' q), algebraMap ↥(Bsub M' q) (FF M') b ∈ W := fun b =>
    coe_mem_valuationSubring_of_mem_chartAlg M' q W hR hjW b b.2
  have hϖ : (algebraMap ↥(Bsub M' q) (FF M') (algebraMap (Rq q) ↥(Bsub M' q) ((q : ℕ) : Rq q)))⁻¹ ∉ W := by
    change (qF M' q)⁻¹ ∉ W
    intro hinv
    have hlt := (ValuationSubring.mem_nonunits_iff _).mp hq
    have hq0 : qF M' q ≠ 0 := by
      rw [qF_eq]
      exact (map_ne_zero _).mpr (by exact_mod_cast (Fact.out : q.Prime).ne_zero)
    have hle1 := (W.valuation_le_one_iff _).mpr hinv
    rw [map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).mpr hq0)] at hle1
    exact absurd hlt (not_lt.mpr hle1)
  have hunit : ∀ b : ↥(Bsub M' q), b ∉ Ideal.span {algebraMap (Rq q) ↥(Bsub M' q) ((q : ℕ) : Rq q)} →
      (algebraMap ↥(Bsub M' q) (FF M') b)⁻¹ ∈ W := fun b hb =>
    inv_mem_of_not_mem_span M' q hqM' W hR hq hQ b hb
  obtain ⟨b, hb⟩ := gaussLift hinj W _ hBV hϖ hunit x hxW N ⟨_, hyB⟩ (by simp)
  rw [← hb]
  exact b.2

noncomputable def toRing (q : ℕ) [Fact q.Prime]
    (A : Type) [CommRing A] [IsLocalRing A] (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) : Rq q →+* A :=
  haveI : IsLocalization.AtPrime (Rq q) (Ideal.span {(q : ℤ)}) :=
    GaloisRep.isLocalization_ratLocalizedAt (Fact.out : q.Prime)
  IsLocalization.lift (M := (Ideal.span {(q : ℤ)}).primeCompl) (g := Int.castRingHom A) (fun y => by
    obtain ⟨y, hy⟩ := y
    have hy' : ¬ (q : ℤ) ∣ y := by
      simpa [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton] using hy
    simpa using isUnit_intCast_of_not_dvd q A hAq y hy')

private theorem _root_.ModularCurve.IntClAux.ringHom_ext (q : ℕ) [Fact q.Prime] {T : Type} [CommRing T] (f g : Rq q →+* T) : f = g := by
  haveI : IsLocalization.AtPrime (Rq q) (Ideal.span {(q : ℤ)}) :=
    GaloisRep.isLocalization_ratLocalizedAt (Fact.out : q.Prime)
  refine IsLocalization.ringHom_ext (Ideal.span {(q : ℤ)}).primeCompl ?_
  exact RingHom.ext_int _ _

p2m_export "ModularCurve.IntClAux" "ringHom_ext"
end ModularCurve.IntClAux

open ModularCurve.IntClAux in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (g : LaurentSeries ℚ) (hg : g ∈ ModularCurve.modularFunctionFieldFull M')
    (hgA : ∀ n : ℤ, ∃ a : A, algebraMap A L a = algebraMap ℚ L (g.coeff n))
    (hgj : IsIntegral ↥(Algebra.adjoin ℚ ({ModularCurve.jq} : Set (LaurentSeries ℚ))) g)
    (hgK : ModularCurve.coeffEmb L g ∈ K) :
    (⟨ModularCurve.coeffEmb L g, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j := by
  classical
  set gF : FF M' := ⟨g, hg⟩ with hgF

  have hcoeff : ∀ n : ℤ, (gF : LaurentSeries ℚ).coeff n ∈ GaloisRep.ratLocalizedAt q := by
    intro n
    obtain ⟨a, ha⟩ := hgA n
    exact mem_ratLocalizedAt_of_eq q L A (IsFractionRing.injective A L) hAq _ a ha

  have hint1 : IsIntegral ↥(T1 M') gF := by
    refine isIntegral_transfer (Algebra.adjoin ℚ ({ModularCurve.jq} : Set (LaurentSeries ℚ))) (T1 M')
      (RingHom.id _) (algebraMap (FF M') (LaurentSeries ℚ)) Subtype.val_injective ?_ hgj rfl
    intro c hc
    refine Algebra.adjoin_induction (p := fun c _ => ∃ d ∈ T1 M',
      algebraMap (FF M') (LaurentSeries ℚ) d = (RingHom.id _) c) ?_ ?_ ?_ ?_ hc
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨IgusaScheme.jFull M', Algebra.subset_adjoin rfl, rfl⟩
    · intro r
      refine ⟨algebraMap ℚ (FF M') r, Subalgebra.algebraMap_mem _ _, ?_⟩
      exact RingHom.congr_fun (Subsingleton.elim ((algebraMap (FF M') (LaurentSeries ℚ)).comp (algebraMap ℚ (FF M')))
        (algebraMap ℚ (LaurentSeries ℚ))) r
    · rintro x y - - ⟨d₁, hd₁, h₁⟩ ⟨d₂, hd₂, h₂⟩
      exact ⟨d₁ + d₂, Subalgebra.add_mem _ hd₁ hd₂, by rw [map_add, map_add, h₁, h₂]⟩
    · rintro x y - - ⟨d₁, hd₁, h₁⟩ ⟨d₂, hd₂, h₂⟩
      exact ⟨d₁ * d₂, Subalgebra.mul_mem _ hd₁ hd₂, by rw [map_mul, map_mul, h₁, h₂]⟩

  have hmem : gF ∈ Bsub M' q := mem_Bsub_of_forall_coeff_mem_of_isIntegral M' q hqM' gF hcoeff hint1
  have hint0 : IsIntegral ↥(T0 M' q) gF := hmem

  letI algZA : Algebra (Rq q) A := (toRing q A hAq).toAlgebra
  haveI : IsScalarTower (Rq q) A L := IsScalarTower.of_algebraMap_eq' (ringHom_ext q _ _)
  have hcoeK : ∀ y : L, ((algebraMap L ↥K y : ↥K) : LaurentSeries L) = HahnSeries.single 0 y := fun y => by
    rw [← ModularCurve.algebraMap_laurentSeries_eq_single]; rfl
  have hRF : ∀ r : Rq q, ((algebraMap (Rq q) (FF M') r : FF M') : LaurentSeries ℚ) = HahnSeries.single 0 (r : ℚ) :=
    fun r => RingHom.congr_fun (ringHom_ext q ((algebraMap (FF M') (LaurentSeries ℚ)).comp (algebraMap (Rq q) (FF M')))
      ((HahnSeries.C : ℚ →+* LaurentSeries ℚ).comp (GaloisRep.ratLocalizedAt q).subtype)) r
  refine isIntegral_transfer (T0 M' q) (Algebra.adjoin A ({j} : Set ↥K))
    ((ModularCurve.coeffEmb L).comp (algebraMap (FF M') (LaurentSeries ℚ))) (algebraMap ↥K (LaurentSeries L))
    Subtype.val_injective ?_ hint0 rfl
  intro c hc
  refine Algebra.adjoin_induction (p := fun c _ => ∃ d ∈ Algebra.adjoin A ({j} : Set ↥K),
    algebraMap ↥K (LaurentSeries L) d = ((ModularCurve.coeffEmb L).comp (algebraMap (FF M') (LaurentSeries ℚ))) c)
    ?_ ?_ ?_ ?_ hc
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨j, Algebra.subset_adjoin rfl, hj⟩
  · intro r
    refine ⟨algebraMap A ↥K (algebraMap (Rq q) A r), Subalgebra.algebraMap_mem _ _, ?_⟩
    rw [IsScalarTower.algebraMap_apply A L ↥K, ← IsScalarTower.algebraMap_apply (Rq q) A L]
    change ((algebraMap L ↥K _ : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L ((algebraMap (Rq q) (FF M') r : FF M') : LaurentSeries ℚ)
    rw [hcoeK, IsScalarTower.algebraMap_apply (Rq q) ℚ L, hRF, ModularCurve.coeffEmb, ModularCurve.coeffMap_single]
    rfl
  · rintro x y - - ⟨d₁, hd₁, h₁⟩ ⟨d₂, hd₂, h₂⟩
    exact ⟨d₁ + d₂, Subalgebra.add_mem _ hd₁ hd₂, by rw [map_add, map_add, h₁, h₂]⟩
  · rintro x y - - ⟨d₁, hd₁, h₁⟩ ⟨d₂, hd₂, h₂⟩
    exact ⟨d₁ * d₂, Subalgebra.mul_mem _ hd₁ hd₂, by rw [map_mul, map_mul, h₁, h₂]⟩

end S_ModularCurve_coeffEmb_mem_chartAlgFin_of_forall_coeff_of_isIntegral_adjoin_jq
end P2MW
export P2MW.S_ModularCurve_coeffEmb_mem_chartAlgFin_of_forall_coeff_of_isIntegral_adjoin_jq (solution)
