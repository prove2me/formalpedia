-- Prove2me | solution 1 for ModularCurve.exists_dRModelPackage_ffPin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/8d423db2-3d14-5c56-b5e1-dddbe1212711

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Theorems.Thm_AlgebraicGeometry_mem_smoothLocus_of_not_mem_range_of_isClosedImmersion
import Theorems.Thm_ModularCurve_DRModel_isReduced_pullback_toBase_of_charP

import Theorems.Thm_ModularCurve_IgusaScheme_isProper_toBase_int
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_flat_toBase
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_sections_of_isAffineOpen
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_int_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_locallyOfFinitePresentation_toBase
import Theorems.Thm_ModularCurve_IgusaScheme_smooth_pullback_snd_toBase_int_localizationAway
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algHom_int_chartAlgInf_eq_coeff_zero
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_nonempty_schemeHomOver_id_toBase_of_algHom
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_rat_tensor_chartAlg_chartRing
import Theorems.Thm_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_galoisCompat_and_ratPlaceCompat
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_CharPModel_finiteDimensional_adjoin_jBar
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_IgusaScheme_exists_isPullback_twoChartIntegralModel_int_and_iso_pullback_and_iotaFin_comp_eq
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_irreducibleSpace
import Theorems.Thm_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
import Theorems.Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_charZero
import Theorems.Thm_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators
import Theorems.Thm_ModularCurve_DRModel_isReduced_pFibre
import Theorems.Thm_ModularCurve_DRModel_exists_chartAlgFin_valuationSubring_pair_levelP
import Theorems.Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_charP
import Theorems.Thm_ModularCurve_DRModel_exists_iso_comp_toBase_eq_and_hom_comp_hom_eq_id_and_exists_algHom_comp_hom_eq
import Theorems.Thm_ModularCurve_DRModel_dvd_coeffZero_of_mem_nonunits_and_exists_not_dvd_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_dRModelPackage_ffPin
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply RegularLocalRingQuotientAscent.dualNumberFst_apply"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply"
p2m_attr_erase "simp" "HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry ModularCurve~jBar P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.ModularCurve AlgebraicCurve P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicCurve IsLocalRing"
open scoped TensorProduct

attribute [local instance] ModularCurve.DRModelPackage.neZero_of_fact_prime

universe u

section
open TopologicalSpace
namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.congr_app Spec.map_preimage IsOpenImmersion.lift SmoothOfRelativeDimension.smooth IsOpenImmersion.of_comp Spec.map_comp_assoc SmoothOfRelativeDimension Scheme.Hom Scheme.Hom.smoothLocus Spec Scheme.Opens.toScheme Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Smooth IsOpenImmersion Scheme.Hom.comp_base genericPoint_eq_of_isOpenImmersion Flat HasRingHomProperty.comp_of_isOpenImmersion IsClosedImmersion IsReduced Scheme.Hom.comp_app Spec.map_id Scheme.Opens LocallyOfFinitePresentation HasRingHomProperty IsOpenImmersion.lift_fac Scheme.ΓSpecIso mem_smoothLocus_of_not_mem_range_of_isClosedImmersion smoothOfRelativeDimension_of_irreducibleSpace exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.congr_app germToFunctionField Hom Γ Hom.smoothLocus Opens.toScheme ΓSpecIso_inv_naturality Hom.comp_base Hom.comp_app Opens ΓSpecIso"
namespace Hom
p2m_export "AlgebraicGeometry.Scheme.Hom" "congr_app image preimage_smoothLocus_eq smoothLocus_eq_top_iff app smoothLocus injective appIso_inv_app appIso appTop comp_base naturality comp_app smoothLocus_eq_top appIso_hom preimage_image_eq ker comp_apply"
p2m_open "AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]

theorem smoothLocus_congr {g : X ⟶ Y} [LocallyOfFinitePresentation g] (h : g = f) :
    g.smoothLocus = f.smoothLocus := by
  subst h; rfl

private theorem _root_.AlgebraicGeometry.Scheme.Hom.le_smoothLocus_of_smooth (U : X.Opens) [Smooth (U.ι ≫ f)] : U ≤ f.smoothLocus := by
  intro x hx
  have h : (Opens.map U.ι.base).obj f.smoothLocus = ⊤ := by
    rw [preimage_smoothLocus_eq U.ι f, smoothLocus_eq_top]
  have hx' : (⟨x, hx⟩ : U) ∈ (Opens.map U.ι.base).obj f.smoothLocus := by
    rw [h]; exact Opens.mem_top _
  (first | exact hx' | simpa using hx' | (have h__ := hx'; simp at h__; exact h__))

p2m_export "AlgebraicGeometry.Scheme.Hom" "le_smoothLocus_of_smooth"

private theorem _root_.AlgebraicGeometry.Scheme.Hom.le_smoothLocus_of_smoothOfRelativeDimension (n : ℕ) (U : X.Opens)
    [SmoothOfRelativeDimension n (U.ι ≫ f)] : U ≤ f.smoothLocus :=
  haveI : Smooth (U.ι ≫ f) := SmoothOfRelativeDimension.smooth n _
  f.le_smoothLocus_of_smooth U

p2m_export "AlgebraicGeometry.Scheme.Hom" "le_smoothLocus_of_smoothOfRelativeDimension"

scoped instance smooth_smoothLocus_ι_comp : Smooth (f.smoothLocus.ι ≫ f) := by
  rw [← smoothLocus_eq_top_iff, ← preimage_smoothLocus_eq f.smoothLocus.ι f]
  exact f.smoothLocus.ι_preimage_self

private theorem _root_.AlgebraicGeometry.Scheme.Hom.smoothLocus_le_preimage_of_iso_over (w : X ≅ X) (hw : w.hom ≫ f = f) :
    f.smoothLocus ≤ (Opens.map w.hom.base).obj f.smoothLocus := by
  rw [preimage_smoothLocus_eq w.hom f, smoothLocus_congr f hw]

p2m_export "AlgebraicGeometry.Scheme.Hom" "smoothLocus_le_preimage_of_iso_over"

private theorem _root_.AlgebraicGeometry.Scheme.Hom.apply_mem_smoothLocus_of_iso_over (w : X ≅ X) (hw : w.hom ≫ f = f) {x : X}
    (hx : x ∈ f.smoothLocus) : w.hom.base x ∈ f.smoothLocus :=
  f.smoothLocus_le_preimage_of_iso_over w hw hx

p2m_export "AlgebraicGeometry.Scheme.Hom" "apply_mem_smoothLocus_of_iso_over"

private theorem _root_.AlgebraicGeometry.Scheme.Hom.range_comp_subset_smoothLocus_of_iso_over (w : X ≅ X) (hw : w.hom ≫ f = f)
    {T : Scheme.{u}} (s : T ⟶ X) (hs : Set.range s.base ⊆ (f.smoothLocus : Set X)) :
    Set.range (s ≫ w.hom).base ⊆ (f.smoothLocus : Set X) := by
  rintro _ ⟨t, rfl⟩
  rw [Scheme.Hom.comp_base, TopCat.comp_app]
  exact f.apply_mem_smoothLocus_of_iso_over w hw (hs ⟨t, rfl⟩)

p2m_export "AlgebraicGeometry.Scheme.Hom" "range_comp_subset_smoothLocus_of_iso_over"

private theorem _root_.AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_smoothLocus_ι_comp (n : ℕ) [IrreducibleSpace X]
    (W : X.Opens) (hW : (W : Set X).Nonempty) [hWsm : SmoothOfRelativeDimension n (W.ι ≫ f)] :
    SmoothOfRelativeDimension n (f.smoothLocus.ι ≫ f) := by
  have hWle : W ≤ f.smoothLocus := f.le_smoothLocus_of_smoothOfRelativeDimension n W

  obtain ⟨x₀, hx₀⟩ := hW
  have hirr := @Topology.IsOpenEmbedding.irreducibleSpace _ _ _ _ _ f.smoothLocus.isOpenEmbedding'
    inferInstance ⟨⟨x₀, hWle hx₀⟩⟩
  haveI : IrreducibleSpace (↥(f.smoothLocus : Scheme.{u})) := hirr

  let V : (f.smoothLocus : Scheme.{u}).Opens := (Opens.map f.smoothLocus.ι.base).obj W
  have hV : (V : Set f.smoothLocus).Nonempty := ⟨⟨x₀, hWle hx₀⟩, hx₀⟩

  have hrange : Set.range (V.ι ≫ f.smoothLocus.ι).base ⊆ Set.range W.ι.base := by
    rintro _ ⟨v, rfl⟩
    refine ⟨⟨(f.smoothLocus.ι.base (V.ι.base v)), ?_⟩, ?_⟩
    · exact v.2
    · simp
  let l : (V : Scheme.{u}) ⟶ W := IsOpenImmersion.lift W.ι (V.ι ≫ f.smoothLocus.ι) hrange
  have hl : l ≫ W.ι = V.ι ≫ f.smoothLocus.ι := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (l ≫ W.ι) := by rw [hl]; infer_instance
  haveI : IsOpenImmersion l := IsOpenImmersion.of_comp l W.ι
  haveI : SmoothOfRelativeDimension n (V.ι ≫ (f.smoothLocus.ι ≫ f)) := by
    have h := HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension n) (f := l)
      (W.ι ≫ f) hWsm
    rwa [← Category.assoc, hl, Category.assoc] at h
  exact AlgebraicGeometry.smoothOfRelativeDimension_of_irreducibleSpace n (f.smoothLocus.ι ≫ f) V hV

p2m_export "AlgebraicGeometry.Scheme.Hom" "smoothOfRelativeDimension_smoothLocus_ι_comp"
end AlgebraicGeometry.Scheme.Hom
p2m_reactivate "P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry.Scheme.Hom"
p2m_reactivate "P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry"
end
p2m_reactivate "P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry.Scheme.Hom"

section ExportTools
p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.congr_app Spec.map_preimage IsOpenImmersion.lift SmoothOfRelativeDimension.smooth IsOpenImmersion.of_comp Spec.map_comp_assoc SmoothOfRelativeDimension Scheme.Hom Scheme.Hom.smoothLocus Spec Scheme.Opens.toScheme Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Smooth IsOpenImmersion Scheme.Hom.comp_base genericPoint_eq_of_isOpenImmersion Flat HasRingHomProperty.comp_of_isOpenImmersion IsClosedImmersion IsReduced Scheme.Hom.comp_app Spec.map_id Scheme.Opens LocallyOfFinitePresentation HasRingHomProperty IsOpenImmersion.lift_fac Scheme.ΓSpecIso mem_smoothLocus_of_not_mem_range_of_isClosedImmersion smoothOfRelativeDimension_of_irreducibleSpace exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.congr_app germToFunctionField Hom Γ Hom.smoothLocus Opens.toScheme ΓSpecIso_inv_naturality Hom.comp_base Hom.comp_app Opens ΓSpecIso" end AlgebraicGeometry.Scheme
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme" in
theorem AlgebraicGeometry.Scheme.appIso_hom_res_app_appIso_inv_apply
    {X Y : Scheme} (f : Y ⟶ X) {A B : CommRingCat} (ι : Spec A ⟶ X) [IsOpenImmersion ι]
    (g : Spec B ⟶ Y) [IsOpenImmersion g] (θ : A ⟶ B) (hfac : g ≫ f = Spec.map θ ≫ ι) (a : A)
    (V' : (Spec B).Opens) (hV' : g ''ᵁ V' ≤ f ⁻¹ᵁ (ι ''ᵁ ⊤)) :
    (g.appIso V').hom (Y.presheaf.map (homOfLE hV').op
      ((f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a)))) =
    (Spec B).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso B).inv (θ a)) := by
  let V : X.Opens := ι ''ᵁ ⊤
  let r := (Scheme.ΓSpecIso A).inv a
  show (g.appIso V').hom (Y.presheaf.map (homOfLE hV').op ((f.app V) ((ι.appIso ⊤).inv r))) = _

  have e1 := CategoryTheory.ConcreteCategory.congr_hom (g.appIso_hom V')
    (Y.presheaf.map (homOfLE hV').op ((f.app V) ((ι.appIso ⊤).inv r)))
  rw [CategoryTheory.comp_apply] at e1
  rw [e1]

  have e2 := CategoryTheory.ConcreteCategory.congr_hom (g.naturality (homOfLE hV').op) ((f.app V) ((ι.appIso ⊤).inv r))
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e2
  rw [e2]

  have e3 := CategoryTheory.ConcreteCategory.congr_hom
    ((Scheme.Hom.comp_app g f V).symm.trans ((Scheme.Hom.congr_app hfac V).trans
      (congrArg (· ≫ (Spec B).presheaf.map _) (Scheme.Hom.comp_app (Spec.map θ) ι V))))
    ((ι.appIso ⊤).inv r)
  erw [e3]
  erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply]

  have e4 := CategoryTheory.ConcreteCategory.congr_hom (ι.appIso_inv_app ⊤) r
  rw [CategoryTheory.comp_apply] at e4
  erw [e4]

  have e5 := CategoryTheory.ConcreteCategory.congr_hom
    ((Spec.map θ).naturality (eqToHom (ι.preimage_image_eq ⊤)).op) r
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e5
  erw [e5]

  have e6 := CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality θ) a
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e6
  erw [← e6]

  simp only [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

end ExportTools
p2m_reactivate "P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry.Scheme.Hom"

section ExportGenerator
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry Opposite TopologicalSpace"
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicCurve AlgebraicCurve.CurveModel P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicCurve.CurveModel"
open scoped IntermediateField
namespace AlgebraicCurve p2m_export "AlgebraicCurve" "TwoChartIntegralModel.chartAlgFin TwoChartIntegralModel.chartAlgInf TwoChartIntegralModel TwoChartIntegralModel.ιFin TwoChartIntegralModel.ιInf TwoChartIntegralModel.toBase TwoChartIntegralModel.ιInf_toBase TwoChartIntegralModel.chartBaseChange CurveModel CurveModel.X₀ CurveModel.ι₀ CurveModel.ofGenerator CurveModel.chartRing TwoChartIntegralModel.flat_toBase TwoChartIntegralModel.isIntegral TwoChartIntegralModel.isIntegrallyClosed_sections_of_isAffineOpen TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf TwoChartIntegralModel.locallyOfFinitePresentation_toBase finiteDimensional_adjoin_of_transcendental" namespace CurveModel p2m_export "AlgebraicCurve.CurveModel" "isProper toBase C ffEquiv isIntegral smooth incl₀ X₀ glued ι₀ ιInf gluedFunctionFieldEquiv thetaHom_toStalk secTop germ_res_secTop ffEquiv_symm_germ_appIso_inv ofGenerator chartRing coe_chartIncl centre" end AlgebraicCurve.CurveModel
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.CurveModel" in

theorem AlgebraicCurve.CurveModel.glued_ffEquiv_symm_germToFunctionField
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
    {X : Scheme.{u}} (f : glued K t ⟶ X) {A₀ : CommRingCat.{u}}
    (ι : Spec A₀ ⟶ X) [IsOpenImmersion ι]
    (θ : A₀ ⟶ CommRingCat.of ↥(chartRing K ({t} : Set L)))
    (hfac : ι₀ K t ≫ f = Spec.map θ ≫ ι) (a : A₀)
    [hne : Nonempty (f ⁻¹ᵁ (ι ''ᵁ ⊤))] :
    (((gluedFunctionFieldEquiv K t).symm
      ((glued K t).germToFunctionField (f ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A₀).inv a))))) : L) =
      ((θ a : ↥(chartRing K ({t} : Set L))) : L) := by
  set U : (glued K t).Opens := f ⁻¹ᵁ (ι ''ᵁ ⊤) with hU
  set σ : Γ(glued K t, U) := (f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A₀).inv a)) with hσ
  let V' : (X₀ K t).Opens := (ι₀ K t) ⁻¹ᵁ U
  have hV'U : (ι₀ K t) ''ᵁ V' ≤ U := by
    rintro _ ⟨x, hx, rfl⟩; exact hx

  have hηU : genericPoint (glued K t) ∈ U := by
    obtain ⟨⟨x, hx⟩⟩ := hne
    exact ((genericPoint_spec (glued K t)).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩
  have hξV' : genericPoint (X₀ K t) ∈ V' := by
    show (ι₀ K t).base (genericPoint (X₀ K t)) ∈ U
    rw [genericPoint_eq_of_isOpenImmersion]
    exact hηU
  have hη : genericPoint (glued K t) ∈ (ι₀ K t) ''ᵁ V' :=
    ⟨genericPoint (X₀ K t), hξV', genericPoint_eq_of_isOpenImmersion _⟩

  have step1 : (glued K t).germToFunctionField U σ =
      (glued K t).presheaf.germ ((ι₀ K t) ''ᵁ V') (genericPoint (glued K t)) hη
        (((ι₀ K t).appIso V').inv (((ι₀ K t).appIso V').hom
          ((glued K t).presheaf.map (homOfLE hV'U).op σ))) := by
    rw [Iso.hom_inv_id_apply, TopCat.Presheaf.germ_res_apply]

  have step2 : ((ι₀ K t).appIso V').hom ((glued K t).presheaf.map (homOfLE hV'U).op σ) =
      (X₀ K t).presheaf.map (homOfLE le_top).op (secTop K (chartRing K ({t} : Set L)) (θ a)) :=
    AlgebraicGeometry.Scheme.appIso_hom_res_app_appIso_inv_apply f ι (ι₀ K t) θ hfac a V' hV'U
  rw [step1, step2]

  rw [ffEquiv_symm_germ_appIso_inv K t (chartRing K ({t} : Set L)) (ι₀ K t) (incl₀ K t)
    (fun b => coe_chartIncl K _ b) rfl V' _ (genericPoint (X₀ K t)) hξV' hη]

  rw [germ_res_secTop]
  exact thetaHom_toStalk K t (chartRing K ({t} : Set L)) (incl₀ K t) (fun b => coe_chartIncl K _ b) _ _

p2m_open_scoped "AlgebraicCurve AlgebraicCurve.CurveModel" in

theorem AlgebraicCurve.CurveModel.ofGenerator_ffEquiv_symm_germToFunctionField
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    (ht : Transcendental K t)
    {X : Scheme.{u}} (f : (CurveModel.ofGenerator K t ht).C ⟶ X) {A₀ : CommRingCat.{u}}
    (ι : Spec A₀ ⟶ X) [IsOpenImmersion ι]
    (θ : A₀ ⟶ CommRingCat.of ↥(chartRing K ({t} : Set L)))
    (hfac : ι₀ K t ≫ f = Spec.map θ ≫ ι) (a : A₀)
    [hne : Nonempty (f ⁻¹ᵁ (ι ''ᵁ ⊤))] :
    (((CurveModel.ofGenerator K t ht).ffEquiv.symm
      ((CurveModel.ofGenerator K t ht).C.germToFunctionField (f ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A₀).inv a))))) : L) =
      ((θ a : ↥(chartRing K ({t} : Set L))) : L) :=
  @AlgebraicCurve.CurveModel.glued_ffEquiv_symm_germToFunctionField K _ L _ _ t _ _ X f A₀ ι _ θ hfac a hne

end ExportGenerator
p2m_reactivate "P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_exists_dRModelPackage_ffPin.AlgebraicGeometry.Scheme.Hom"

namespace ModularCurve p2m_export "ModularCurve" "DRModelPackage.neZero_of_fact_prime DRModel DRModel.toBase DRModel.sectionFibre DRModelPackage jq ModularPolynomialData modularFunctionFieldFull IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme.chartAlgFin IgusaScheme.chartAlgInf IgusaScheme IgusaScheme.igusaTo coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldBar ssJSet DRModel.isReduced_pullback_toBase_of_charP IgusaScheme.isProper_toBase_int transcendental_jq finiteDimensional_adjoin_jFull_modularFunctionFieldFull IgusaScheme.finiteType_int_chartAlgFin_and_chartAlgInf IgusaScheme.smooth_pullback_snd_toBase_int_localizationAway IgusaScheme.exists_algHom_int_chartAlgInf_eq_coeff_zero IgusaScheme.exists_algEquiv_tensor_chartAlg_chartRing CharPModel.jBar IgusaScheme.exists_algEquiv_rat_tensor_chartAlg_chartRing IgusaScheme.exists_genericFibreIso_chartPin_galoisCompat_and_ratPlaceCompat transcendental_coeffEmb_jq CharPModel.finiteDimensional_adjoin_jBar nonempty_modularPolynomialData IgusaScheme.exists_isPullback_twoChartIntegralModel_int_and_iso_pullback_and_iotaFin_comp_eq IgusaScheme.smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_charZero DRModel.exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators DRModel.isReduced_pFibre DRModel.exists_chartAlgFin_valuationSubring_pair_levelP IgusaScheme.smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_charP DRModel.exists_iso_comp_toBase_eq_and_hom_comp_hom_eq_id_and_exists_algHom_comp_hom_eq DRModel.dvd_coeffZero_of_mem_nonunits_and_exists_not_dvd_of_prime" end ModularCurve
p2m_open_scoped "ModularCurve" in

structure ModularCurve.LEG1aCert (p : ℕ) [Fact p.Prime] where
  pkg : DRModelPackage p
  hne : Nonempty (Scheme.Opens.toScheme
        ((pkg.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
          ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))
  hMη : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
        ((pkg.Mη.ffEquiv.symm
            (pkg.Mη.C.germToFunctionField
              ((pkg.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
                ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
              (((pkg.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).app
                  ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
                (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of
                    ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))
            : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ)

namespace ModularCurve p2m_export "ModularCurve" "DRModelPackage.neZero_of_fact_prime DRModel DRModel.toBase DRModel.sectionFibre DRModelPackage jq ModularPolynomialData modularFunctionFieldFull IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme.chartAlgFin IgusaScheme.chartAlgInf IgusaScheme IgusaScheme.igusaTo coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldBar ssJSet DRModel.isReduced_pullback_toBase_of_charP IgusaScheme.isProper_toBase_int transcendental_jq finiteDimensional_adjoin_jFull_modularFunctionFieldFull IgusaScheme.finiteType_int_chartAlgFin_and_chartAlgInf IgusaScheme.smooth_pullback_snd_toBase_int_localizationAway IgusaScheme.exists_algHom_int_chartAlgInf_eq_coeff_zero IgusaScheme.exists_algEquiv_tensor_chartAlg_chartRing CharPModel.jBar IgusaScheme.exists_algEquiv_rat_tensor_chartAlg_chartRing IgusaScheme.exists_genericFibreIso_chartPin_galoisCompat_and_ratPlaceCompat transcendental_coeffEmb_jq CharPModel.finiteDimensional_adjoin_jBar nonempty_modularPolynomialData IgusaScheme.exists_isPullback_twoChartIntegralModel_int_and_iso_pullback_and_iotaFin_comp_eq IgusaScheme.smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_charZero DRModel.exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators DRModel.isReduced_pFibre DRModel.exists_chartAlgFin_valuationSubring_pair_levelP IgusaScheme.smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_charP DRModel.exists_iso_comp_toBase_eq_and_hom_comp_hom_eq_id_and_exists_algHom_comp_hom_eq DRModel.dvd_coeffZero_of_mem_nonunits_and_exists_not_dvd_of_prime" namespace LEG1aCert end ModularCurve.LEG1aCert
p2m_open_scoped "ModularCurve" in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem ModularCurve.LEG1aCert.nonempty (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : Nonempty (LEG1aCert p) := by
  classical

  obtain ⟨jp, W₀, W₁, hjp, hp₀, hp₁, hneW, hgen, hcomplete, ht, hres₀, hres₁⟩ :=
    ModularCurve.DRModel.exists_chartAlgFin_valuationSubring_pair_levelP p

  have htjℚ : Transcendental ℚ (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) := by
    intro halg
    obtain ⟨q, hq, hev⟩ := halg
    refine ModularCurve.transcendental_jq ⟨q, hq, ?_⟩
    have h0 : (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ))
        ((Polynomial.aeval (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p))) q) = 0 := by
      rw [hev, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
        show (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)) (IgusaScheme.jFull p) = jq from
          IgusaScheme.coe_jFull p] at h0
    rw [Polynomial.aeval_def]
    convert h0 using 2 <;> first | rfl | exact Subsingleton.elim _ _
  have htj : Transcendental ℤ (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) := fun h =>
    htjℚ ((IsFractionRing.isAlgebraic_iff ℤ ℚ ↥(modularFunctionFieldFull p)).mp h)
  have hFD := ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull p
  haveI := hFD
  have hsep : Algebra.IsSeparable
      ↥(IntermediateField.adjoin ℚ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)))
      ↥(modularFunctionFieldFull p) := inferInstance
  have hG5 := AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf ℤ ℚ
    ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) htj hFD hsep

  haveI hflat : AlgebraicGeometry.Flat (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
    AlgebraicCurve.TwoChartIntegralModel.flat_toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) (algebraMap ℤ ↥(modularFunctionFieldFull p)).injective_int
  have hFT := ModularCurve.IgusaScheme.finiteType_int_chartAlgFin_and_chartAlgInf p
  haveI := hFT.1
  haveI := hFT.2
  haveI hlofp : AlgebraicGeometry.LocallyOfFinitePresentation (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
    AlgebraicCurve.TwoChartIntegralModel.locallyOfFinitePresentation_toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)

  obtain ⟨φinf, hφinf⟩ := ModularCurve.IgusaScheme.exists_algHom_int_chartAlgInf_eq_coeff_zero p

  let εinf : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
    ⟨Spec.map (CommRingCat.ofHom φinf.toRingHom) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p), by
      rw [Category.assoc, AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase, ← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext1
      exact Subsingleton.elim _ _⟩
  have hεinf : Nonempty (NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) := ⟨εinf⟩

  have hC4ring : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits → (p : ℤ) ∣ φinf a := by
    exact (ModularCurve.DRModel.dvd_coeffZero_of_mem_nonunits_and_exists_not_dvd_of_prime p jp hjp W₀ W₁ hp₀ hp₁ hneW hgen hcomplete ht
      φinf hφinf).1

  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hℓp : ¬ 2 ∣ p := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp h
    omega
  have dataAll : ∀ (d : ℕ) [NeZero d], d ∣ p → ModularPolynomialData d :=
    fun d _ _ => Classical.choice (ModularCurve.nonempty_modularPolynomialData d)
  have htrans : Transcendental (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p) := by
    simpa [ModularCurve.CharPModel.jBar] using ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) p
  haveI : Fact (ModularCurve.CharPModel.jBar p ≠ 0) :=
    ⟨fun h => htrans (by rw [h]; exact isAlgebraic_zero)⟩
  haveI : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p)))
      (modularFunctionFieldBar p) :=
    ModularCurve.CharPModel.finiteDimensional_adjoin_jBar p dataAll
  haveI : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p)))
      (modularFunctionFieldBar p) := by
    have h : IntermediateField.adjoin (AlgebraicClosure ℚ) ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p)) =
        IntermediateField.adjoin (AlgebraicClosure ℚ) ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p)) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self _ _)
      · rw [IntermediateField.adjoin_simple_le_iff]
        simpa using inv_mem (IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) ((ModularCurve.CharPModel.jBar p)⁻¹))
    rw [h]; infer_instance
  obtain ⟨⟨eFin, hFin⟩, ⟨eInf, hInf⟩⟩ := ModularCurve.IgusaScheme.exists_algEquiv_tensor_chartAlg_chartRing p 2
  have htinv₀ : Transcendental ℚ ((IgusaScheme.jFull p))⁻¹ := fun halg => htjℚ (by have h := halg.inv; rwa [inv_inv] at h)
  haveI hfd_inv₀ : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({(IgusaScheme.jFull p)⁻¹} : Set ↥(modularFunctionFieldFull p))) ↥(modularFunctionFieldFull p) :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental (IgusaScheme.jFull p) htinv₀
  obtain ⟨eFin₀, hFin₀'⟩ := ModularCurve.IgusaScheme.exists_algEquiv_rat_tensor_chartAlg_chartRing p 2
    ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))
  obtain ⟨eInf₀, hInf₀'⟩ := ModularCurve.IgusaScheme.exists_algEquiv_rat_tensor_chartAlg_chartRing p 2
    ({(IgusaScheme.jFull p)⁻¹} : Set ↥(modularFunctionFieldFull p))
  have hFin₀ : ∀ b : ModularCurve.IgusaScheme.chartAlgFin p 2,
      ((eFin₀ (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)))) : ↥(modularFunctionFieldFull p))
        = (b : ↥(modularFunctionFieldFull p)) := fun b => by rw [hFin₀' 1 b, one_smul]
  have hInf₀ : ∀ b : ModularCurve.IgusaScheme.chartAlgInf p 2,
      ((eInf₀ (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(IgusaScheme.jFull p)⁻¹} : Set ↥(modularFunctionFieldFull p)))) : ↥(modularFunctionFieldFull p))
        = (b : ↥(modularFunctionFieldFull p)) := fun b => by rw [hInf₀' 1 b, one_smul]
  obtain ⟨eηI, hisoI, heηI, hpinFinη, hpinInfη, hgalI, e₀I, hiso₀I, he₀I, hpinFin₀, hpinInf₀, hcompatI⟩ :=
    ModularCurve.IgusaScheme.exists_genericFibreIso_chartPin_galoisCompat_and_ratPlaceCompat
      p 2 hℓp htrans eFin hFin eInf hInf htjℚ eFin₀ hFin₀ eInf₀ hInf₀
  haveI := hisoI
  haveI := hiso₀I

  obtain ⟨v, hv, hI, hvFin, hvInf⟩ :=
    ModularCurve.IgusaScheme.exists_isPullback_twoChartIntegralModel_int_and_iso_pullback_and_iotaFin_comp_eq p 2
  obtain ⟨Iη, hIη_snd, hIη_fst⟩ := hI (AlgebraicClosure ℚ)
  obtain ⟨I₀, hI₀_snd, hI₀_fst⟩ := hI ℚ

  let θr : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+*
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p))) :=
    (eFin.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt 2)) (A := (AlgebraicClosure ℚ))
        (B := ↥(ModularCurve.IgusaScheme.chartAlgFin p 2))).toRingHom).comp
      (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange ℤ ↥(modularFunctionFieldFull p) ↥(GaloisRep.ratLocalizedAt 2) ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)))
  have hθr : ∀ a, ((θr a : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
      ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p)))) : modularFunctionFieldBar p) =
      ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull p)).2⟩ := by
    intro a
    exact hFin (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange ℤ ↥(modularFunctionFieldFull p) ↥(GaloisRep.ratLocalizedAt 2) ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)) a)
  let θ : CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⟶
      CommRingCat.of ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p))) :=
    CommRingCat.ofHom θr
  have hfac : AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p) ≫ (eηI ≫ Iη.hom) ≫
        pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) _ =
      Spec.map θ ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) := by
    rw [Category.assoc, hIη_fst, reassoc_of% hpinFinη, hvFin]
    exact (Spec.map_comp_assoc
      (CommRingCat.ofHom (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange ℤ ↥(modularFunctionFieldFull p) ↥(GaloisRep.ratLocalizedAt 2) ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))))
      (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt 2)) (A := (AlgebraicClosure ℚ))
            (B := ↥(ModularCurve.IgusaScheme.chartAlgFin p 2))).toRingHom)) _).symm

  have hUne : ∀ ξ : ↥(AlgebraicCurve.CurveModel.X₀ (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p)),
      (AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p)).base ξ ∈
        ((eηI ≫ Iη.hom) ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) _) ⁻¹ᵁ
          ((AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by
    intro ξ
    have e := congrArg (fun g => g.base ξ) hfac
    exact ⟨(Spec.map θ).base ξ, trivial, e.symm⟩

  have hspecQ : ∀ f : AlgebraicGeometry.Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ AlgebraicGeometry.Spec (CommRingCat.of ℚ),
      f = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) := fun f => by
    rw [← AlgebraicGeometry.Spec.map_preimage f]
    congr 1
    ext1
    exact Subsingleton.elim _ _
  have hgfix : ∀ g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
      (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt 2) (AlgebraicClosure ℚ)) = algebraMap ↥(GaloisRep.ratLocalizedAt 2) (AlgebraicClosure ℚ) := fun g => by
    ext r
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt 2) ℚ (AlgebraicClosure ℚ) r]
    exact g.commutes _

  have hbaseI : ∀ (x : {q : AlgebraicGeometry.Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
        (CurveModel.ofGenerator (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p) htrans).C //
        q ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p) htrans).toBase = 𝟙 _}),
      (x.1 ≫ eηI ≫ CategoryTheory.Limits.pullback.fst _ _) ≫ IgusaScheme.igusaTo p 2
        = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt 2) (AlgebraicClosure ℚ))) := fun x => by
    rw [Category.assoc, Category.assoc, CategoryTheory.Limits.pullback.condition, ← Category.assoc eηI, heηI,
      reassoc_of% x.2]

  haveI : IrreducibleSpace ↥(DRModel p) := by
    haveI := AlgebraicCurve.TwoChartIntegralModel.isIntegral ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
    infer_instance
  obtain ⟨W, hyW, hWsm⟩ :=
    AlgebraicGeometry.exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
      (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_charZero p ℚ)
      ((DRModel.sectionFibre εinf (algebraMap ℤ ℚ) ≫ pullback.fst _ _).base (IsLocalRing.closedPoint ℚ))
      ⟨(DRModel.sectionFibre εinf (algebraMap ℤ ℚ)).base (IsLocalRing.closedPoint ℚ), rfl⟩
  haveI := hWsm

  let G3M : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (hdec : DecidableEq κ), CurveModel κ (RatFunc κ) :=
    fun κ _ _ _ hdec => (@ModularCurve.DRModel.exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators p _ _ hp jp hjp W₀ W₁ hp₀ hp₁ hneW hgen hcomplete ht hres₀ hres₁ κ _ _ _ hdec).choose
  let G3cInf : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (hdec : DecidableEq κ),
      (G3M κ hdec).C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) :=
    fun κ _ _ _ hdec => (@ModularCurve.DRModel.exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators p _ _ hp jp hjp W₀ W₁ hp₀ hp₁ hneW hgen hcomplete ht hres₀ hres₁ κ _ _ _ hdec).choose_spec.choose
  let G3cZero : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (hdec : DecidableEq κ),
      (G3M κ hdec).C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) :=
    fun κ _ _ _ hdec => (@ModularCurve.DRModel.exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators p _ _ hp jp hjp W₀ W₁ hp₀ hp₁ hneW hgen hcomplete ht hres₀ hres₁ κ _ _ _ hdec).choose_spec.choose_spec.choose
  have G3spec : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (hdec : DecidableEq κ),
      (G3cInf κ hdec) ≫ pullback.snd _ _ = (G3M κ hdec).toBase ∧ (G3cZero κ hdec) ≫ pullback.snd _ _ = (G3M κ hdec).toBase ∧
      IsClosedImmersion (G3cInf κ hdec) ∧ IsClosedImmersion (G3cZero κ hdec) ∧
      (∀ x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
      x ∈ Set.range (G3cInf κ hdec).base ∨ x ∈ Set.range (G3cZero κ hdec).base) ∧
      Set.range (G3cInf κ hdec).base ≠ Set.range (G3cZero κ hdec).base ∧
      IsReduced (pullback (G3cInf κ hdec) (G3cZero κ hdec)) ∧
      Nat.card ↥(pullback (G3cInf κ hdec) (G3cZero κ hdec)) = Nat.card ↥(ssJSet p κ) ∧

      (∀ (ψ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ)
      (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (DRModel.toBase p)),
      ε.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) →
      ((∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits → (p : ℤ) ∣ ψ a) →
      Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base ⊆ Set.range (G3cInf κ hdec).base) ∧
      ((∀ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits → (p : ℤ) ∣ ψ a) →
      Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base ⊆ Set.range (G3cZero κ hdec).base) ∧

      ((∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      (a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits ∧ ¬ (p : ℤ) ∣ ψ a) →
      Disjoint (Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base) (Set.range (G3cZero κ hdec).base)) ∧
      ((∃ a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      (a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits ∧ ¬ (p : ℤ) ∣ ψ a) →
      Disjoint (Set.range (DRModel.sectionFibre ε (algebraMap ℤ κ)).base) (Set.range (G3cInf κ hdec).base))) :=
    fun κ _ _ _ hdec => (@ModularCurve.DRModel.exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators p _ _ hp jp hjp W₀ W₁ hp₀ hp₁ hneW hgen hcomplete ht hres₀ hres₁ κ _ _ _ hdec).choose_spec.choose_spec.choose_spec
  have hsec : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ],
      Set.range (DRModel.sectionFibre εinf (algebraMap ℤ κ)).base ⊆ Set.range (G3cInf κ (Classical.decEq κ)).base :=
    fun κ _ _ _ => ((G3spec κ (Classical.decEq κ)).2.2.2.2.2.2.2.2 φinf εinf rfl).1 hC4ring

  have hN12c_gen : ∀ {k : Type} [Field k]
      (hsm : SmoothOfRelativeDimension 1 (pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))),
      εinf.1.base ((Spec.map (CommRingCat.ofHom (algebraMap ℤ k))).base (IsLocalRing.closedPoint k))
        ∈ ((DRModel.toBase p).smoothLocus : Set ↥(DRModel p)) := by
    intro k _ hsm
    obtain ⟨W, hyW, hWsm⟩ :=
      AlgebraicGeometry.exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
        (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) hsm
        (εinf.1.base ((Spec.map (CommRingCat.ofHom (algebraMap ℤ k))).base (IsLocalRing.closedPoint k)))
        ⟨(DRModel.sectionFibre εinf (algebraMap ℤ k)).base (IsLocalRing.closedPoint k), by
          have h1 : DRModel.sectionFibre εinf (algebraMap ℤ k) ≫ pullback.fst _ _ =
              Spec.map (CommRingCat.ofHom (algebraMap ℤ k)) ≫ εinf.1 := pullback.lift_fst _ _ _
          change (DRModel.sectionFibre εinf (algebraMap ℤ k) ≫ pullback.fst _ _).base (IsLocalRing.closedPoint k) = _
          rw [h1]
          rfl⟩
    haveI := hWsm
    exact (DRModel.toBase p).le_smoothLocus_of_smoothOfRelativeDimension 1 W hyW
  have hN12c : Set.range εinf.1.base ⊆ ((DRModel.toBase p).smoothLocus : Set ↥(DRModel p)) := by
    rintro _ ⟨𝔭, rfl⟩
    by_cases h𝔭p : 𝔭.asIdeal = Ideal.span {(p : ℤ)}
    ·

      let κ : Type := AlgebraicClosure (ZMod p)
      haveI : CharP κ p := charP_of_injective_algebraMap (algebraMap (ZMod p) κ).injective p
      have hκred : IsReduced (pullback (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) :=
        ModularCurve.DRModel.isReduced_pullback_toBase_of_charP p κ
      have hC4ring' := (ModularCurve.DRModel.dvd_coeffZero_of_mem_nonunits_and_exists_not_dvd_of_prime p jp hjp W₀ W₁ hp₀ hp₁ hneW
        hgen hcomplete ht φinf hφinf).2
      have hdisj := ((G3spec κ (Classical.decEq κ)).2.2.2.2.2.2.2.2 φinf εinf rfl).2.2.1 hC4ring'
      have hy : (DRModel.sectionFibre εinf (algebraMap ℤ κ)).base (IsLocalRing.closedPoint κ) ∉
          Set.range (G3cZero κ (Classical.decEq κ)).base :=
        Set.disjoint_left.mp hdisj ⟨IsLocalRing.closedPoint κ, rfl⟩
      have hmem := @AlgebraicGeometry.mem_smoothLocus_of_not_mem_range_of_isClosedImmersion ℤ _ (DRModel p)
        (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) hflat hlofp κ _ (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) hκred
        (G3M κ (Classical.decEq κ)).C (G3M κ (Classical.decEq κ)).C (G3M κ (Classical.decEq κ)).toBase inferInstance
        (G3cInf κ (Classical.decEq κ)) (G3cZero κ (Classical.decEq κ))
        (G3spec κ (Classical.decEq κ)).2.2.1 (G3spec κ (Classical.decEq κ)).2.2.2.1
        (G3spec κ (Classical.decEq κ)).1 (G3spec κ (Classical.decEq κ)).2.2.2.2.1 _ hy
      have h1 : DRModel.sectionFibre εinf (algebraMap ℤ κ) ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)) ≫ εinf.1 := pullback.lift_fst _ _ _
      have h2 : (pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base
            ((DRModel.sectionFibre εinf (algebraMap ℤ κ)).base (IsLocalRing.closedPoint κ)) =
          εinf.1.base ((Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))).base (IsLocalRing.closedPoint κ)) := by
        change (DRModel.sectionFibre εinf (algebraMap ℤ κ) ≫ pullback.fst _ _).base (IsLocalRing.closedPoint κ) = _
        rw [h1]
        rfl
      have hpt : (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))).base (IsLocalRing.closedPoint κ) = 𝔭 := by
        apply PrimeSpectrum.ext
        change Ideal.comap (algebraMap ℤ κ) (IsLocalRing.closedPoint κ).asIdeal = 𝔭.asIdeal
        rw [h𝔭p, show (IsLocalRing.closedPoint κ).asIdeal = ⊥ from Ideal.eq_bot_of_prime _]
        change RingHom.ker (algebraMap ℤ κ) = Ideal.span {(p : ℤ)}
        have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
        have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
          ((Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp Fact.out)).isMaximal
            (by rwa [Ne, Ideal.span_singleton_eq_bot])
        refine (hmax.eq_of_le (RingHom.ker_ne_top _) ?_).symm
        rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast]
        exact CharP.cast_eq_zero κ p
      rw [← hpt, ← h2]
      exact hmem
    · by_cases h0 : 𝔭.asIdeal = ⊥
      ·
        have hpt : (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))).base (IsLocalRing.closedPoint ℚ) = 𝔭 := by
          apply PrimeSpectrum.ext
          change Ideal.comap (algebraMap ℤ ℚ) (IsLocalRing.closedPoint ℚ).asIdeal = 𝔭.asIdeal
          rw [h0, show (IsLocalRing.closedPoint ℚ).asIdeal = ⊥ from Ideal.eq_bot_of_prime _]
          exact (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ ℚ).injective_int
        rw [← hpt]
        exact hN12c_gen (ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_charZero p ℚ)
      ·
        set g := Submodule.IsPrincipal.generator 𝔭.asIdeal with hg
        have hspan : Ideal.span {g} = 𝔭.asIdeal := Ideal.span_singleton_generator _
        have hg0 : g ≠ 0 := fun h => h0 (by rw [← hspan, h, Ideal.span_singleton_eq_bot])
        have hgprime : Prime g := (Ideal.span_singleton_prime hg0).mp (hspan ▸ 𝔭.isPrime)
        set ℓ := g.natAbs with hℓ
        have hℓprime : ℓ.Prime := Int.prime_iff_natAbs_prime.mp hgprime
        haveI : Fact ℓ.Prime := ⟨hℓprime⟩
        have hspanℓ : 𝔭.asIdeal = Ideal.span {(ℓ : ℤ)} := by rw [← hspan, hℓ, Int.span_natAbs]
        have hℓp' : ¬ ℓ ∣ p := by
          intro hdvd
          have : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓprime Fact.out).mp hdvd
          exact h𝔭p (by rw [hspanℓ, this])
        have hpt : (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod ℓ)))).base (IsLocalRing.closedPoint (ZMod ℓ)) = 𝔭 := by
          apply PrimeSpectrum.ext
          change Ideal.comap (algebraMap ℤ (ZMod ℓ)) (IsLocalRing.closedPoint (ZMod ℓ)).asIdeal = 𝔭.asIdeal
          rw [hspanℓ, show (IsLocalRing.closedPoint (ZMod ℓ)).asIdeal = ⊥ from Ideal.eq_bot_of_prime _]
          exact ZMod.ker_intCastRingHom ℓ
        rw [← hpt]
        exact hN12c_gen (ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_charP p ℓ hℓp' (ZMod ℓ))

  obtain ⟨w, hw_over, hw_invol, ψ₀, hwε, hψ₀W₁, hψ₀W₀⟩ :=
    ModularCurve.DRModel.exists_iso_comp_toBase_eq_and_hom_comp_hom_eq_id_and_exists_algHom_comp_hom_eq
      p hp jp hjp W₀ W₁ hp₀ hp₁ hneW hgen hcomplete ht hres₀ hres₁ φinf hφinf

  let εzero : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
    ⟨εinf.1 ≫ w.hom, by rw [Category.assoc]; exact (congrArg (εinf.1 ≫ ·) hw_over).trans εinf.2⟩
  have hεzero : εzero.1 = Spec.map (CommRingCat.ofHom ψ₀.toRingHom) ≫
      AlgebraicCurve.TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) := hwε
  have hsec0 : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ],
      Set.range (DRModel.sectionFibre εzero (algebraMap ℤ κ)).base ⊆ Set.range (G3cZero κ (Classical.decEq κ)).base :=
    fun κ _ _ _ => ((G3spec κ (Classical.decEq κ)).2.2.2.2.2.2.2.2 ψ₀ εzero hεzero).2.1 hψ₀W₁

  have hN12c0 : Set.range εzero.1.base ⊆ ((DRModel.toBase p).smoothLocus : Set ↥(DRModel p)) :=
    (DRModel.toBase p).range_comp_subset_smoothLocus_of_iso_over w hw_over εinf.1 hN12c
  refine ⟨⟨
    {
      isProper := ModularCurve.IgusaScheme.isProper_toBase_int p
      flat := hflat
      isIntegral := AlgebraicCurve.TwoChartIntegralModel.isIntegral ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
      normal := fun U hU =>
        AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_sections_of_isAffineOpen ℤ ↥(modularFunctionFieldFull p)
          (IgusaScheme.jFull p) U hU
      M₀ := CurveModel.ofGenerator ℚ (IgusaScheme.jFull p) htjℚ
      e₀ := e₀I ≫ I₀.hom
      e₀_iso := inferInstance
      he₀ := by
        change (e₀I ≫ I₀.hom) ≫ pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) _ = _
        rw [Category.assoc, hI₀_snd]; exact he₀I
      Mη := CurveModel.ofGenerator (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p) htrans
      eη := eηI ≫ Iη.hom
      eη_iso := inferInstance
      heη := by
        change (eηI ≫ Iη.hom) ≫ pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) _ = _
        rw [Category.assoc, hIη_snd]; exact heηI
      hgal := by

        intro g x x' hx
        apply hgalI g x x'
        apply hv.hom_ext
        · simp only [Category.assoc] at hx ⊢
          rw [← hIη_fst]
          exact hx
        · rw [hbaseI x', Category.assoc, hbaseI x, ← AlgebraicGeometry.Spec.map_comp]
          change _ = AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt 2) (AlgebraicClosure ℚ))))
          rw [hgfix g]
      hcompat := by

        intro x y x₀ hy hx₀
        refine hcompatI x (y ≫ I₀.inv) x₀ ?_ ?_
        · apply hv.hom_ext
          · rw [Category.assoc, Category.assoc, ← hI₀_fst, ← Category.assoc I₀.inv, I₀.inv_hom_id, Category.id_comp,
              Category.assoc, Category.assoc, ← hIη_fst]
            simp only [Category.assoc] at hy
            exact hy
          · rw [hbaseI x, Category.assoc, Category.assoc, CategoryTheory.Limits.pullback.condition,
              ← Category.assoc I₀.inv, ← Category.assoc y]
            have h1 : I₀.inv ≫ CategoryTheory.Limits.pullback.snd _ _ = CategoryTheory.Limits.pullback.snd _ _ := by
              rw [← hI₀_snd, ← Category.assoc, I₀.inv_hom_id, Category.id_comp]
            rw [Category.assoc y, h1, ← Category.assoc y,
              hspecQ (y ≫ CategoryTheory.Limits.pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
                (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
              ← AlgebraicGeometry.Spec.map_comp]
            change AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt 2) ℚ))) = _
            rw [← IsScalarTower.algebraMap_eq ↥(GaloisRep.ratLocalizedAt 2) ℚ (AlgebraicClosure ℚ)]
        · have h2 : y ≫ CategoryTheory.inv (e₀I ≫ I₀.hom) = (y ≫ I₀.inv) ≫ CategoryTheory.inv e₀I := by
            rw [CategoryTheory.IsIso.inv_comp, CategoryTheory.IsIso.Iso.inv_hom, Category.assoc]
          rw [← h2]
          exact hx₀
      εinf := εinf
      εzero := εzero
      smoothLocus := (DRModel.toBase p).smoothLocus
      smoothLocus_relDim := (DRModel.toBase p).smoothOfRelativeDimension_smoothLocus_ι_comp 1 W ⟨_, hyW⟩
      smoothLocus_maximal := fun U hU => by haveI := hU; exact (DRModel.toBase p).le_smoothLocus_of_smooth U
      εinf_mem_smoothLocus := hN12c
      εzero_mem_smoothLocus := hN12c0
      smooth_away := ModularCurve.IgusaScheme.smooth_pullback_snd_toBase_int_localizationAway p
      pFibre_reduced := ModularCurve.DRModel.isReduced_pFibre p hp
      ratModel := fun κ _ _ _ => G3M κ (Classical.decEq κ)
      compInf := fun κ _ _ _ => G3cInf κ (Classical.decEq κ)
      compZero := fun κ _ _ _ => G3cZero κ (Classical.decEq κ)
      compInf_over := fun κ _ _ _ => (G3spec κ (Classical.decEq κ)).1
      compZero_over := fun κ _ _ _ => (G3spec κ (Classical.decEq κ)).2.1
      compInf_isClosedImmersion := fun κ _ _ _ => (G3spec κ (Classical.decEq κ)).2.2.1
      compZero_isClosedImmersion := fun κ _ _ _ => (G3spec κ (Classical.decEq κ)).2.2.2.1
      comp_jointly_surjective := fun κ _ _ _ => (G3spec κ (Classical.decEq κ)).2.2.2.2.1
      range_compInf_ne := fun κ _ _ _ => (G3spec κ (Classical.decEq κ)).2.2.2.2.2.1
      crossing_reduced := fun κ _ _ _ => (G3spec κ (Classical.decEq κ)).2.2.2.2.2.2.1
      crossing_card := fun κ _ _ _ hdec => by

        obtain rfl : hdec = Classical.decEq κ := Subsingleton.elim _ _
        exact (G3spec κ (Classical.decEq κ)).2.2.2.2.2.2.2.1
      εinf_mem_compInf := hsec
      εzero_mem_compZero := hsec0
      w := w
      w_over := hw_over
      w_invol := hw_invol
      w_sections := rfl
      chartFin_finite := hG5.1
      chartInf_finite := hG5.2
    }, ?_, ?_⟩⟩
  ·
    exact ⟨⟨(AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p)).base (Classical.arbitrary _),
      hUne _⟩⟩
  ·
    intro a
    haveI : Nonempty ((((eηI ≫ Iη.hom) ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) _) ⁻¹ᵁ
        ((AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))) :=
      ⟨⟨_, hUne (Classical.arbitrary _)⟩⟩
    have key := AlgebraicCurve.CurveModel.ofGenerator_ffEquiv_symm_germToFunctionField (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p)
      htrans ((eηI ≫ Iη.hom) ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) _)
      (AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) θ hfac a
    refine (congrArg (fun y : modularFunctionFieldBar p => (y : LaurentSeries (AlgebraicClosure ℚ))) key).trans ?_
    simp only [θ, CommRingCat.hom_ofHom, hθr]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    ∃ (𝔛 : DRModelPackage p) (_ : Nonempty (Scheme.Opens.toScheme
        ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
          ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))),
      ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((𝔛.Mη.ffEquiv.symm
          (𝔛.Mη.C.germToFunctionField
            ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
            (((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).app
                ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of
                  ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))
          : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) := by
  obtain ⟨c⟩ := ModularCurve.LEG1aCert.nonempty p hp
  exact ⟨c.pkg, c.hne, c.hMη⟩

end S_ModularCurve_exists_dRModelPackage_ffPin
end P2MW
export P2MW.S_ModularCurve_exists_dRModelPackage_ffPin (solution)
