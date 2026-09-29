-- Prove2me | solution 1 for ModularCurve.IgusaScheme.isProper_and_smooth_and_geometricallyIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/a627aa1d-96c2-53c4-8a2f-f72fc865e89f

import Definitions.Def_ModularCurve_IgusaScheme
import Theorems.Thm_ModularCurve_IgusaScheme_isProper_igusaTo
import Theorems.Thm_ModularCurve_IgusaScheme_geometricallyIntegral_igusaTo
import Theorems.Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_igusaTo_of_smooth_fiber
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_IgusaScheme_flat_igusaTo
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegral
import Theorems.Thm_AlgebraicGeometry_Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Theorems.Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_residue
import Theorems.Thm_ModularCurve_IgusaScheme_exists_curveModel_genericFibre_iso_and_galoisCompat
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral.ModularCurve.IgusaScheme"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme IgusaScheme.isIntegral"
p2m_open "ModularCurve"

namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "chartAlgFin chartAlgInf XFin XInf ιFin ιInf igusaTo ιFin_igusaTo ιInf_igusaTo mem_range_ιFin_or_mem_range_ιInf isProper_igusaTo geometricallyIntegral_igusaTo smoothOfRelativeDimension_one_igusaTo_of_smooth_fiber finiteType_chartAlgFin_and_chartAlgInf flat_igusaTo isIntegral smoothOfRelativeDimension_one_pullback_residue exists_curveModel_genericFibre_iso_and_galoisCompat"
p2m_open "ModularCurve.IgusaScheme"

namespace Curve

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)

set_option quotPrecheck false in
local notation "X₀" => ModularCurve.IgusaScheme N ℓ

scoped instance isNoetherianRing_base : IsNoetherianRing ℤℓ :=
  haveI := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ
  inferInstance

scoped instance finiteType_chartAlgFin : Algebra.FiniteType ℤℓ (chartAlgFin N ℓ) :=
  (finiteType_chartAlgFin_and_chartAlgInf N ℓ).1

scoped instance finiteType_chartAlgInf : Algebra.FiniteType ℤℓ (chartAlgInf N ℓ) :=
  (finiteType_chartAlgFin_and_chartAlgInf N ℓ).2

def twoChartCover : (X₀).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b => cond b (XFin N ℓ) (XInf N ℓ))
    (fun b => match b with
      | true => ιFin N ℓ
      | false => ιInf N ℓ)
    (fun x => by
      rcases mem_range_ιFin_or_mem_range_ιInf N ℓ x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, y, hy⟩)
    (fun b => match b with
      | true => inferInstanceAs (IsOpenImmersion (ιFin N ℓ))
      | false => inferInstanceAs (IsOpenImmersion (ιInf N ℓ)))

scoped instance locallyOfFinitePresentation_igusaTo : LocallyOfFinitePresentation (igusaTo N ℓ) := by
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation)
    (twoChartCover N ℓ) ?_
  rintro (_ | _)
  · change LocallyOfFinitePresentation (ιInf N ℓ ≫ igusaTo N ℓ)
    rw [ιInf_igusaTo, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mpr inferInstance)
  · change LocallyOfFinitePresentation (ιFin N ℓ ≫ igusaTo N ℓ)
    rw [ιFin_igusaTo, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mpr inferInstance)

omit [Fact ℓ.Prime] in

theorem ringHom_ratLocalizedAt_ext {A : Type*} [Ring A] (f g : ℤℓ →+* A) : f = g := by
  refine RingHom.ext fun x => ?_
  obtain ⟨q, hq⟩ := x
  have hden0 : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz

  have hmem : (q.den : ℚ)⁻¹ ∈ GaloisRep.ratLocalizedAt ℓ := by
    show ((q.den : ℚ)⁻¹).den.Coprime ℓ
    rw [Rat.inv_natCast_den, if_neg q.den_nz]
    exact hq
  set dinv : ℤℓ := ⟨(q.den : ℚ)⁻¹, hmem⟩ with hdinv
  have hx : (⟨q, hq⟩ : ℤℓ) = (q.num : ℤℓ) * dinv := by
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_intCast, hdinv]
    rw [← div_eq_mul_inv, Rat.num_div_den]
  have hd1 : (q.den : ℤℓ) * dinv = 1 := by
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one, hdinv]
    exact mul_inv_cancel₀ hden0
  have hd2 : dinv * (q.den : ℤℓ) = 1 := by rw [mul_comm]; exact hd1
  have hf : f dinv = g dinv := by

    have h1 : (q.den : A) * f dinv = 1 := by rw [← map_natCast f, ← map_mul, hd1, map_one]
    have h2 : g dinv * (q.den : A) = 1 := by rw [← map_natCast g, ← map_mul, hd2, map_one]
    exact (left_inv_eq_right_inv h2 h1).symm
  rw [hx, map_mul, map_mul, map_intCast, map_intCast, hf]

scoped instance isLocalization_away_rat : IsLocalization.Away ((ℓ : ℕ) : ℤℓ) ℚ := by
  have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    refine isUnit_iff_ne_zero.mpr ?_
    show (((ℓ : ℤℓ) ^ n : ℤℓ) : ℚ) ≠ 0
    rw [Subring.coe_pow, Subring.coe_natCast]
    exact pow_ne_zero _ hℓ
  · intro z
    obtain ⟨k, m, hm, hden⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd z.den_nz ℓ (Fact.out : ℓ.Prime).ne_one
    have hm0 : m ≠ 0 := by rintro rfl; exact z.den_nz (by simpa using hden)
    have hcop : m.Coprime ℓ :=
      (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)

    have hmem : ((z.num : ℚ) / m) ∈ GaloisRep.ratLocalizedAt ℓ := by
      show (((z.num : ℚ) / m)).den.Coprime ℓ
      have ha : ((z.num : ℚ) / m) = Rat.divInt z.num (m : ℤ) := by
        rw [Rat.divInt_eq_div, Int.cast_natCast]
      have hdvd : (((z.num : ℚ) / m).den : ℤ) ∣ (m : ℤ) := by
        rw [ha]
        exact Rat.den_dvd z.num m
      have hdvd' : ((z.num : ℚ) / m).den ∣ m := by exact_mod_cast hdvd
      exact Nat.Coprime.coprime_dvd_left hdvd' hcop
    refine ⟨(⟨(z.num : ℚ) / m, hmem⟩, ⟨(ℓ : ℤℓ) ^ k, k, rfl⟩), ?_⟩
    show z * ((((ℓ : ℤℓ) ^ k : ℤℓ) : ℚ)) = (z.num : ℚ) / m
    rw [Subring.coe_pow, Subring.coe_natCast]
    have hden' : (z.den : ℚ) = (ℓ : ℚ) ^ k * m := by exact_mod_cast hden
    calc z * (ℓ : ℚ) ^ k = (z.num : ℚ) / (z.den : ℚ) * (ℓ : ℚ) ^ k := by rw [Rat.num_div_den]
      _ = (z.num : ℚ) / m / (ℓ : ℚ) ^ k * (ℓ : ℚ) ^ k := by
          rw [hden', mul_comm ((ℓ : ℚ) ^ k), ← div_div]
      _ = (z.num : ℚ) / m := div_mul_cancel₀ _ (pow_ne_zero k hℓ)
  · intro x y h
    exact ⟨1, by simpa using Subtype.val_injective h⟩

scoped instance isOpenImmersion_specMap_rat :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap ℤℓ ℚ))) :=
  IsOpenImmersion.of_isLocalization ((ℓ : ℕ) : ℤℓ)

omit [NeZero N] [Fact ℓ.Prime] in

theorem fromSpecResidueField_spec_eq (R : CommRingCat.{0}) (y : Spec R) :
    (Spec R).fromSpecResidueField y =
      Spec.map (CommRingCat.ofHom (algebraMap R y.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso R y).inv) := by
  rw [Spec.map_comp, Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]

omit [NeZero N] [Fact ℓ.Prime] in

theorem smooth_pullback_snd_comp {X S T T' : Scheme.{0}} (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ T)
    [Smooth (pullback.snd f g)] : Smooth (pullback.snd f (h ≫ g)) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd f g h]
  infer_instance

omit [NeZero N] [Fact ℓ.Prime] in

theorem smoothOfRelativeDimension_pullback_snd_comp (n : ℕ) {X S T T' : Scheme.{0}}
    (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ T)
    [SmoothOfRelativeDimension n (pullback.snd f g)] :
    SmoothOfRelativeDimension n (pullback.snd f (h ≫ g)) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd f g h]
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  have : SmoothOfRelativeDimension n (pullback.snd (pullback.snd f g) h) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ inferInstance
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension n) _ _).mpr this

omit [NeZero N] [Fact ℓ.Prime] in

theorem of_pullback_snd_comp_of_descendsAlong {P Q : MorphismProperty Scheme.{0}}
    [P.RespectsIso] (hPQ : P.DescendsAlong Q)
    {X S T T' : Scheme.{0}} (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ T) (hQ : Q h)
    (hP : P (pullback.snd f (h ≫ g))) : P (pullback.snd f g) := by
  haveI := hPQ
  have hP' : P (pullback.snd (pullback.snd f g) h) := by
    rw [← pullbackLeftPullbackSndIso_hom_snd f g h]
    exact (MorphismProperty.cancel_left_of_respectsIso P _ _).mpr hP
  exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := P) (Q := Q) hQ hP'

omit [NeZero N] [Fact ℓ.Prime] in

theorem surjective_flat_quasiCompact_specMap_of_field (K L : Type) [Field K] [Field L]
    [Algebra K L] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  refine ⟨⟨⟨fun x => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩, ?_⟩, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
  infer_instance

theorem smoothOfRelativeDimension_one_pullback_rat (hℓN : ¬ ℓ ∣ N) :
    SmoothOfRelativeDimension 1
      (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ℤℓ ℚ)))) := by
  obtain ⟨Mη, eη, hiso, hcomp, -⟩ := exists_curveModel_genericFibre_iso_and_galoisCompat N ℓ hℓN
  haveI := hiso

  have h1 : SmoothOfRelativeDimension 1 (pullback.snd (igusaTo N ℓ)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (AlgebraicClosure ℚ))))) := by
    rw [(IsIso.eq_inv_comp eη).mpr hcomp]
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) _ _).mpr
      inferInstance

  have hbase : Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (AlgebraicClosure ℚ))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℤℓ ℚ)) := by
    rw [ringHom_ratLocalizedAt_ext ℓ (algebraMap ℤℓ (AlgebraicClosure ℚ))
      ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap ℤℓ ℚ)), CommRingCat.ofHom_comp,
      Spec.map_comp]
  rw [hbase] at h1
  exact of_pullback_snd_comp_of_descendsAlong
    (AlgebraicGeometry.SmoothOfRelativeDimension.descendsAlong_surjective_inf_flat_inf_quasiCompact 1)
    _ _ _ (surjective_flat_quasiCompact_specMap_of_field ℚ (AlgebraicClosure ℚ)) h1

theorem smooth_fiberToSpecResidueField (hℓN : ¬ ℓ ∣ N)
    (y : Spec (CommRingCat.of ℤℓ)) :
    Smooth ((igusaTo N ℓ).fiberToSpecResidueField y) := by

  set g : CommRingCat.of ℤℓ ⟶ (Spec (CommRingCat.of ℤℓ)).residueField y :=
    CommRingCat.ofHom (algebraMap ℤℓ y.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (CommRingCat.of ℤℓ) y).inv with hg
  change Smooth (pullback.snd (igusaTo N ℓ) ((Spec (CommRingCat.of ℤℓ)).fromSpecResidueField y))
  rw [fromSpecResidueField_spec_eq, ← hg]
  set K : Type := ↥((Spec (CommRingCat.of ℤℓ)).residueField y) with hK
  let ψ : ℤℓ →+* K := g.hom
  have hgψ : g = CommRingCat.ofHom ψ := (CommRingCat.ofHom_hom g).symm
  by_cases hchar : ((ℓ : ℕ) : K) = 0
  ·
    haveI : CharP K ℓ := (CharP.charP_iff_prime_eq_zero (Fact.out : ℓ.Prime)).mpr hchar
    let φ : ℤℓ →+* AlgebraicClosure K := (algebraMap K (AlgebraicClosure K)).comp ψ
    have hsp : Smooth (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom φ))) :=
      (smoothOfRelativeDimension_one_pullback_residue N ℓ hℓN (AlgebraicClosure K) φ).smooth
    have hφ : Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ Spec.map g := by
      rw [hgψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [hφ] at hsp
    exact of_pullback_snd_comp_of_descendsAlong
      AlgebraicGeometry.Smooth.descendsAlong_surjective_inf_flat_inf_quasiCompact
      _ _ _ (surjective_flat_quasiCompact_specMap_of_field K (AlgebraicClosure K)) hsp
  ·
    haveI : CharZero K := by
      obtain ⟨p, hp⟩ := CharP.exists K
      rcases CharP.char_is_prime_or_zero K p with hprime | rfl
      · exfalso
        have hp0 : (p : K) = 0 := CharP.cast_eq_zero K p
        by_cases hpl : p = ℓ
        · exact hchar (hpl ▸ hp0)
        · have hcop : p.Coprime ℓ := (Nat.coprime_primes hprime Fact.out).mpr hpl
          have hmem : (p : ℚ)⁻¹ ∈ GaloisRep.ratLocalizedAt ℓ := by
            show ((p : ℚ)⁻¹).den.Coprime ℓ
            rw [Rat.inv_natCast_den, if_neg hprime.ne_zero]
            exact hcop
          have h1 : (p : ℤℓ) * ⟨(p : ℚ)⁻¹, hmem⟩ = 1 := by
            apply Subtype.ext
            simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one]
            exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hprime.ne_zero)
          have h2 : ψ (p : ℤℓ) * ψ ⟨(p : ℚ)⁻¹, hmem⟩ = 1 := by rw [← map_mul, h1, map_one]
          rw [map_natCast, hp0, zero_mul] at h2
          exact zero_ne_one h2
      · exact CharP.charP_to_charZero K
    have hψ : ψ = (algebraMap ℚ K).comp (algebraMap ℤℓ ℚ) := ringHom_ratLocalizedAt_ext ℓ _ _
    have hg' : g = CommRingCat.ofHom (algebraMap ℤℓ ℚ) ≫ CommRingCat.ofHom (algebraMap ℚ K) := by
      rw [hgψ, hψ, CommRingCat.ofHom_comp]
    rw [hg', Spec.map_comp]
    haveI := (smoothOfRelativeDimension_one_pullback_rat N ℓ hℓN).smooth
    exact smooth_pullback_snd_comp _ _ _

def genericOpen : (X₀).Opens :=
  (igusaTo N ℓ) ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap ℤℓ ℚ))).opensRange

theorem genericOpen_nonempty (hℓN : ¬ ℓ ∣ N) :
    ((genericOpen N ℓ : (X₀).Opens) : Set X₀).Nonempty := by
  obtain ⟨Mη, eη, hiso, hcomp, -⟩ := exists_curveModel_genericFibre_iso_and_galoisCompat N ℓ hℓN
  obtain ⟨p⟩ : Nonempty Mη.C := inferInstance
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (AlgebraicClosure ℚ))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℤℓ ℚ)) := by
    rw [ringHom_ratLocalizedAt_ext ℓ (algebraMap ℤℓ (AlgebraicClosure ℚ))
      ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap ℤℓ ℚ)), CommRingCat.ofHom_comp,
      Spec.map_comp]
  have hsq : (eη ≫ pullback.fst (igusaTo N ℓ) _) ≫ igusaTo N ℓ =
      (eη ≫ pullback.snd (igusaTo N ℓ) _) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (AlgebraicClosure ℚ))) := by
    simp only [Category.assoc, pullback.condition]
  refine ⟨(eη ≫ pullback.fst (igusaTo N ℓ) _) p, ?_⟩
  change (igusaTo N ℓ) ((eη ≫ pullback.fst (igusaTo N ℓ) _) p) ∈
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap ℤℓ ℚ)))
  refine ⟨Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))
      ((eη ≫ pullback.snd (igusaTo N ℓ) _) p), ?_⟩
  have h1 := congrArg (fun φ => φ p) hsq
  have h2 := congrArg (fun φ => φ ((eη ≫ pullback.snd (igusaTo N ℓ) _) p)) hbase
  simp only [Scheme.Hom.comp_apply] at h1 h2 ⊢
  rw [h1, h2]

theorem smoothOfRelativeDimension_one_genericOpen (hℓN : ¬ ℓ ∣ N) :
    SmoothOfRelativeDimension 1 ((genericOpen N ℓ).ι ≫ igusaTo N ℓ) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap ℤℓ ℚ)) with hg
  have hrange : Set.range (genericOpen N ℓ).ι = Set.range (pullback.fst (igusaTo N ℓ) g) := by
    rw [Scheme.Opens.range_ι, IsOpenImmersion.range_pullbackFst]
    rfl
  have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac (genericOpen N ℓ).ι
    (pullback.fst (igusaTo N ℓ) g) hrange
  have heq : (genericOpen N ℓ).ι ≫ igusaTo N ℓ =
      (IsOpenImmersion.isoOfRangeEq (genericOpen N ℓ).ι (pullback.fst (igusaTo N ℓ) g) hrange).hom ≫
        pullback.snd (igusaTo N ℓ) g ≫ g := by
    rw [← pullback.condition, ← Category.assoc, hfac]
  rw [heq]
  haveI := smoothOfRelativeDimension_one_pullback_rat N ℓ hℓN
  have : SmoothOfRelativeDimension (0 + (1 + 0))
      ((IsOpenImmersion.isoOfRangeEq (genericOpen N ℓ).ι (pullback.fst (igusaTo N ℓ) g) hrange).hom ≫
        pullback.snd (igusaTo N ℓ) g ≫ g) := inferInstance
  simpa using this

theorem isProper_and_smooth_and_geometricallyIntegral (hℓN : ¬ ℓ ∣ N) :
    IsProper (igusaTo N ℓ) ∧ SmoothOfRelativeDimension 1 (igusaTo N ℓ) ∧
      GeometricallyIntegral (igusaTo N ℓ) := by
  haveI : Flat (igusaTo N ℓ) := flat_igusaTo N ℓ
  haveI : IsIntegral X₀ := ModularCurve.IgusaScheme.isIntegral N ℓ
  haveI : SmoothOfRelativeDimension 1 ((genericOpen N ℓ).ι ≫ igusaTo N ℓ) :=
    smoothOfRelativeDimension_one_genericOpen N ℓ hℓN
  exact ⟨isProper_igusaTo N ℓ,
    smoothOfRelativeDimension_one_igusaTo_of_smooth_fiber N ℓ
      (smooth_fiberToSpecResidueField N ℓ hℓN) (genericOpen N ℓ) (genericOpen_nonempty N ℓ hℓN),
    geometricallyIntegral_igusaTo N ℓ hℓN⟩

end Curve
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral.ModularCurve.IgusaScheme.Curve"

end IgusaScheme
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral.ModularCurve.IgusaScheme.Curve P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral.ModularCurve.IgusaScheme"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral.ModularCurve.IgusaScheme.Curve P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral.ModularCurve.IgusaScheme.Curve P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral.ModularCurve"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral.ModularCurve.IgusaScheme"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) :
    IsProper (igusaTo N ℓ) ∧ SmoothOfRelativeDimension 1 (igusaTo N ℓ) ∧
      GeometricallyIntegral (igusaTo N ℓ) :=
  ModularCurve.IgusaScheme.Curve.isProper_and_smooth_and_geometricallyIntegral N ℓ hℓN

end S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral (solution)
