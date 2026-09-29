-- Prove2me | solution 1 for ModularCurve.isPrime_span_algebraMap_chartAlgFin_xHFunctionField_top_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6e27c7a8-e57d-5645-8e39-f934663589d6

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_ModularCurve_exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth_of_isIntegrallyClosed
import Theorems.Thm_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral
import Theorems.Thm_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed
import Theorems.Thm_Ideal_isPrime_span_algebraMap_of_isDomain_tensor
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isPrime_span_algebraMap_chartAlgFin_xHFunctionField_top_of_natCast_ne_zero
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory ModularCurve P2MW.S_ModularCurve_isPrime_span_algebraMap_chartAlgFin_xHFunctionField_top_of_natCast_ne_zero.ModularCurve AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "jq modularFunctionFieldFull coeffEmb laurentBaseChange xHFunctionField xHFunctionFieldC_top IgusaScheme.igusaAlgebra IgusaScheme.jFull IgusaScheme.chartAlgFin IgusaScheme IgusaScheme.ιFin IgusaScheme.igusaTo IgusaScheme.ιFin_igusaTo exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth_of_isIntegrallyClosed IgusaScheme.isProper_and_smooth_and_geometricallyIntegral IgusaScheme.isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull finiteDimensional_adjoin_jFull_modularFunctionFieldFull"
namespace GoodRedMPrimeAux
p2m_open "ModularCurve"

theorem igusaAlgebra_eq (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    (IgusaScheme.igusaAlgebra N ℓ :
      Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N)) = Algebra.ofSubsemiring _ :=
  Algebra.algebra_ext _ _ fun _ => rfl

def SmoothFin (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (inst : Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N)) : Prop :=
  @Algebra.Smooth ↥(GaloisRep.ratLocalizedAt ℓ) _
    ↥(@TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) _ ↥(modularFunctionFieldFull N) _ inst
        {IgusaScheme.jFull N})
    (Subalgebra.toCommRing _) (Subalgebra.algebra _)

def DomFin (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type) [Field k] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) k]
    (inst : Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N)) : Prop :=
  IsDomain (k ⊗[↥(GaloisRep.ratLocalizedAt ℓ)]
    ↥(@TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) _ ↥(modularFunctionFieldFull N) _ inst
        {IgusaScheme.jFull N}))

theorem smooth_chartAlg_jFull (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) :
    Algebra.Smooth ↥(GaloisRep.ratLocalizedAt ℓ)
      ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N)
        {IgusaScheme.jFull N}) := by

  have hsm : AlgebraicGeometry.SmoothOfRelativeDimension 1 (IgusaScheme.igusaTo N ℓ) :=
    (ModularCurve.IgusaScheme.isProper_and_smooth_and_geometricallyIntegral N ℓ hℓN).2.1
  haveI : AlgebraicGeometry.Smooth (IgusaScheme.igusaTo N ℓ) :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth 1 (IgusaScheme.igusaTo N ℓ)
  have h : AlgebraicGeometry.Smooth (IgusaScheme.ιFin N ℓ ≫ IgusaScheme.igusaTo N ℓ) := inferInstance
  rw [IgusaScheme.ιFin_igusaTo, AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)]
    at h
  have h' : Algebra.Smooth ↥(GaloisRep.ratLocalizedAt ℓ) ↥(IgusaScheme.chartAlgFin N ℓ) :=
    RingHom.smooth_algebraMap.mp h

  have h1 : SmoothFin N ℓ (IgusaScheme.igusaAlgebra N ℓ) := h'
  rw [igusaAlgebra_eq] at h1
  exact h1

theorem isDomain_tensor_chartAlg_jFull (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (k : Type) [Field k] [IsAlgClosed k] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) k] :
    IsDomain (k ⊗[↥(GaloisRep.ratLocalizedAt ℓ)]
      ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N)
        {IgusaScheme.jFull N})) := by
  have h1 : DomFin N ℓ k (IgusaScheme.igusaAlgebra N ℓ) :=
    (ModularCurve.IgusaScheme.isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed N ℓ hℓN k).1
  rw [igusaAlgebra_eq] at h1
  exact h1

theorem exists_prime_not_dvd_forall_isUnit
    (A : Type) [CommRing A] [IsLocalRing A]
    (M' : ℕ) [NeZero M'] (hM' : (M' : IsLocalRing.ResidueField A) ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ M' ∧ ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A) := by
  set κ := IsLocalRing.ResidueField A
  have hunit : ∀ n : ℕ, (n : κ) ≠ 0 → IsUnit (n : A) := by
    intro n hn
    by_contra h
    apply hn
    have hmem : (n : A) ∈ IsLocalRing.maximalIdeal A := h
    have := (IsLocalRing.residue_eq_zero_iff (n : A)).mpr hmem
    simpa using this
  rcases CharP.char_is_prime_or_zero κ (ringChar κ) with hpr | h0
  · refine ⟨ringChar κ, hpr, ?_, ?_⟩
    · intro hdvd
      exact hM' ((ringChar.spec κ M').mpr hdvd)
    · intro n hn
      exact hunit n (fun h => hn ((ringChar.spec κ n).mp h))
  · haveI : CharP κ 0 := by
      have := ringChar.charP κ
      rwa [h0] at this
    haveI : CharZero κ := CharP.charP_to_charZero κ
    obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (M' + 1)
    refine ⟨p, hp, ?_, ?_⟩
    · intro hdvd
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M')) hdvd
      omega
    · intro n hn
      refine hunit n ?_
      have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero p)
      exact_mod_cast hn0

noncomputable def ratLocalizedAtToRing (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] (hu : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A)) :
    ↥(GaloisRep.ratLocalizedAt p) →+* A :=
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp Fact.out)
  haveI : IsLocalization.AtPrime (↥(GaloisRep.ratLocalizedAt p)) (Ideal.span {(p : ℤ)}) :=
    GaloisRep.isLocalization_ratLocalizedAt (Fact.out : p.Prime)
  IsLocalization.lift (M := (Ideal.span {(p : ℤ)}).primeCompl) (g := Int.castRingHom A) (fun y => by
    obtain ⟨y, hy⟩ := y
    have hy' : ¬ (p : ℤ) ∣ y := by
      simpa [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton] using hy
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
    · have hn : ¬ p ∣ n := fun h => hy' (Int.natCast_dvd_natCast.mpr h)
      simpa using hu n hn
    · have hn : ¬ p ∣ n := fun h => hy' ((Int.natCast_dvd_natCast.mpr h).neg_right)
      simpa using (hu n hn).neg)

theorem ratLocalizedAtToRing_spec (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] (hu : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A)) (z : ℤ) :
    ratLocalizedAtToRing p A hu (algebraMap ℤ _ z) = z := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp Fact.out)
  haveI : IsLocalization.AtPrime (↥(GaloisRep.ratLocalizedAt p)) (Ideal.span {(p : ℤ)}) :=
    GaloisRep.isLocalization_ratLocalizedAt (Fact.out : p.Prime)
  simp [ratLocalizedAtToRing]

theorem ringHom_ratLocalizedAt_ext (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (f g : ↥(GaloisRep.ratLocalizedAt p) →+* B) : f = g := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp Fact.out)
  haveI : IsLocalization.AtPrime (↥(GaloisRep.ratLocalizedAt p)) (Ideal.span {(p : ℤ)}) :=
    GaloisRep.isLocalization_ratLocalizedAt (Fact.out : p.Prime)
  refine IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl ?_
  exact RingHom.ext_int _ _

end ModularCurve.GoodRedMPrimeAux

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
open ModularCurve.GoodRedMPrimeAux in
theorem solution
    (M' : ℕ) [NeZero M']
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hM' : (M' : IsLocalRing.ResidueField A) ≠ 0)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M' (⊤ : Subgroup (ZMod M')ˣ)))
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    (Ideal.span {algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ}).IsPrime := by
  classical

  have hF : ModularCurve.xHFunctionField M' (⊤ : Subgroup (ZMod M')ˣ) = modularFunctionFieldFull M' :=
    (xHFunctionFieldC_top ℚ M').trans (qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull M')
  have hK' : K = ModularCurve.laurentBaseChange L (modularFunctionFieldFull M') := by rw [hK, hF]

  obtain ⟨p, hp, hpM, hu⟩ := exists_prime_not_dvd_forall_isUnit A M' hM'
  haveI : Fact p.Prime := ⟨hp⟩
  letI algZA : Algebra ↥(GaloisRep.ratLocalizedAt p) A := (ratLocalizedAtToRing p A hu).toAlgebra
  haveI : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A L :=
    IsScalarTower.of_algebraMap_eq' (ringHom_ratLocalizedAt_ext p _ _)

  haveI : Algebra.IsAlgebraic
      ↥(IntermediateField.adjoin ℚ ({IgusaScheme.jFull M'} : Set ↥(modularFunctionFieldFull M')))
      ↥(modularFunctionFieldFull M') := by
    haveI := ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull M'
    exact Algebra.IsAlgebraic.of_finite _ _
  have hsm := smooth_chartAlg_jFull M' p hpM
  have hx' : ((j : LaurentSeries L)) =
      ModularCurve.coeffEmb L ((IgusaScheme.jFull M' : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) := by
    rw [hj]; rfl
  obtain ⟨e, -⟩ :=
    ModularCurve.exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth_of_isIntegrallyClosed
      p (modularFunctionFieldFull M') (IgusaScheme.jFull M') hsm L K hK' A j hx'

  let Ω : Type := AlgebraicClosure (IsLocalRing.ResidueField A)
  haveI : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A Ω := inferInstance
  haveI hdomB := isDomain_tensor_chartAlg_jFull M' p hpM Ω
  have e₁ := Algebra.TensorProduct.cancelBaseChange ↥(GaloisRep.ratLocalizedAt p) A Ω Ω
    ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥(modularFunctionFieldFull M')
        {IgusaScheme.jFull M'})
  have e₂ := Algebra.TensorProduct.congr (AlgEquiv.refl : Ω ≃ₐ[Ω] Ω) e
  have e₃ : Ω ⊗[A] ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) ≃*
      Ω ⊗[A] (A ⊗[↥(GaloisRep.ratLocalizedAt p)]
        ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥(modularFunctionFieldFull M')
            {IgusaScheme.jFull M'})) := e₂.symm.toMulEquiv
  have e₄ : Ω ⊗[A] (A ⊗[↥(GaloisRep.ratLocalizedAt p)]
        ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥(modularFunctionFieldFull M')
            {IgusaScheme.jFull M'})) ≃*
      Ω ⊗[↥(GaloisRep.ratLocalizedAt p)]
        ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥(modularFunctionFieldFull M')
            {IgusaScheme.jFull M'}) := e₁.toMulEquiv
  haveI : IsDomain (Ω ⊗[A] ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j)) :=
    @MulEquiv.isDomain _ _ _ _ hdomB (e₃.trans e₄)

  have hker : RingHom.ker (algebraMap A Ω) = Ideal.span {ϖ} := by
    rw [← hϖ]
    have : algebraMap A Ω = (algebraMap (IsLocalRing.ResidueField A) Ω).comp (IsLocalRing.residue A) := rfl
    have hinj : RingHom.ker (algebraMap (IsLocalRing.ResidueField A) Ω) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap (IsLocalRing.ResidueField A) Ω).injective
    rw [this, ← RingHom.comap_ker, hinj, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
  have hmax : (Ideal.span {ϖ} : Ideal A).IsMaximal := by
    rw [← hϖ]; exact IsLocalRing.maximalIdeal.isMaximal A
  exact Ideal.isPrime_span_algebraMap_of_isDomain_tensor (κ := Ω) ϖ hker hmax

end S_ModularCurve_isPrime_span_algebraMap_chartAlgFin_xHFunctionField_top_of_natCast_ne_zero
end P2MW
export P2MW.S_ModularCurve_isPrime_span_algebraMap_chartAlgFin_xHFunctionField_top_of_natCast_ne_zero (solution)
