-- Prove2me | solution 1 for ModularCurve.FullLevel.jInvChartInf_not_mem_of_exists_two_minimalPrimes_span_le_chartAlgInf_laurentBaseChange_gamma0_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/60bdf9fc-b7f9-5d21-8c93-f372b834a6ac

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_ModularUnit

import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlgInf_mul_chartAlgInf_laurentBaseChange_of_charZero_of_not_dvd

import Theorems.Thm_ModularCurve_IgusaScheme_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_finite_minimalPrimes_tensor_chartAlgInf_mul_and_ncard_eq_two_of_not_dvd

import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast

import Theorems.Thm_ModularCurve_IgusaScheme_sup_sup_span_jInvChartInf_eq_top_of_mem_minimalPrimes_of_not_dvd
import Theorems.Thm_ValuationSubring_exists_ratLocalizedAt_ringHom_of_liesOverPrime
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_jInvChartInf_not_mem_of_exists_two_minimalPrimes_span_le_chartAlgInf_laurentBaseChange_gamma0_mul
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure"
p2m_attr_erase "instance" "instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

open scoped TensorProduct
open ModularCurve ModularCurve.IgusaScheme AlgebraicCurve

namespace X0qDvrCross

theorem exists_ringHom_ratLocalizedAt (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (L : Type) [Field L] [CharZero L] [Algebra A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    ∃ f : ↥(GaloisRep.ratLocalizedAt p) →+* A,
      (algebraMap A L).comp f = algebraMap ↥(GaloisRep.ratLocalizedAt p) L := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  haveI hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hp)
  haveI := GaloisRep.isLocalization_ratLocalizedAt hp
  have hunit : ∀ y : (Ideal.span {(p : ℤ)}).primeCompl, IsUnit (algebraMap ℤ A y) := by
    intro y
    by_contra hy
    have hmem : algebraMap ℤ A y ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal _).mpr hy
    let I : Ideal ℤ := Ideal.comap (algebraMap ℤ A) (IsLocalRing.maximalIdeal A)
    have hI : I.IsPrime := Ideal.comap_isPrime _ _
    have hpI : (p : ℤ) ∈ I := by
      change algebraMap ℤ A (p : ℤ) ∈ IsLocalRing.maximalIdeal A
      simpa using hAp
    have hle : Ideal.span {(p : ℤ)} ≤ I := (Ideal.span_singleton_le_iff_mem _).mpr hpI
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      Ideal.IsPrime.isMaximal hP (by simpa using hp0)
    have hEq : Ideal.span {(p : ℤ)} = I := hmax.eq_of_le hI.ne_top hle
    have hyI : (y : ℤ) ∈ I := hmem
    rw [← hEq] at hyI
    exact y.2 hyI
  refine ⟨IsLocalization.lift (M := (Ideal.span {(p : ℤ)}).primeCompl) hunit, ?_⟩
  apply IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl
  rw [RingHom.comp_assoc, IsLocalization.lift_comp]
  exact RingHom.ext_int _ _

theorem isLocalHom_and_flat_of_mem_maximalIdeal (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (L : Type) [Field L] [CharZero L] [Algebra A L] [IsFractionRing A L]
    [Algebra ↥(GaloisRep.ratLocalizedAt p) A] [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    IsLocalHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) A) ∧ Module.Flat ↥(GaloisRep.ratLocalizedAt p) A := by
  classical
  have hp : p.Prime := Fact.out
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  haveI := GaloisRep.isLocalization_ratLocalizedAt hp
  haveI hdvr : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp
  have hRL : algebraMap ↥(GaloisRep.ratLocalizedAt p) L =
      (algebraMap ℚ L).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) :=
    IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (Subsingleton.elim _ _)
  have hinjL : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt p) L) := by
    rw [hRL, RingHom.coe_comp]
    exact (algebraMap ℚ L).injective.comp Subtype.val_injective
  have hinj : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt p) A) := by
    intro r s h
    apply hinjL
    rw [IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt p) A L, h,
      ← IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt p) A L]
  haveI : Module.IsTorsionFree ↥(GaloisRep.ratLocalizedAt p) A := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r a h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · left; exact hinj (by rw [h, map_zero])
    · right; exact h
  refine ⟨⟨fun r hr => ?_⟩, inferInstance⟩
  by_contra hnu
  have hr' : r ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) := (IsLocalRing.mem_maximalIdeal _).mpr hnu
  rw [GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p hp] at hr'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr'
  have hmem : algebraMap ↥(GaloisRep.ratLocalizedAt p) A (c * p) ∈ IsLocalRing.maximalIdeal A := by
    rw [map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ hAp
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem hr

section RightStructure

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

noncomputable def commRight :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)
    (A ⊗[R] B) ≃ₗ[B] (B ⊗[R] A) :=
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)
  { (Algebra.TensorProduct.comm R A B).toLinearEquiv.toAddEquiv with
    map_smul' := fun b x => by
      change (Algebra.TensorProduct.comm R A B) (b • x) = b • (Algebra.TensorProduct.comm R A B) x
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul a b' =>
        change (Algebra.TensorProduct.comm R A B) ((1 : A) ⊗ₜ[R] b * a ⊗ₜ[R] b') = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.comm_tmul,
          Algebra.TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add] }

theorem flat_right [Module.Flat R A] :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)
    Module.Flat B (A ⊗[R] B) :=
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)
  Module.Flat.of_linearEquiv (commRight (R := R) (A := A) (B := B))

theorem tmul_one_eq_of_eq_unit_mul_pow (ϖ x : A) (u : Aˣ) (n : ℕ) (hx : x = ↑u * ϖ ^ n) :
    x ⊗ₜ[R] (1 : B) = ((u : A) ⊗ₜ[R] (1 : B)) * (ϖ ⊗ₜ[R] (1 : B)) ^ n := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hx]

theorem tmul_one_mem_of_eq_unit_mul_pow (ϖ x : A) (u : Aˣ) (n : ℕ) (hx : x = ↑u * ϖ ^ n)
    (𝔮 : Ideal (A ⊗[R] B)) [𝔮.IsPrime] (h : x ⊗ₜ[R] (1 : B) ∈ 𝔮) : ϖ ⊗ₜ[R] (1 : B) ∈ 𝔮 := by
  have hu : IsUnit ((u : A) ⊗ₜ[R] (1 : B)) :=
    (Units.isUnit u).map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)
  rw [tmul_one_eq_of_eq_unit_mul_pow ϖ x u n hx, Ideal.unit_mul_mem_iff_mem _ hu] at h
  exact Ideal.IsPrime.mem_of_pow_mem ‹_› n h

theorem comap_includeRight_mem_minimalPrimes [Module.Flat R A] (ϖ x : A) (u : Aˣ) (n : ℕ) (hn : 0 < n)
    (hx : x = ↑u * ϖ ^ n) (c : B) (hc : (1 : A) ⊗ₜ[R] c = x ⊗ₜ[R] (1 : B))
    (𝔮 : Ideal (A ⊗[R] B)) (h𝔮 : 𝔮 ∈ (Ideal.span {ϖ ⊗ₜ[R] (1 : B)}).minimalPrimes) :
    Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) 𝔮 ∈ (Ideal.span {c}).minimalPrimes := by
  classical
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)
  haveI : Module.Flat B (A ⊗[R] B) := flat_right
  haveI h𝔮prime : 𝔮.IsPrime := h𝔮.1.1
  have hϖ𝔮 : ϖ ⊗ₜ[R] (1 : B) ∈ 𝔮 := h𝔮.1.2 (Ideal.subset_span rfl)

  haveI hQprime : (𝔮.under B).IsPrime := Ideal.comap_isPrime _ _
  have hunder : Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) 𝔮 = 𝔮.under B := rfl
  have hcmem : ∀ (P : Ideal (A ⊗[R] B)) [P.IsPrime], ϖ ⊗ₜ[R] (1 : B) ∈ P → c ∈ P.under B := by
    intro P _ hP
    rw [Ideal.under_def, Ideal.mem_comap]
    change (1 : A) ⊗ₜ[R] c ∈ P
    rw [hc, tmul_one_eq_of_eq_unit_mul_pow ϖ x u n hx]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem P hP n hn)
  have hcQ : Ideal.span {c} ≤ 𝔮.under B := (Ideal.span_singleton_le_iff_mem _).mpr (hcmem 𝔮 hϖ𝔮)

  obtain ⟨P', hP'min, hP'le⟩ := Ideal.exists_minimalPrimes_le hcQ
  haveI : P'.IsPrime := hP'min.1.1
  haveI : 𝔮.LiesOver (𝔮.under B) := ⟨rfl⟩
  obtain ⟨𝔮', h𝔮'le, h𝔮'prime, h𝔮'over⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := P') (q := 𝔮.under B) 𝔮 hP'le
  have hc𝔮' : x ⊗ₜ[R] (1 : B) ∈ 𝔮' := by
    have : c ∈ 𝔮'.under B := by rw [← h𝔮'over.over]; exact hP'min.1.2 (Ideal.subset_span rfl)
    rw [Ideal.under_def, Ideal.mem_comap] at this
    change (1 : A) ⊗ₜ[R] c ∈ 𝔮' at this
    rwa [hc] at this
  have hϖ𝔮' : ϖ ⊗ₜ[R] (1 : B) ∈ 𝔮' := tmul_one_mem_of_eq_unit_mul_pow ϖ x u n hx 𝔮' hc𝔮'
  have h𝔮𝔮' : 𝔮 ≤ 𝔮' := h𝔮.2 ⟨h𝔮'prime, (Ideal.span_singleton_le_iff_mem _).mpr hϖ𝔮'⟩ h𝔮'le
  have heq : 𝔮' = 𝔮 := le_antisymm h𝔮'le h𝔮𝔮'
  have hQP' : 𝔮.under B = P' := by rw [h𝔮'over.over, heq]
  rw [hunder, hQP']
  exact hP'min

end RightStructure

section Theta

variable (R A B κ : Type) [CommRing R] [CommRing A] [CommRing B] [Field κ] [Algebra R A] [Algebra R B]
  [Algebra A κ] [Algebra R κ] [IsScalarTower R A κ]

noncomputable def theta : A ⊗[R] B →ₐ[R] κ ⊗[R] B :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A κ) (AlgHom.id R B)

theorem theta_tmul (a : A) (b : B) : theta R A B κ (a ⊗ₜ[R] b) = algebraMap A κ a ⊗ₜ[R] b :=
  Algebra.TensorProduct.map_tmul _ _ a b

variable {R A B κ}

theorem exists_rTensor_subtype_eq {N P : Type} [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P]
    [Module.Flat R B] (S : Submodule R N) (g : N →ₗ[R] P) (hSg : LinearMap.ker g = S)
    (t : N ⊗[R] B) (ht : g.rTensor B t = 0) : ∃ s : ↥S ⊗[R] B, S.subtype.rTensor B s = t := by
  have hex : Function.Exact S.subtype g := LinearMap.exact_iff.mpr (by rw [hSg, Submodule.range_subtype])
  have := Module.Flat.rTensor_exact B hex
  exact (this t).mp ht

theorem mem_span_of_theta_eq_zero [Module.Flat R B] (ϖ : A)
    (hker : ∀ a : A, algebraMap A κ a = 0 ↔ a ∈ Ideal.span {ϖ})
    (t : A ⊗[R] B) (ht : theta R A B κ t = 0) : t ∈ Ideal.span {ϖ ⊗ₜ[R] (1 : B)} := by
  classical
  let g : A →ₗ[R] κ := (IsScalarTower.toAlgHom R A κ).toLinearMap
  let S : Submodule R A := (Ideal.span {ϖ}).restrictScalars R
  have hSg : LinearMap.ker g = S := by
    ext a
    rw [LinearMap.mem_ker]
    exact hker a
  have hθg : ∀ t : A ⊗[R] B, theta R A B κ t = g.rTensor B t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rw [theta_tmul, LinearMap.rTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  obtain ⟨s, hs⟩ := exists_rTensor_subtype_eq S g hSg t (by rw [← hθg, ht])
  rw [← hs]
  clear hs ht hθg
  induction s using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul m b =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]
    have hm : (m : A) ∈ Ideal.span {ϖ} := m.2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hm
    have : ((m : A)) ⊗ₜ[R] b = (c ⊗ₜ[R] b) * (ϖ ⊗ₜ[R] (1 : B)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hc]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem mem_span_of_one_tmul_eq_zero [Module.Flat R B] (c : R)
    (hker : ∀ r : R, algebraMap R κ r = 0 ↔ r ∈ Ideal.span {c})
    (b : B) (hb : (1 : κ) ⊗ₜ[R] b = 0) : b ∈ Ideal.span {algebraMap R B c} := by
  classical
  let g : R →ₗ[R] κ := Algebra.linearMap R κ
  let S : Submodule R R := Ideal.span {c}
  have hSg : LinearMap.ker g = S := by
    ext r
    rw [LinearMap.mem_ker]
    exact hker r
  have ht : g.rTensor B ((1 : R) ⊗ₜ[R] b) = 0 := by
    rw [LinearMap.rTensor_tmul]
    change algebraMap R κ 1 ⊗ₜ[R] b = 0
    rw [map_one, hb]
  obtain ⟨s, hs⟩ := exists_rTensor_subtype_eq S g hSg _ ht
  have hb' : b = TensorProduct.lid R B (S.subtype.rTensor B s) := by
    rw [hs, TensorProduct.lid_tmul, one_smul]
  rw [hb']
  clear hb' hs ht hb
  induction s using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | tmul m b' =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, TensorProduct.lid_tmul, Algebra.smul_def]
    have hm : (m : R) ∈ Ideal.span {c} := m.2
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hm
    rw [← hd, map_mul, mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

theorem isIntegral_theta [Algebra.IsIntegral A κ] :
    letI : Algebra (A ⊗[R] B) (κ ⊗[R] B) := (theta R A B κ).toRingHom.toAlgebra
    Algebra.IsIntegral (A ⊗[R] B) (κ ⊗[R] B) := by
  classical
  letI : Algebra (A ⊗[R] B) (κ ⊗[R] B) := (theta R A B κ).toRingHom.toAlgebra
  have halg : ∀ t : A ⊗[R] B, algebraMap (A ⊗[R] B) (κ ⊗[R] B) t = theta R A B κ t := fun _ => rfl
  have hcomp : (algebraMap (A ⊗[R] B) (κ ⊗[R] B)).comp
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) =
      (Algebra.TensorProduct.includeLeftRingHom : κ →+* κ ⊗[R] B).comp (algebraMap A κ) := by
    ext a
    simp only [RingHom.comp_apply, halg]
    change theta R A B κ (a ⊗ₜ[R] 1) = (algebraMap A κ a) ⊗ₜ[R] 1
    rw [theta_tmul]
  refine ⟨fun z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | tmul c b =>
    have h1 : c ⊗ₜ[R] b = (c ⊗ₜ[R] (1 : B)) * ((1 : κ) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h1]
    refine IsIntegral.mul ?_ ?_
    · have hc : IsIntegral A c := Algebra.IsIntegral.isIntegral (R := A) c
      exact hc.map_of_comp_eq _ _ hcomp
    · have : ((1 : κ) ⊗ₜ[R] b) = algebraMap (A ⊗[R] B) (κ ⊗[R] B) ((1 : A) ⊗ₜ[R] b) := by
        rw [halg, theta_tmul, map_one]
      rw [this]
      exact isIntegral_algebraMap
  | add x y hx hy => exact hx.add hy

end Theta

section transport
variable {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra A C]

theorem algEquiv_tmul_one (e : A ⊗[R] B ≃ₐ[A] C) (a : A) : e (a ⊗ₜ[R] (1 : B)) = algebraMap A C a := by
  rw [← e.commutes a, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem tmul_one_mem_comap (e : A ⊗[R] B ≃ₐ[A] C) (a : A) (y : Ideal C) (h : algebraMap A C a ∈ y) :
    a ⊗ₜ[R] (1 : B) ∈ Ideal.comap e.toRingEquiv.toRingHom y := by
  rw [Ideal.mem_comap]
  change e (a ⊗ₜ[R] (1 : B)) ∈ y
  rwa [algEquiv_tmul_one]

theorem comap_mem_minimalPrimes_span_of_ringEquiv {S T : Type} [CommRing S] [CommRing T] (e : S ≃+* T) (s : S)
    (𝔭 : Ideal T) (h𝔭 : 𝔭 ∈ (Ideal.span {e s}).minimalPrimes) :
    Ideal.comap e.toRingHom 𝔭 ∈ (Ideal.span {s}).minimalPrimes := by
  have hI : Ideal.span {e s} = Ideal.comap e.symm.toRingHom (Ideal.span {s}) := by
    change _ = Ideal.comap e.symm _
    rw [Ideal.comap_symm, Ideal.map_span, Set.image_singleton]
  rw [hI, Ideal.comap_minimalPrimes_eq_of_surjective (f := e.symm.toRingHom) e.symm.surjective] at h𝔭
  obtain ⟨𝔮, h𝔮, rfl⟩ := h𝔭
  have : Ideal.comap e.toRingHom (Ideal.comap e.symm.toRingHom 𝔮) = 𝔮 := by
    rw [Ideal.comap_comap]
    convert Ideal.comap_id 𝔮
    ext x; simp
  rw [this]; exact h𝔮

end transport

end X0qDvrCross

open X0qDvrCross

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L
      (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M' * q))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j : ↥K₀) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j)) [y.IsPrime]
    (hyϖ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j) ϖ ∈ y)
    (htwo : ∃ 𝔭 ∈ (Ideal.span {algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j) ϖ}).minimalPrimes,
        ∃ 𝔭' ∈ (Ideal.span {algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j) ϖ}).minimalPrimes,
          𝔭 ≠ 𝔭' ∧ 𝔭 ≤ y ∧ 𝔭' ≤ y)

    : AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K₀) j ∉ y := by
  classical
  intro hcusp
  have hq : q.Prime := Fact.out

  obtain ⟨f, hf⟩ := exists_ringHom_ratLocalizedAt q A L hAq
  letI algRA : Algebra ↥(GaloisRep.ratLocalizedAt q) A := f.toAlgebra
  haveI : IsScalarTower ↥(GaloisRep.ratLocalizedAt q) A L := IsScalarTower.of_algebraMap_eq' hf.symm
  obtain ⟨hloc, hflatA⟩ := isLocalHom_and_flat_of_mem_maximalIdeal q A L hAq
  haveI := hloc
  haveI := hflatA
  haveI : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq)
  haveI := GaloisRep.isLocalization_ratLocalizedAt hq
  haveI hdvrR : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt q) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt q hq

  obtain ⟨e, he⟩ :=
    ModularCurve.IgusaScheme.exists_algEquiv_tensor_chartAlgInf_mul_chartAlgInf_laurentBaseChange_of_charZero_of_not_dvd
      M' q hqM' L K₀ hK₀ A hAq j hj

  have hRB : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt q) ↥(chartAlgInf (M' * q) q)) := by
    intro r s h
    have h' : algebraMap ℚ ↥(modularFunctionFieldFull (M' * q)) (r : ℚ) =
        algebraMap ℚ ↥(modularFunctionFieldFull (M' * q)) (s : ℚ) := congrArg Subtype.val h
    exact Subtype.ext ((algebraMap ℚ ↥(modularFunctionFieldFull (M' * q))).injective h')
  haveI : Module.IsTorsionFree ↥(GaloisRep.ratLocalizedAt q) ↥(chartAlgInf (M' * q) q) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r b h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · left; exact hRB (by rw [h, map_zero])
    · right; exact h
  haveI hBflat : Module.Flat ↥(GaloisRep.ratLocalizedAt q) ↥(chartAlgInf (M' * q) q) := inferInstance

  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_zero] at hϖ
    exact IsDiscreteValuationRing.not_a_field A hϖ
  have hϖirr : Irreducible ϖ := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ hϖ0 hϖ
  have hqA0 : (q : A) ≠ 0 := by
    intro h
    have : (q : L) = 0 := by rw [← map_natCast (algebraMap A L), h, map_zero]
    exact (Nat.cast_ne_zero.mpr hq.ne_zero) this
  obtain ⟨n, u, hqu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hqA0 hϖirr
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hqu
      exact (IsLocalRing.mem_maximalIdeal _).mp hAq (hqu ▸ Units.isUnit u)
    · exact h
  let y' : Ideal (A ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgInf (M' * q) q)) := Ideal.comap e.toRingEquiv.toRingHom y
  haveI hy' : y'.IsPrime := Ideal.comap_isPrime _ _
  have hϖ' : ϖ ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] (1 : ↥(chartAlgInf (M' * q) q)) ∈ y' := tmul_one_mem_comap e ϖ y hyϖ
  have heϖ : e.toRingEquiv (ϖ ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] (1 : ↥(chartAlgInf (M' * q) q))) =
      algebraMap A ↥(TwoChartIntegralModel.chartAlgInf A (↥K₀) j) ϖ := algEquiv_tmul_one e ϖ
  obtain ⟨𝔭₀, h𝔭₀, 𝔭₁, h𝔭₁, hne, hle₀, hle₁⟩ := htwo
  let 𝔮₀ : Ideal (A ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgInf (M' * q) q)) := Ideal.comap e.toRingEquiv.toRingHom 𝔭₀
  let 𝔮₁ : Ideal (A ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgInf (M' * q) q)) := Ideal.comap e.toRingEquiv.toRingHom 𝔭₁
  have h𝔮₀ : 𝔮₀ ∈ (Ideal.span {ϖ ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] (1 : ↥(chartAlgInf (M' * q) q))}).minimalPrimes :=
    comap_mem_minimalPrimes_span_of_ringEquiv e.toRingEquiv _ 𝔭₀ (by rw [heϖ]; exact h𝔭₀)
  have h𝔮₁ : 𝔮₁ ∈ (Ideal.span {ϖ ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] (1 : ↥(chartAlgInf (M' * q) q))}).minimalPrimes :=
    comap_mem_minimalPrimes_span_of_ringEquiv e.toRingEquiv _ 𝔭₁ (by rw [heϖ]; exact h𝔭₁)
  have h𝔮ne : 𝔮₀ ≠ 𝔮₁ := fun h =>
    hne (Ideal.comap_injective_of_surjective e.toRingEquiv.toRingHom e.toRingEquiv.surjective h)
  haveI : 𝔮₀.IsPrime := h𝔮₀.1.1
  haveI : 𝔮₁.IsPrime := h𝔮₁.1.1
  have hϖ𝔮₀ : ϖ ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] (1 : ↥(chartAlgInf (M' * q) q)) ∈ 𝔮₀ := h𝔮₀.1.2 (Ideal.subset_span rfl)
  have hϖ𝔮₁ : ϖ ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] (1 : ↥(chartAlgInf (M' * q) q)) ∈ 𝔮₁ := h𝔮₁.1.2 (Ideal.subset_span rfl)

  let iR : ↥(chartAlgInf (M' * q) q) →ₐ[↥(GaloisRep.ratLocalizedAt q)] A ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgInf (M' * q) q) :=
    Algebra.TensorProduct.includeRight
  have hpB : ((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q)) • (1 : ↥(chartAlgInf (M' * q) q)) = ((q : ℕ) : ↥(chartAlgInf (M' * q) q)) := by
    rw [Algebra.smul_def, mul_one, map_natCast]
  have hc : (1 : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] ((q : ℕ) : ↥(chartAlgInf (M' * q) q)) =
      ((q : ℕ) : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] (1 : ↥(chartAlgInf (M' * q) q)) := by
    rw [← Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.natCast_def]
  have hQ₀ : Ideal.comap iR 𝔮₀ ∈ (Ideal.span {((q : ℕ) : ↥(chartAlgInf (M' * q) q))}).minimalPrimes :=
    comap_includeRight_mem_minimalPrimes ϖ (q : A) u n hn hqu _ hc 𝔮₀ h𝔮₀
  have hQ₁ : Ideal.comap iR 𝔮₁ ∈ (Ideal.span {((q : ℕ) : ↥(chartAlgInf (M' * q) q))}).minimalPrimes :=
    comap_includeRight_mem_minimalPrimes ϖ (q : A) u n hn hqu _ hc 𝔮₁ h𝔮₁

  have hQne : Ideal.comap iR 𝔮₀ ≠ Ideal.comap iR 𝔮₁ := by

    haveI : CharP (IsLocalRing.ResidueField A) q := by
      refine (CharP.charP_iff_prime_eq_zero hq).mpr ?_
      have : IsLocalRing.residue A (q : A) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hAq
      simpa using this
    haveI : CharP (AlgebraicClosure (IsLocalRing.ResidueField A)) q :=
      charP_of_injective_algebraMap (algebraMap (IsLocalRing.ResidueField A) _).injective q
    haveI : Algebra.IsIntegral A (IsLocalRing.ResidueField A) :=
      Algebra.isIntegral_of_surjective (by
        rw [IsLocalRing.ResidueField.algebraMap_eq]; exact IsLocalRing.residue_surjective)
    haveI : Algebra.IsIntegral A (AlgebraicClosure (IsLocalRing.ResidueField A)) :=
      Algebra.IsIntegral.trans (IsLocalRing.ResidueField A)
    have hkerA : ∀ a : A, algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)) a = 0 ↔ a ∈ Ideal.span {ϖ} := by
      intro a
      rw [IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A)),
        map_eq_zero, IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff, hϖ]
    have hkerR : ∀ r : ↥(GaloisRep.ratLocalizedAt q),
        algebraMap ↥(GaloisRep.ratLocalizedAt q) (AlgebraicClosure (IsLocalRing.ResidueField A)) r = 0 ↔
          r ∈ Ideal.span {((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q))} := by
      intro r
      rw [IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt q) A (AlgebraicClosure (IsLocalRing.ResidueField A)),
        hkerA, ← hϖ, ← GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast q hq, IsLocalRing.mem_maximalIdeal,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
      exact ⟨fun h hr => h (hr.map _), fun h hr => h (isUnit_of_map_unit (algebraMap _ A) r hr)⟩
    let θ := theta ↥(GaloisRep.ratLocalizedAt q) A ↥(chartAlgInf (M' * q) q) (AlgebraicClosure (IsLocalRing.ResidueField A))
    have hθ : ∀ a b, θ (a ⊗ₜ b) = algebraMap A _ a ⊗ₜ b := theta_tmul _ _ _ _
    letI algθ := θ.toRingHom.toAlgebra
    have halgθ : ∀ t, algebraMap _ _ t = θ t := fun _ => rfl
    haveI : Algebra.IsIntegral (A ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgInf (M' * q) q))
        ((AlgebraicClosure (IsLocalRing.ResidueField A)) ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgInf (M' * q) q)) :=
      isIntegral_theta

    have hθϖ : θ (ϖ ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] (1 : ↥(chartAlgInf (M' * q) q))) = 0 := by
      rw [hθ, (hkerA ϖ).mpr (Ideal.mem_span_singleton_self ϖ), TensorProduct.zero_tmul]

    obtain ⟨hfin, hcard⟩ :=
      ModularCurve.IgusaScheme.finite_minimalPrimes_tensor_chartAlgInf_mul_and_ncard_eq_two_of_not_dvd M' q hqM'
        (AlgebraicClosure (IsLocalRing.ResidueField A))

    have lift : ∀ (𝔮 : Ideal (A ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgInf (M' * q) q))),
        𝔮 ∈ (Ideal.span {ϖ ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] (1 : ↥(chartAlgInf (M' * q) q))}).minimalPrimes →
        ∃ 𝔔 ∈ minimalPrimes ((AlgebraicClosure (IsLocalRing.ResidueField A)) ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgInf (M' * q) q)),
          Ideal.comap θ.toRingHom 𝔔 = 𝔮 := by
      intro 𝔮 h𝔮
      haveI : 𝔮.IsPrime := h𝔮.1.1
      have hker : Ideal.comap (algebraMap (A ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgInf (M' * q) q))
          ((AlgebraicClosure (IsLocalRing.ResidueField A)) ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgInf (M' * q) q))) ⊥ ≤ 𝔮 := by
        intro t ht
        rw [Ideal.mem_comap, halgθ, Ideal.mem_bot] at ht
        exact h𝔮.1.2 (mem_span_of_theta_eq_zero ϖ hkerA t ht)
      obtain ⟨𝔔, -, h𝔔prime, h𝔔comap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔮 ⊥ hker
      obtain ⟨𝔔', h𝔔'min, h𝔔'le⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := 𝔔) bot_le
      haveI : 𝔔'.IsPrime := h𝔔'min.1.1
      refine ⟨𝔔', h𝔔'min, le_antisymm ?_ (h𝔮.2 ⟨Ideal.comap_isPrime _ _, ?_⟩ ?_)⟩
      · rw [← h𝔔comap]; exact Ideal.comap_mono h𝔔'le
      · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
        change θ _ ∈ 𝔔'
        rw [hθϖ]; exact zero_mem _
      · rw [← h𝔔comap]; exact Ideal.comap_mono h𝔔'le
    obtain ⟨𝔔₀, h𝔔₀min, h𝔔₀c⟩ := lift 𝔮₀ h𝔮₀
    obtain ⟨𝔔₁, h𝔔₁min, h𝔔₁c⟩ := lift 𝔮₁ h𝔮₁
    have h𝔔ne : 𝔔₀ ≠ 𝔔₁ := by
      intro h; apply h𝔮ne; rw [← h𝔔₀c, ← h𝔔₁c, h]
    have hall : minimalPrimes ((AlgebraicClosure (IsLocalRing.ResidueField A)) ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgInf (M' * q) q))
        = {𝔔₀, 𝔔₁} := by
      symm
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfin
      · intro P hP
        rcases hP with rfl | rfl
        · exact h𝔔₀min
        · exact h𝔔₁min
      · rw [hcard, Set.ncard_pair h𝔔ne]

    intro hQeq
    obtain ⟨-, -, -, hcard2⟩ :=
      ModularCurve.IgusaScheme.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd M' q hqM'
    obtain ⟨P', hP'min, hP'ne⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hcard2]; norm_num) (Ideal.comap iR 𝔮₀)
    haveI : P'.IsPrime := hP'min.1.1

    have hnot : ¬ (Ideal.comap iR 𝔮₀ ≤ P') := by
      intro hle
      exact hP'ne (le_antisymm hle (hP'min.2 ⟨hQ₀.1.1, hQ₀.1.2⟩ hle)).symm
    obtain ⟨b, hb₀, hbP'⟩ := Set.not_subset.mp hnot
    have hb₁ : b ∈ Ideal.comap iR 𝔮₁ := hQeq ▸ hb₀

    have h1 : θ ((1 : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] b) =
        (1 : AlgebraicClosure (IsLocalRing.ResidueField A)) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] b := by
      rw [hθ, map_one]
    have hb𝔔₀ : (1 : AlgebraicClosure (IsLocalRing.ResidueField A)) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] b ∈ 𝔔₀ := by
      have : (1 : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] b ∈ Ideal.comap θ.toRingHom 𝔔₀ := by rw [h𝔔₀c]; exact hb₀
      rw [Ideal.mem_comap] at this
      change θ _ ∈ 𝔔₀ at this
      rwa [h1] at this
    have hb𝔔₁ : (1 : AlgebraicClosure (IsLocalRing.ResidueField A)) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] b ∈ 𝔔₁ := by
      have : (1 : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] b ∈ Ideal.comap θ.toRingHom 𝔔₁ := by rw [h𝔔₁c]; exact hb₁
      rw [Ideal.mem_comap] at this
      change θ _ ∈ 𝔔₁ at this
      rwa [h1] at this
    have hnil : (1 : AlgebraicClosure (IsLocalRing.ResidueField A)) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] b ∈
        (⊥ : Ideal ((AlgebraicClosure (IsLocalRing.ResidueField A)) ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgInf (M' * q) q))).radical := by
      rw [← Ideal.sInf_minimalPrimes]
      change _ ∈ sInf (minimalPrimes _)
      rw [hall, Submodule.mem_sInf]
      intro i hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with h | h
      · rw [h]; exact hb𝔔₀
      · rw [h]; exact hb𝔔₁
    obtain ⟨m, hm⟩ := hnil
    rw [Ideal.mem_bot, Algebra.TensorProduct.tmul_pow, one_pow] at hm

    have hbm : b ^ m ∈ Ideal.span {algebraMap ↥(GaloisRep.ratLocalizedAt q) ↥(chartAlgInf (M' * q) q) ((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q))} :=
      mem_span_of_one_tmul_eq_zero ((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q)) hkerR (b ^ m) hm
    rw [map_natCast] at hbm
    exact hbP' (Ideal.IsPrime.mem_of_pow_mem ‹_› m (hP'min.1.2 hbm))

  let yB : Ideal ↥(chartAlgInf (M' * q) q) := Ideal.comap iR y'
  haveI : yB.IsPrime := Ideal.comap_isPrime _ _
  have hyBq : ((q : ℕ) : ↥(chartAlgInf (M' * q) q)) ∈ yB := by
    change iR _ ∈ y'
    rw [map_natCast, Algebra.TensorProduct.natCast_def, tmul_one_eq_of_eq_unit_mul_pow ϖ (q : A) u n hqu]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem y' hϖ' n hn)
  have htwoB : ∃ 𝔭 ∈ (Ideal.span {((q : ℕ) : ↥(chartAlgInf (M' * q) q))}).minimalPrimes,
      ∃ 𝔭' ∈ (Ideal.span {((q : ℕ) : ↥(chartAlgInf (M' * q) q))}).minimalPrimes, 𝔭 ≠ 𝔭' ∧ 𝔭 ≤ yB ∧ 𝔭' ≤ yB :=
    ⟨_, hQ₀, _, hQ₁, hQne, Ideal.comap_mono (f := iR) (Ideal.comap_mono (f := e.toRingEquiv.toRingHom) hle₀),
      Ideal.comap_mono (f := iR) (Ideal.comap_mono (f := e.toRingEquiv.toRingHom) hle₁)⟩

  have hejInv : e ((1 : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] jInvChartInf (M' * q) q) =
      TwoChartIntegralModel.jInvChartInf A (↥K₀) j := by
    apply Subtype.ext
    apply Subtype.ext
    rw [he]
    first
      | (show ModularCurve.coeffEmb L (((jFull (M' * q))⁻¹ : ↥(modularFunctionFieldFull (M' * q))) : LaurentSeries ℚ) =
            (((j⁻¹ : ↥K₀)) : LaurentSeries L)
         rw [InvMemClass.coe_inv, map_inv₀, ModularCurve.IgusaScheme.coe_jFull, InvMemClass.coe_inv, hj])
      | (simp [map_inv₀, ModularCurve.IgusaScheme.coe_jFull, AlgebraicCurve.TwoChartIntegralModel.jInvChartInf, hj])
      | (rw [he]; simp [map_inv₀, ModularCurve.IgusaScheme.coe_jFull, hj])
  have hjB : jInvChartInf (M' * q) q ∈ yB := by
    change iR _ ∈ y'
    change e.toRingEquiv.toRingHom (iR (jInvChartInf (M' * q) q)) ∈ y
    have : iR (jInvChartInf (M' * q) q) = (1 : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] jInvChartInf (M' * q) q := rfl
    rw [this]
    change e ((1 : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt q)] jInvChartInf (M' * q) q) ∈ y
    rw [hejInv]
    exact hcusp
  obtain ⟨Q₀, hQ₀m, Q₁, hQ₁m, hQne', hQ₀le, hQ₁le⟩ := htwoB
  have htop := ModularCurve.IgusaScheme.sup_sup_span_jInvChartInf_eq_top_of_mem_minimalPrimes_of_not_dvd M' q hqM' Q₀ Q₁ hQ₀m hQ₁m hQne'
  have hle : (⊤ : Ideal ↥(chartAlgInf (M' * q) q)) ≤ yB := by
    rw [← htop]
    exact sup_le (sup_le hQ₀le hQ₁le) ((Ideal.span_singleton_le_iff_mem _).mpr hjB)
  exact (Ideal.IsPrime.ne_top ‹yB.IsPrime›) (top_le_iff.mp hle)

end S_ModularCurve_FullLevel_jInvChartInf_not_mem_of_exists_two_minimalPrimes_span_le_chartAlgInf_laurentBaseChange_gamma0_mul
end P2MW
export P2MW.S_ModularCurve_FullLevel_jInvChartInf_not_mem_of_exists_two_minimalPrimes_span_le_chartAlgInf_laurentBaseChange_gamma0_mul (solution)
