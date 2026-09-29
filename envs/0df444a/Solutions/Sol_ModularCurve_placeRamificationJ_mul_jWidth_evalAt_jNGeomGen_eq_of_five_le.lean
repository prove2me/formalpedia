-- Prove2me | solution 1 for ModularCurve.placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b54dd38a-3b01-5b2d-a2be-14e766bfd73c

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_algebraMap_sub_one_of_cast_natAbs_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField
import Theorems.Thm_KaehlerDifferential_span_D_eq_top_of_transcendental
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_ModularCurve_coe_eq_thetaL_div_of_D_eq_smul
import Theorems.Thm_ModularCurve_thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC
import Theorems.Thm_ModularCurve_thetaL_qExpand
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq_of_five_le
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange WeierstrassCurve.Affine.Point.instFinite GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective"

noncomputable section

namespace RoadDelta

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective KaehlerDifferential IsLocalRing"

section Values

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {a : v.toValuationSubring}
    (ha : a ∈ maximalIdeal v.toValuationSubring) (ha0 : (a : F) ≠ 0) : 0 < v.ord (a : F) := by
  by_contra hle
  push Not at hle
  have h0 : 0 ≤ v.ord (a : F) := v.ord_nonneg_of_mem a.2
  have heq : v.ord (a : F) = 0 := le_antisymm hle h0
  have hinv : (a : F)⁻¹ ∈ v.toValuationSubring := by
    rw [v.mem_iff_ord_nonneg (inv_ne_zero ha0), v.ord_inv, heq, neg_zero]
  have hunit : IsUnit a := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(a : F)⁻¹, hinv⟩, ?_⟩
    ext
    simp [mul_inv_cancel₀ ha0]
  exact (mem_maximalIdeal _).mp ha hunit

theorem sub_algebraMap_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (c : K) :
    f - algebraMap K F c ∈ v.toValuationSubring :=
  sub_mem hf (v.algebraMap_mem' c)

set_option maxHeartbeats 12800000 in
theorem residue_sub_algebraMap (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (c : K) :
    residue v.toValuationSubring ⟨f - algebraMap K F c, sub_algebraMap_mem v hf c⟩
      = algebraMap K v.ResidueField (v.evalAt f) - algebraMap K v.ResidueField c := by
  have hsplit : (⟨f - algebraMap K F c, sub_algebraMap_mem v hf c⟩ : v.toValuationSubring)
      = ⟨f, hf⟩ - algebraMap K v.toValuationSubring c := by
    apply Subtype.ext
    push_cast
    rw [v.coe_algebraMap]
  rw [hsplit, map_sub, v.algebraMap_evalAt hv hf]
  congr 1

set_option maxHeartbeats 12800000 in
theorem ord_sub_algebraMap_evalAt_pos (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (hne : f - algebraMap K F (v.evalAt f) ≠ 0) :
    0 < v.ord (f - algebraMap K F (v.evalAt f)) := by
  have hmem : (⟨f - algebraMap K F (v.evalAt f), sub_algebraMap_mem v hf _⟩ : v.toValuationSubring)
      ∈ maximalIdeal v.toValuationSubring := by
    rw [← residue_eq_zero_iff, residue_sub_algebraMap v hv hf, sub_self]
  exact ord_pos_of_mem_maximalIdeal v hmem hne

set_option maxHeartbeats 12800000 in
theorem ord_sub_algebraMap_eq_zero_of_ne (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) {c : K} (hc : c ≠ v.evalAt f) :
    v.ord (f - algebraMap K F c) = 0 := by
  have hnot : (⟨f - algebraMap K F c, sub_algebraMap_mem v hf c⟩ : v.toValuationSubring)
      ∉ maximalIdeal v.toValuationSubring := by
    rw [← residue_eq_zero_iff, residue_sub_algebraMap v hv hf, sub_eq_zero]
    exact fun h => hc (v.algebraMap_residueField_injective h).symm
  have hunit : IsUnit (⟨f - algebraMap K F c, sub_algebraMap_mem v hf c⟩ : v.toValuationSubring) := by
    by_contra h
    exact hnot ((mem_maximalIdeal _).mpr h)
  obtain ⟨u, hu⟩ := hunit
  have := v.ord_coe_unit u
  rw [hu] at this
  exact this

theorem isCurveOver_cast {L : Type*} [Field L] [Algebra K L]
    {E E' : IntermediateField K L} (h : E = E') (hE : IsCurveOver K ↥E) : IsCurveOver K ↥E' := by
  subst h; exact hE

theorem cast_ne_zero_of_lt (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] {n : ℕ} (h0 : n ≠ 0) (hn : n < p) :
    ((n : ℕ) : K) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff K p] at h
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h) (not_le.mpr hn)

end Values

section LevelN

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

theorem isIntegral_jNGeomGen :
    IsIntegral (Algebra.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))) (jNGeomGen K N) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  set A := Algebra.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N)) with hA
  have hjA : jGeomGen K N ∈ A := Algebra.subset_adjoin rfl
  let g : Polynomial ℤ →+* ↥A := Polynomial.eval₂RingHom (Int.castRingHom ↥A) ⟨jGeomGen K N, hjA⟩
  have hg : (algebraMap ↥A ↥(modularFunctionFieldC K N)).comp g
      = Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldC K N)) (jGeomGen K N) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [g]
  refine ⟨data.Φ.map g, data.monic.map g, ?_⟩
  rw [Polynomial.eval₂_map, hg]
  exact evalModularPair_jGeomGen_eq_zero K N data

theorem jNGeomGen_mem_of_jGeomGen_mem (x : Place K ↥(modularFunctionFieldC K N))
    (hj : jGeomGen K N ∈ x.toValuationSubring) : jNGeomGen K N ∈ x.toValuationSubring :=
  x.mem_toValuationSubring_of_isIntegral_adjoin hj (isIntegral_jNGeomGen K N)

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (hg : Function.Injective g) :
    Function.Injective (coeffMap g) := fun b c h =>
  HahnSeries.ext (funext fun k => hg (by rw [← coeffMap_coeff, ← coeffMap_coeff, h]))

theorem evalModularPair_jNGeomGen_jGeomGen_eq_zero (hN : 1 < N) (data : ModularPolynomialData N) :
    evalModularPair (jNGeomGen K N) (jGeomGen K N) data.Φ = 0 := by
  have hsymm := ModularPolynomialData.evalSymm_of_one_lt N hN data
  have haeval : ∀ x : LaurentSeries ℚ, (Polynomial.aeval (R := ℤ) x).toRingHom
      = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) x := fun x =>
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)
  have hQ : evalModularPair (jqNModC ℚ N) (jqModC ℚ) data.Φ = 0 := by
    have h := hsymm (jqNModC ℚ N) (jqModC ℚ)
    rw [haeval, haeval] at h
    change evalModularPair (jqNModC ℚ N) (jqModC ℚ) data.Φ = evalModularPair (jqModC ℚ) (jqNModC ℚ N) data.Φ at h
    rw [h]
    exact evalModularPair_jq_eq_zero ℚ data
  have hZ : evalModularPair (jqNModC ℤ N) (jqModC ℤ) data.Φ = 0 := by
    apply coeffMap_injective (Int.castRingHom ℚ) (Int.cast_injective)
    rw [map_evalModularPair, coeffMap_jqNModC, coeffMap_jqModC, hQ, map_zero]
  have hK : evalModularPair (jqNModC K N) (jqModC K) data.Φ = 0 := by
    have := congrArg (coeffMap (Int.castRingHom K)) hZ
    rwa [map_evalModularPair, coeffMap_jqNModC, coeffMap_jqModC, map_zero] at this
  have hval := map_evalModularPair (modularFunctionFieldC K N).val.toRingHom
    (jNGeomGen K N) (jGeomGen K N) data.Φ
  have hgen : (modularFunctionFieldC K N).val.toRingHom (jGeomGen K N) = jqModC K := rfl
  have hgenN : (modularFunctionFieldC K N).val.toRingHom (jNGeomGen K N) = jqNModC K N := rfl
  rw [hgen, hgenN, hK] at hval
  exact (map_eq_zero_iff _ (modularFunctionFieldC K N).val.toRingHom.injective).mp hval

theorem isIntegral_jGeomGen (hN : 1 < N) :
    IsIntegral (Algebra.adjoin K ({jNGeomGen K N} : Set ↥(modularFunctionFieldC K N))) (jGeomGen K N) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  set A := Algebra.adjoin K ({jNGeomGen K N} : Set ↥(modularFunctionFieldC K N)) with hA
  have hjA : jNGeomGen K N ∈ A := Algebra.subset_adjoin rfl
  let g : Polynomial ℤ →+* ↥A := Polynomial.eval₂RingHom (Int.castRingHom ↥A) ⟨jNGeomGen K N, hjA⟩
  have hg : (algebraMap ↥A ↥(modularFunctionFieldC K N)).comp g
      = Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldC K N)) (jNGeomGen K N) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [g]
  refine ⟨data.Φ.map g, data.monic.map g, ?_⟩
  rw [Polynomial.eval₂_map, hg]
  exact evalModularPair_jNGeomGen_jGeomGen_eq_zero K N hN data

theorem jGeomGen_mem_of_jNGeomGen_mem (x : Place K ↥(modularFunctionFieldC K N))
    (hj : jNGeomGen K N ∈ x.toValuationSubring) : jGeomGen K N ∈ x.toValuationSubring := by
  rcases Nat.lt_or_ge 1 N with hN | hN
  · exact x.mem_toValuationSubring_of_isIntegral_adjoin hj (isIntegral_jGeomGen K N hN)
  · have h1 : N = 1 := le_antisymm hN (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
    subst h1
    rwa [jNGeomGen_one] at hj

theorem toNat_ord_sub_evalAt_eq_zero (x : Place K ↥(modularFunctionFieldC K N)) (f : ↥(modularFunctionFieldC K N))
    (hf0 : f ≠ 0) (hf : f ∉ x.toValuationSubring) :
    (x.ord (f - algebraMap K ↥(modularFunctionFieldC K N) (x.evalAt f))).toNat = 0 := by
  have he : x.evalAt f = 0 := by
    rw [Place.evalAt, dif_neg hf]
  rw [he, map_zero, sub_zero]
  have : ¬ 0 ≤ x.ord f := fun h => hf ((x.mem_iff_ord_nonneg hf0).mpr h)
  exact Int.toNat_eq_zero.mpr (by omega)

end LevelN

section Theta

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

theorem thetaL_coeff' (x : LaurentSeries K) (n : ℤ) :
    (thetaL K x).coeff n = (n : K) * x.coeff n := by
  rw [thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp only [Nat.cast_one, sub_add_cancel, Ring.choose_one_right, zsmul_eq_mul]

theorem thetaL_jqModC_ne_zero : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries K => x.coeff (-1)) h
  beta_reduce at h1
  rw [thetaL_coeff', coeff_jqModC_neg_one, HahnSeries.coeff_zero] at h1
  norm_num at h1

variable {K N} in
theorem thetaL_jqNModC_ne_zero (hN : (N : K) ≠ 0) : thetaL K (jqNModC K N) ≠ 0 := by
  rw [jqNModC, thetaL_qExpand]
  refine mul_ne_zero ?_ ?_
  · intro h
    have := congrArg (fun x : LaurentSeries K => x.coeff 0) h
    simp only [HahnSeries.coeff_single_same, HahnSeries.coeff_zero] at this
    exact hN this
  · exact (map_ne_zero (qExpand K N)).mpr (thetaL_jqModC_ne_zero K)

end Theta

section Main

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
  (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]

theorem jWidth_mul (hK : (1728 : K) ≠ 0) (x : K) (ρ o1 o2 : ℤ)
    (h1 : o1 = if x = 0 then ρ else 0) (h2 : o2 = if x = 1728 then ρ else 0) :
    (jWidth x : ℤ) * (6 * ρ - 4 * o1 - 3 * o2) = 6 * ρ := by
  by_cases h0 : x = 0
  · have hx1 : x ≠ 1728 := by rw [h0]; exact fun h => hK h.symm
    rw [jWidth_of_eq_zero h0, h1, h2, if_pos h0, if_neg hx1]; push_cast; ring
  · by_cases hx1 : x = 1728
    · rw [jWidth_of_eq_1728 hx1 h0, h1, h2, if_neg h0, if_pos hx1]; push_cast; ring
    · rw [jWidth_of_ne h0 hx1, h1, h2, if_neg h0, if_neg hx1]; push_cast; ring

theorem c_le_six (hK : (1728 : K) ≠ 0) (x : K) (ρ o1 o2 : ℤ) (hρ : ρ ≤ (jWidth x : ℤ))
    (h1 : o1 = if x = 0 then ρ else 0) (h2 : o2 = if x = 1728 then ρ else 0) :
    6 * ρ - 4 * o1 - 3 * o2 ≤ 6 := by
  by_cases h0 : x = 0
  · have hx1 : x ≠ 1728 := by rw [h0]; exact fun h => hK h.symm
    rw [jWidth_of_eq_zero h0] at hρ
    rw [h1, h2, if_pos h0, if_neg hx1]; push_cast at hρ; linarith
  · by_cases hx1 : x = 1728
    · rw [jWidth_of_eq_1728 hx1 h0] at hρ
      rw [h1, h2, if_neg h0, if_pos hx1]; push_cast at hρ; linarith
    · rw [jWidth_of_ne h0 hx1] at hρ
      rw [h1, h2, if_neg h0, if_neg hx1]; push_cast at hρ; linarith

theorem le_three_of_c_le_six (hK : (1728 : K) ≠ 0) (x : K) (ρ o1 o2 : ℤ) (hρ : 0 < ρ)
    (h1 : o1 = if x = 0 then ρ else 0) (h2 : o2 = if x = 1728 then ρ else 0)
    (h : 6 * ρ - 4 * o1 - 3 * o2 ≤ 6) : ρ ≤ 3 := by
  by_cases h0 : x = 0
  · rw [h1, if_pos h0] at h
    have hx1 : x ≠ 1728 := by rw [h0]; exact fun h => hK h.symm
    rw [h2, if_neg hx1] at h; linarith
  · rw [h1, if_neg h0] at h
    by_cases hx1 : x = 1728
    · rw [h2, if_pos hx1] at h; linarith
    · rw [h2, if_neg hx1] at h; linarith

set_option maxHeartbeats 16000000 in
include hp5 hpN in
theorem main (w : Place K ↥(modularFunctionFieldC K N)) :
    placeRamificationJ N w * jWidth (w.evalAt (jNGeomGen K N))
      = (w.ord (jNGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) (w.evalAt (jNGeomGen K N)))).toNat
          * jWidth (w.evalAt (jGeomGen K N)) := by
  classical
  haveI : PerfectField K := IsAlgClosed.perfectField K
  set F := ↥(modularFunctionFieldC K N)
  have hN : (N : K) ≠ 0 := fun h0 => hpN ((CharP.cast_eq_zero_iff K p N).1 h0)
  have hp5' : (5 : ℕ) ≤ p := hp5

  have h1728 : (1728 : K) ≠ 0 := by
    have h2 : ((2 : ℕ) : K) ≠ 0 := cast_ne_zero_of_lt p K (by norm_num) (by omega)
    have h3 : ((3 : ℕ) : K) ≠ 0 := cast_ne_zero_of_lt p K (by norm_num) (by omega)
    have : (1728 : K) = ((2 : ℕ) : K) ^ 6 * ((3 : ℕ) : K) ^ 3 := by push_cast; norm_num
    rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  set j : F := jGeomGen K N with hjdef
  set jN : F := jNGeomGen K N with hjNdef
  by_cases haff : j ∈ w.toValuationSubring
  swap
  ·
    have hjN : jN ∉ w.toValuationSubring := fun h => haff (jGeomGen_mem_of_jNGeomGen_mem K N w h)
    have hj0 : j ≠ 0 := by simpa using jGeomGen_sub_algebraMap_ne_zero K N 0
    have hjN0 : jN ≠ 0 := by simpa using jNGeomGen_sub_algebraMap_ne_zero K N 0
    unfold placeRamificationJ
    rw [toNat_ord_sub_evalAt_eq_zero K N w _ hj0 haff, toNat_ord_sub_evalAt_eq_zero K N w _ hjN0 hjN,
      zero_mul, zero_mul]

  have hjNmem : jN ∈ w.toValuationSubring := jNGeomGen_mem_of_jGeomGen_mem K N w haff
  have hw : IsAffineGeomPlace K N w := ⟨haff, hjNmem⟩
  obtain ⟨data⟩ := nonempty_modularPolynomialData N

  obtain ⟨hfin, hsep⟩ := finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC K N data
    (isSeparable_jqNModC_of_natCast_ne_zero K N hN)
  haveI : FiniteDimensional ↥(IntermediateField.adjoin K ({j} : Set F)) F := hfin
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin K ({j} : Set F)) F := hsep
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K ({j} : Set F)) F := Algebra.IsAlgebraic.of_finite _ _

  haveI : IsCurveOver K F :=
    isCurveOver_cast (modularFunctionFieldC_eq_modularFunctionFieldFullC K p N hpN).symm
      (isCurveOver_modularFunctionFieldFullC K N)
  have hrat : w.IsRational := (w.isRational_iff_deg_eq_one).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed w)

  set a : K := w.evalAt j with hadef
  set a' : K := w.evalAt jN with ha'def
  have hra : 0 < w.ord (j - algebraMap K F a) :=
    ord_sub_algebraMap_evalAt_pos w hrat haff (jGeomGen_sub_algebraMap_ne_zero K N a)
  have hra' : 0 < w.ord (jN - algebraMap K F a') :=
    ord_sub_algebraMap_evalAt_pos w hrat hjNmem (jNGeomGen_sub_algebraMap_ne_zero K N a')
  set r : ℤ := w.ord (j - algebraMap K F a) with hrdef
  set rN : ℤ := w.ord (jN - algebraMap K F a') with hrNdef
  have hR : (placeRamificationJ N w : ℤ) = r := by
    show (((w.ord (jGeomGen K N - algebraMap K F (w.evalAt (jGeomGen K N)))).toNat : ℕ) : ℤ) = r
    rw [Int.toNat_of_nonneg hra.le]
  have hRN : (((w.ord (jN - algebraMap K F a')).toNat : ℕ) : ℤ) = rN := Int.toNat_of_nonneg hra'.le

  have hR0 : 0 < placeRamificationJ N w := by
    have : (0 : ℤ) < (placeRamificationJ N w : ℤ) := by rw [hR]; exact hra
    exact_mod_cast this
  have hdvd : placeRamificationJ N w ∣ jWidth a := placeRamificationJ_dvd_jWidth_of_ord_pos (q := p) hp5 hpN hR0
  have hrle : r ≤ (jWidth a : ℤ) := by
    rw [← hR]; exact_mod_cast Nat.le_of_dvd (jWidth_pos a) hdvd
  have hW3 : (jWidth a : ℤ) ≤ 3 := by
    have hwle : jWidth a ≤ 3 := by unfold jWidth; split_ifs <;> omega
    exact_mod_cast hwle
  have hW3' : (jWidth a' : ℤ) ≤ 3 := by
    have hwle : jWidth a' ≤ 3 := by unfold jWidth; split_ifs <;> omega
    exact_mod_cast hwle
  have htame : (((w.ord (j - algebraMap K F a)).natAbs : ℕ) : K) ≠ 0 := by
    have h1 : (w.ord (j - algebraMap K F a)).natAbs = placeRamificationJ N w := by
      rw [← Int.natAbs_natCast (placeRamificationJ N w), hR]
    rw [h1]
    exact cast_ne_zero_of_lt p K hR0.ne' (by
      have : (placeRamificationJ N w : ℤ) ≤ 3 := by rw [hR]; exact hrle.trans hW3
      omega)

  have hθj : thetaL K (jqModC K) ≠ 0 := thetaL_jqModC_ne_zero K
  have hθjN : thetaL K (jqNModC K N) ≠ 0 := thetaL_jqNModC_ne_zero hN
  have hhmem : thetaL K (jqNModC K N) / thetaL K (jqModC K) ∈ modularFunctionFieldC K N :=
    thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC K p N hpN (jqNModC K N) (jqNModC_mem K N)
  set h : F := ⟨thetaL K (jqNModC K N) / thetaL K (jqModC K), hhmem⟩ with hhdef
  have hh : (h : LaurentSeries K) * thetaL K (jqModC K) = thetaL K (jqNModC K N) := div_mul_cancel₀ _ hθj
  have hh0 : h ≠ 0 := by
    intro h0
    have : (h : LaurentSeries K) = 0 := by rw [h0]; rfl
    rw [this, zero_mul] at hh
    exact hθjN hh.symm
  have hjtr : Transcendental K j := by
    intro halg
    exact transcendental_jqModC K (IntermediateField.isAlgebraic_iff.mp halg)
  have hDj : D K F j ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K j hjtr
  have hspan := KaehlerDifferential.span_D_eq_top_of_transcendental K j hjtr
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : F, c₀ • D K F j = D K F jN := by
    have : D K F jN ∈ Submodule.span F ({D K F j} : Set (Ω[F⁄K])) := by rw [hspan]; exact Submodule.mem_top
    exact Submodule.mem_span_singleton.mp this
  have hc₀h : c₀ = h := by
    apply Subtype.ext
    rw [coe_eq_thetaL_div_of_D_eq_smul K (modularFunctionFieldC K N) jN j c₀ hc₀.symm hθj]
    rfl
  have hD : D K F jN = h • D K F j := by rw [← hc₀h]; exact hc₀.symm
  have hDjN : D K F jN ≠ 0 := by rw [hD]; exact smul_ne_zero hh0 hDj

  have hδ : w.ordDiff (D K F j) = r - 1 :=
    Place.ordDiff_D_eq_ord_sub_algebraMap_sub_one_of_cast_natAbs_ne_zero j w hra.ne' htame
  have hδN : w.ordDiff (D K F jN) = w.ord h + (r - 1) := by
    rw [hD, Place.ordDiff_smul_of_perfectField j w hh0 hDj, hδ]
  have hδN_le : rN - 1 ≤ w.ordDiff (D K F jN) := by
    have hDsub : D K F (jN - algebraMap K F a') = D K F jN := by
      rw [map_sub, Derivation.map_algebraMap, sub_zero]
    have := Place.ord_sub_one_le_ordDiff_D_of_perfectField j w (f := jN - algebraMap K F a') (by rw [hDsub]; exact hDjN)
    rwa [hDsub] at this

  have hC2 := six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace p hp5 N hpN K h hh w hw

  have hoj : w.ord j = if a = 0 then r else 0 := by
    split_ifs with h0
    · rw [hrdef, h0, map_zero, sub_zero]
    · have := ord_sub_algebraMap_eq_zero_of_ne w hrat haff (c := 0) (fun h => h0 h.symm)
      rwa [map_zero, sub_zero] at this
  have hoj' : w.ord (j - algebraMap K F 1728) = if a = 1728 then r else 0 := by
    split_ifs with h1
    · rw [hrdef, h1]
    · exact ord_sub_algebraMap_eq_zero_of_ne w hrat haff (fun h => h1 h.symm)
  have hojN : w.ord jN = if a' = 0 then rN else 0 := by
    split_ifs with h0
    · rw [hrNdef, h0, map_zero, sub_zero]
    · have := ord_sub_algebraMap_eq_zero_of_ne w hrat hjNmem (c := 0) (fun h => h0 h.symm)
      rwa [map_zero, sub_zero] at this
  have hojN' : w.ord (jN - algebraMap K F 1728) = if a' = 1728 then rN else 0 := by
    split_ifs with h1
    · rw [hrNdef, h1]
    · exact ord_sub_algebraMap_eq_zero_of_ne w hrat hjNmem (fun h => h1 h.symm)

  have hC2' : 6 * w.ord h = 4 * w.ord jN + 3 * w.ord (jN - algebraMap K F 1728) - 4 * w.ord j
      - 3 * w.ord (j - algebraMap K F 1728) := by linarith [hC2]
  have hineq : 6 * rN - 4 * w.ord jN - 3 * w.ord (jN - algebraMap K F 1728)
      ≤ 6 * r - 4 * w.ord j - 3 * w.ord (j - algebraMap K F 1728) := by
    have e1 : w.ordDiff (D K F jN) = w.ord h + (r - 1) := hδN
    linarith [hδN_le, hC2']
  have hca : 6 * r - 4 * w.ord j - 3 * w.ord (j - algebraMap K F 1728) ≤ 6 :=
    c_le_six K h1728 a r _ _ hrle hoj hoj'
  have hrN3 : rN ≤ 3 := le_three_of_c_le_six K h1728 a' rN _ _ hra' hojN hojN' (hineq.trans hca)
  have htameN : (((w.ord (jN - algebraMap K F a')).natAbs : ℕ) : K) ≠ 0 := by
    have h1 : (((w.ord (jN - algebraMap K F a')).natAbs : ℕ) : ℤ) = rN := by
      rw [← hrNdef]; exact Int.natAbs_of_nonneg hra'.le
    have h2 : (w.ord (jN - algebraMap K F a')).natAbs ≤ 3 := by omega
    have h3 : (w.ord (jN - algebraMap K F a')).natAbs ≠ 0 := by omega
    exact cast_ne_zero_of_lt p K h3 (by omega)
  have hδN' : w.ordDiff (D K F jN) = rN - 1 :=
    Place.ordDiff_D_eq_ord_sub_algebraMap_sub_one_of_cast_natAbs_ne_zero j w hra'.ne' htameN
  have heq : 6 * rN - 4 * w.ord jN - 3 * w.ord (jN - algebraMap K F 1728)
      = 6 * r - 4 * w.ord j - 3 * w.ord (j - algebraMap K F 1728) := by
    linarith [hδN, hδN', hC2']

  have e1 := jWidth_mul K h1728 a r _ _ hoj hoj'
  have e2 := jWidth_mul K h1728 a' rN _ _ hojN hojN'
  rw [heq] at e2
  have hfinal' : 6 * (r * (jWidth a' : ℤ)) = 6 * (rN * (jWidth a : ℤ)) := by
    linear_combination (-(jWidth a' : ℤ)) * e1 + (jWidth a : ℤ) * e2
  have hfin : r * (jWidth a' : ℤ) = rN * (jWidth a : ℤ) := by linarith

  have : ((placeRamificationJ N w * jWidth a' : ℕ) : ℤ)
      = (((w.ord (jN - algebraMap K F a')).toNat * jWidth a : ℕ) : ℤ) := by
    push_cast
    rw [hR, hRN]
    exact hfin
  exact_mod_cast this

end Main

end RoadDelta

end

p2m_open "ModularCurve~coeffMap_injective" in open AlgebraicCurve  in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k]
    (w : Place k ↥(modularFunctionFieldC k N)) :
    placeRamificationJ N w * jWidth (w.evalAt (jNGeomGen k N))
      = (w.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (w.evalAt (jNGeomGen k N)))).toNat
          * jWidth (w.evalAt (jGeomGen k N)) :=
  RoadDelta.main p hp5 N hpN k w

end S_ModularCurve_placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq_of_five_le
end P2MW
export P2MW.S_ModularCurve_placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq_of_five_le (solution)
