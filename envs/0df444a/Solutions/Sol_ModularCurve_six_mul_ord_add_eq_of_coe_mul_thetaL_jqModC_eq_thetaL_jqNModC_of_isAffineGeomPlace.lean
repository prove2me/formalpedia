-- Prove2me | solution 1 for ModularCurve.six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/73ddb588-d629-5f0f-a710-96f4ca76f2f2

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_algebraMap_sub_one_of_cast_natAbs_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField
import Theorems.Thm_KaehlerDifferential_span_D_eq_top_of_transcendental
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_ModularCurve_coe_eq_thetaL_div_of_D_eq_smul
import Theorems.Thm_ModularCurve_thetaL_qExpand
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
import Theorems.Thm_ModularCurve_natAbs_ord_jGeomGen_cast_ne_zero_of_ord_neg
import Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_neg
import Definitions.Def_SwdAlgebra
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_EisensteinSeries_ramanujan_system_qExpansion_int
import Theorems.Thm_ModularCurve_eisenstein4_cube_sub_mk_sq
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_theta_mul
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_LaurentSeries_HeckeV
import Theorems.Thm_ModularCurve_exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModPForms_heckeV_mem_modPMod_mul
import Theorems.Thm_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
import Theorems.Thm_LaurentSeries_heckeV_eq_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois HahnSeries.ramScale_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU"
p2m_attr_erase "simp" "ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

set_option autoImplicit false

noncomputable section

namespace ATHETA2Q

p2m_open "ModularCurve~coeffMap_injective PowerSeries"

set_option maxHeartbeats 6400000 in

def P : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ)

set_option maxHeartbeats 6400000 in

def R : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5

set_option maxHeartbeats 6400000 in

def Dq (g : PowerSeries ℤ) : PowerSeries ℤ := PowerSeries.X * PowerSeries.derivative ℤ g

set_option maxHeartbeats 6400000 in
theorem Dq_add (f g : PowerSeries ℤ) : Dq (f + g) = Dq f + Dq g := by
  unfold Dq; rw [map_add, mul_add]

set_option maxHeartbeats 6400000 in
theorem Dq_sub (f g : PowerSeries ℤ) : Dq (f - g) = Dq f - Dq g := by
  unfold Dq; rw [map_sub, mul_sub]

set_option maxHeartbeats 6400000 in
theorem Dq_neg (f : PowerSeries ℤ) : Dq (-f) = -Dq f := by
  unfold Dq; rw [map_neg, mul_neg]

set_option maxHeartbeats 6400000 in
theorem Dq_mul (f g : PowerSeries ℤ) : Dq (f * g) = Dq f * g + f * Dq g := by
  unfold Dq; rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring

set_option maxHeartbeats 6400000 in
theorem Dq_pow (f : PowerSeries ℤ) (n : ℕ) : Dq (f ^ n) = n * f ^ (n - 1) * Dq f := by
  unfold Dq; rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]; ring

set_option maxHeartbeats 6400000 in
theorem Dq_X : Dq PowerSeries.X = PowerSeries.X := by
  unfold Dq; rw [PowerSeries.derivative_X, mul_one]

set_option maxHeartbeats 6400000 in
theorem Dq_natCast (n : ℕ) : Dq (n : PowerSeries ℤ) = 0 := by
  unfold Dq; rw [Derivation.map_natCast, mul_zero]

set_option maxHeartbeats 6400000 in
theorem Dq_natCast_mul (n : ℕ) (f : PowerSeries ℤ) : Dq ((n : PowerSeries ℤ) * f) = n * Dq f := by
  rw [Dq_mul, Dq_natCast, zero_mul, zero_add]

set_option maxHeartbeats 6400000 in

theorem ramanujan :
    3 * Dq eisenstein4 = P * eisenstein4 - R ∧ 2 * Dq R = P * R - eisenstein4 ^ 2 := by
  obtain ⟨-, h2, h3⟩ := EisensteinSeries.ramanujan_system_qExpansion_int P eisenstein4 R rfl rfl rfl
  exact ⟨h2, h3⟩

set_option maxHeartbeats 6400000 in

def Δ' : PowerSeries ℤ := PowerSeries.X * dedekindEtaUnit

set_option maxHeartbeats 6400000 in
theorem disc : (1728 : PowerSeries ℤ) * Δ' = eisenstein4 ^ 3 - R ^ 2 := by
  have h : eisenstein4 ^ 3 - R ^ 2 = 1728 * (PowerSeries.X * dedekindEtaUnit) :=
    ModularCurve.eisenstein4_cube_sub_mk_sq
  rw [h]; rfl

set_option maxHeartbeats 6400000 in
theorem natCast_ne_zero {n : ℕ} (hn : n ≠ 0) : (n : PowerSeries ℤ) ≠ 0 := by
  intro h
  have h' := congrArg (PowerSeries.constantCoeff (R := ℤ)) h
  rw [map_natCast, map_zero] at h'
  exact hn (by exact_mod_cast h')

set_option maxHeartbeats 6400000 in
theorem X_ne_zero' : (PowerSeries.X : PowerSeries ℤ) ≠ 0 := PowerSeries.X_ne_zero

set_option maxHeartbeats 6400000 in
theorem dedekindEtaUnit_ne_zero : (dedekindEtaUnit : PowerSeries ℤ) ≠ 0 :=
  left_ne_zero_of_mul_eq_one dedekindEtaUnit_mul_inv

set_option maxHeartbeats 6400000 in
theorem Δ'_ne_zero : Δ' ≠ 0 := mul_ne_zero X_ne_zero' dedekindEtaUnit_ne_zero

set_option maxHeartbeats 6400000 in

theorem Dq_Δ' : Dq Δ' = P * Δ' := by
  obtain ⟨hQ, hR⟩ := ramanujan
  have h1728 : ((1728 : ℕ) : PowerSeries ℤ) = 1728 := by norm_cast
  have h1 : Dq ((1728 : PowerSeries ℤ) * Δ') = 1728 * Dq Δ' := by
    rw [← h1728, Dq_natCast_mul]
  have h2 : Dq (eisenstein4 ^ 3 - R ^ 2) = P * (eisenstein4 ^ 3 - R ^ 2) := by
    rw [Dq_sub, Dq_pow, Dq_pow]
    push_cast
    linear_combination (eisenstein4 ^ 2) * hQ - R * hR
  have h3 : (1728 : PowerSeries ℤ) * Dq Δ' = 1728 * (P * Δ') := by
    rw [← h1, disc, h2, ← disc]; ring
  exact mul_left_cancel₀ (h1728 ▸ natCast_ne_zero (by norm_num)) h3

set_option maxHeartbeats 6400000 in

theorem jNum_mul_Δ' : jNum * Δ' = PowerSeries.X * eisenstein4 ^ 3 := by
  show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) = _
  linear_combination (eisenstein4 ^ 3 * PowerSeries.X) * dedekindEtaUnit_mul_inv

set_option maxHeartbeats 6400000 in

def T₀ : PowerSeries ℤ := Dq jNum - jNum

set_option maxHeartbeats 6400000 in
theorem T₀_mul_Δ' : T₀ * Δ' = -(PowerSeries.X * eisenstein4 ^ 2 * R) := by
  obtain ⟨hQ, hR⟩ := ramanujan

  have h1 : Dq (jNum * Δ') = Dq jNum * Δ' + P * (jNum * Δ') := by
    rw [Dq_mul, Dq_Δ']; ring
  have h2 : Dq (PowerSeries.X * eisenstein4 ^ 3) =
      PowerSeries.X * eisenstein4 ^ 3 + PowerSeries.X * eisenstein4 ^ 2 * (3 * Dq eisenstein4) := by
    rw [Dq_mul, Dq_X, Dq_pow]; push_cast; ring
  have h3 : Dq jNum * Δ' = PowerSeries.X * eisenstein4 ^ 3 - PowerSeries.X * eisenstein4 ^ 2 * R := by
    have h := h1
    rw [jNum_mul_Δ', h2, hQ] at h
    linear_combination -h
  unfold T₀
  rw [sub_mul, h3, jNum_mul_Δ']; ring

set_option maxHeartbeats 6400000 in
theorem six_mul_Dq_T₀_mul_Δ' :
    6 * (Dq T₀ * Δ') =
      -6 * (PowerSeries.X * eisenstein4 ^ 2 * R)
        - 4 * (PowerSeries.X * eisenstein4 * R) * (P * eisenstein4 - R)
        - 3 * (PowerSeries.X * eisenstein4 ^ 2) * (P * R - eisenstein4 ^ 2)
        + 6 * P * (PowerSeries.X * eisenstein4 ^ 2 * R) := by
  obtain ⟨hQ, hR⟩ := ramanujan
  have h1 : Dq (T₀ * Δ') = Dq T₀ * Δ' + P * (T₀ * Δ') := by
    rw [Dq_mul, Dq_Δ']; ring
  have h2 : 6 * Dq (PowerSeries.X * eisenstein4 ^ 2 * R) =
      6 * (PowerSeries.X * eisenstein4 ^ 2 * R)
        + 4 * (PowerSeries.X * eisenstein4 * R) * (3 * Dq eisenstein4)
        + 3 * (PowerSeries.X * eisenstein4 ^ 2) * (2 * Dq R) := by
    rw [Dq_mul, Dq_mul, Dq_X, Dq_pow]; push_cast; ring
  have h3 : 6 * Dq (T₀ * Δ') = -(6 * Dq (PowerSeries.X * eisenstein4 ^ 2 * R)) := by
    rw [T₀_mul_Δ', Dq_neg]; ring
  rw [h2, hQ, hR, h1, T₀_mul_Δ'] at h3
  linear_combination h3

set_option maxHeartbeats 6400000 in
theorem jNum_sub_mul_Δ' :
    (jNum - 1728 * PowerSeries.X) * Δ' = PowerSeries.X * R ^ 2 := by
  linear_combination jNum_mul_Δ' - PowerSeries.X * disc

set_option maxHeartbeats 6400000 in
theorem seven_jNum_sub_mul_Δ' :
    (7 * jNum - 6912 * PowerSeries.X) * Δ' =
      3 * (PowerSeries.X * eisenstein4 ^ 3) + 4 * (PowerSeries.X * R ^ 2) := by
  linear_combination 7 * jNum_mul_Δ' - 4 * PowerSeries.X * disc

set_option maxHeartbeats 6400000 in

theorem integer_identity :
    P * T₀ * jNum * (jNum - 1728 * PowerSeries.X) =
      6 * (Dq T₀ - T₀) * jNum * (jNum - 1728 * PowerSeries.X)
        - T₀ ^ 2 * (7 * jNum - 6912 * PowerSeries.X) := by
  refine mul_left_cancel₀ (pow_ne_zero 3 Δ'_ne_zero) ?_
  have eL : Δ' ^ 3 * (P * T₀ * jNum * (jNum - 1728 * PowerSeries.X)) =
      P * (T₀ * Δ') * (jNum * Δ') * ((jNum - 1728 * PowerSeries.X) * Δ') := by ring
  have eR : Δ' ^ 3 * (6 * (Dq T₀ - T₀) * jNum * (jNum - 1728 * PowerSeries.X)
        - T₀ ^ 2 * (7 * jNum - 6912 * PowerSeries.X)) =
      (6 * (Dq T₀ * Δ') - 6 * (T₀ * Δ')) * (jNum * Δ') * ((jNum - 1728 * PowerSeries.X) * Δ')
        - (T₀ * Δ') ^ 2 * ((7 * jNum - 6912 * PowerSeries.X) * Δ') := by ring
  rw [eL, eR, six_mul_Dq_T₀_mul_Δ', T₀_mul_Δ', jNum_mul_Δ', jNum_sub_mul_Δ', seven_jNum_sub_mul_Δ']
  ring

set_option maxHeartbeats 6400000 in

theorem jNum_sub_mul_Δ'' : (jNum - 1728 * PowerSeries.X) * Δ' = PowerSeries.X * R ^ 2 := jNum_sub_mul_Δ'

set_option maxHeartbeats 6400000 in

theorem X_mul_T₀_pow_six :
    PowerSeries.X * T₀ ^ 6 = jNum ^ 4 * (jNum - 1728 * PowerSeries.X) ^ 3 * Δ' := by
  apply mul_right_cancel₀ (pow_ne_zero 6 Δ'_ne_zero)
  have h1 := T₀_mul_Δ'
  have h2 := jNum_mul_Δ'
  have h3 := jNum_sub_mul_Δ'
  calc PowerSeries.X * T₀ ^ 6 * Δ' ^ 6 = PowerSeries.X * (T₀ * Δ') ^ 6 := by ring
    _ = PowerSeries.X * (-(PowerSeries.X * eisenstein4 ^ 2 * R)) ^ 6 := by rw [h1]
    _ = (jNum * Δ') ^ 4 * ((jNum - 1728 * PowerSeries.X) * Δ') ^ 3 := by rw [h2, h3]; ring
    _ = jNum ^ 4 * (jNum - 1728 * PowerSeries.X) ^ 3 * Δ' * Δ' ^ 6 := by ring

section Field

variable (K : Type) [Field K]

set_option maxHeartbeats 6400000 in

def ι : PowerSeries ℤ →+* LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map (Int.castRingHom K))

set_option maxHeartbeats 6400000 in
theorem ι_apply (g : PowerSeries ℤ) :
    ι K g = HahnSeries.ofPowerSeries ℤ K (g.map (Int.castRingHom K)) := rfl

set_option maxHeartbeats 6400000 in
theorem ι_coeff_natCast (g : PowerSeries ℤ) (m : ℕ) :
    (ι K g).coeff (m : ℤ) = ((PowerSeries.coeff m g : ℤ) : K) := by
  rw [ι_apply, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]; rfl

set_option maxHeartbeats 6400000 in
theorem ι_coeff_of_neg (g : PowerSeries ℤ) {n : ℤ} (hn : n < 0) : (ι K g).coeff n = 0 := by
  rw [ι_apply]; exact ModularCurve.ofPowerSeries_coeff_of_neg _ hn

set_option maxHeartbeats 6400000 in
theorem thetaL_coeff (f : LaurentSeries K) (n : ℤ) : (thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [thetaL_apply, ModularCurve.theta_coeff, zsmul_eq_mul]

set_option maxHeartbeats 6400000 in

theorem thetaL_ι (g : PowerSeries ℤ) : thetaL K (ι K g) = ι K (Dq g) := by
  ext n
  rw [thetaL_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [ι_coeff_of_neg K g hn, ι_coeff_of_neg K _ hn, mul_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [ι_coeff_natCast, ι_coeff_natCast, Dq]
    cases m with
    | zero => rw [PowerSeries.coeff_zero_X_mul]; simp
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      push_cast; ring

set_option maxHeartbeats 6400000 in

theorem thetaL_single_neg_one :
    thetaL K (HahnSeries.single (-1 : ℤ) (1 : K)) = -HahnSeries.single (-1 : ℤ) (1 : K) := by
  ext n
  rw [thetaL_coeff, HahnSeries.coeff_neg, HahnSeries.coeff_single]
  split_ifs with h
  · subst h; simp
  · rw [mul_zero, neg_zero]

set_option maxHeartbeats 6400000 in
theorem single_neg_one_mul_ι_X :
    HahnSeries.single (-1 : ℤ) (1 : K) * ι K PowerSeries.X = 1 := by
  rw [ι_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X, HahnSeries.single_mul_single]
  norm_num

set_option maxHeartbeats 6400000 in
theorem jqModC_eq : jqModC K = HahnSeries.single (-1 : ℤ) (1 : K) * ι K jNum := rfl

set_option maxHeartbeats 6400000 in
theorem ofPowerSeries_qP : HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) = ι K P := rfl

set_option maxHeartbeats 6400000 in

theorem thetaL_jqModC : thetaL K (jqModC K) = HahnSeries.single (-1 : ℤ) (1 : K) * ι K T₀ := by
  rw [jqModC_eq, show thetaL K (HahnSeries.single (-1 : ℤ) (1 : K) * ι K jNum) =
      HahnSeries.single (-1 : ℤ) (1 : K) * thetaL K (ι K jNum) + ι K jNum *
        thetaL K (HahnSeries.single (-1 : ℤ) (1 : K)) from ModularCurve.theta_mul _ _,
    thetaL_ι, thetaL_single_neg_one, T₀, map_sub]
  ring

set_option maxHeartbeats 6400000 in

theorem thetaL_thetaL_jqModC :
    thetaL K (thetaL K (jqModC K)) =
      HahnSeries.single (-1 : ℤ) (1 : K) * (ι K (Dq T₀) - ι K T₀) := by
  rw [thetaL_jqModC, show thetaL K (HahnSeries.single (-1 : ℤ) (1 : K) * ι K T₀) =
      HahnSeries.single (-1 : ℤ) (1 : K) * thetaL K (ι K T₀) + ι K T₀ *
        thetaL K (HahnSeries.single (-1 : ℤ) (1 : K)) from ModularCurve.theta_mul _ _,
    thetaL_ι, thetaL_single_neg_one]
  ring

set_option maxHeartbeats 6400000 in

theorem identity_K :
    ι K P * ι K T₀ * ι K jNum * (ι K jNum - 1728 * ι K PowerSeries.X) =
      6 * (ι K (Dq T₀) - ι K T₀) * ι K jNum * (ι K jNum - 1728 * ι K PowerSeries.X)
        - ι K T₀ ^ 2 * (7 * ι K jNum - 6912 * ι K PowerSeries.X) := by
  have h := congrArg (ι K) integer_identity
  simp only [map_mul, map_sub, map_pow, map_ofNat] at h
  exact h

set_option maxHeartbeats 6400000 in

theorem thetaL_jqModC_pow_six :
    thetaL K (jqModC K) ^ 6 = jqModC K ^ 4 * (jqModC K - 1728) ^ 3 * ι K Δ' := by
  have hsX := single_neg_one_mul_ι_X K
  have hZ := congrArg (ι K) X_mul_T₀_pow_six
  simp only [map_mul, map_sub, map_pow, map_ofNat] at hZ
  rw [thetaL_jqModC, jqModC_eq]
  rw [show (1728 : LaurentSeries K) = 1728 * (HahnSeries.single (-1 : ℤ) (1 : K) * ι K PowerSeries.X) by rw [hsX, mul_one]]
  calc (HahnSeries.single (-1 : ℤ) (1 : K) * ι K T₀) ^ 6
        = (HahnSeries.single (-1 : ℤ) (1 : K)) ^ 6 * ι K T₀ ^ 6 * (HahnSeries.single (-1 : ℤ) (1 : K) * ι K PowerSeries.X) := by
          rw [hsX]; ring
    _ = (HahnSeries.single (-1 : ℤ) (1 : K)) ^ 7 * (ι K PowerSeries.X * ι K T₀ ^ 6) := by ring
    _ = (HahnSeries.single (-1 : ℤ) (1 : K)) ^ 7 * (ι K jNum ^ 4 * (ι K jNum - 1728 * ι K PowerSeries.X) ^ 3 * ι K Δ') := by rw [hZ]
    _ = _ := by ring

end Field

end ATHETA2Q

end

namespace C2B

p2m_open "ModularCurve~coeffMap_injective P2MW.S_ModularCurve_six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace.ATHETA2Q"

set_option maxHeartbeats 6400000 in

def ΔbarPS (K : Type) [Field K] : PowerSeries K :=
  (PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom K)

set_option maxHeartbeats 6400000 in
theorem ι_Δ' (K : Type) [Field K] : ι K Δ' = HahnSeries.ofPowerSeries ℤ K (ΔbarPS K) := rfl

set_option maxHeartbeats 6400000 in
theorem heckeDiagMatrix_one : ModularForm.heckeDiagMatrix 1 = 1 := by
  unfold ModularForm.heckeDiagMatrix
  rw [dif_neg one_ne_zero]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularForm.upperTriangularGL]

set_option maxHeartbeats 6400000 in
theorem ΔbarPS_mem (K : Type) [Field K] : ΔbarPS K ∈ ModPForms.modPMod 1 12 K := by
  obtain ⟨D, hD⟩ := ModularCurve.exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix 1
  rw [heckeDiagMatrix_one, SlashAction.slash_one] at hD
  refine Submodule.subset_span ⟨D, fun n => PowerSeries.coeff n (PowerSeries.X * dedekindEtaUnit), fun n => ?_, ?_⟩
  · show (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑D) = _
    rw [hD, ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit, PowerSeries.coeff_map]
    rfl
  · ext n
    simp only [ΔbarPS, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    rfl

set_option maxHeartbeats 6400000 in
theorem heckeV_ΔbarPS_mem (N : ℕ) [NeZero N] (K : Type) [Field K] :
    PowerSeries.heckeV N (ΔbarPS K) ∈ ModPForms.modPMod N 12 K := by
  have h := ModPForms.heckeV_mem_modPMod_mul 1 12 N (NeZero.ne N) K (ΔbarPS K) (ΔbarPS_mem K)
  rwa [one_mul] at h

set_option maxHeartbeats 6400000 in

theorem ofPowerSeries_heckeV (K : Type) [Field K] (N : ℕ) [NeZero N] (φ : PowerSeries K) :
    HahnSeries.ofPowerSeries ℤ K (PowerSeries.heckeV N φ) = qExpand K N (HahnSeries.ofPowerSeries ℤ K φ) := by
  rw [← LaurentSeries.heckeV_eq_qExpand K N]
  ext n
  rw [LaurentSeries.coeff_heckeV]
  rcases lt_or_ge n 0 with hn | hn
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hn]
    split_ifs with hd
    · obtain ⟨c, rfl⟩ := hd
      have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      have hc : c < 0 := by nlinarith
      rw [Int.mul_ediv_cancel_left _ hN.ne', ModularCurve.ofPowerSeries_coeff_of_neg _ hc]
    · rfl
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_heckeV]
    by_cases hd : N ∣ m
    · rw [if_pos hd, if_pos (Int.natCast_dvd_natCast.mpr hd)]
      obtain ⟨c, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N)), Nat.cast_mul,
        Int.mul_ediv_cancel_left _ (by exact_mod_cast (NeZero.ne N)), HahnSeries.ofPowerSeries_apply_coeff]
    · rw [if_neg hd, if_neg (fun h => hd (Int.natCast_dvd_natCast.mp h))]

set_option maxHeartbeats 6400000 in

theorem exists_G (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (K : Type) [Field K] [CharP K p] :
    ∃ G : ↥(modularFunctionFieldC K N), IsModPFormFn K 6 (G : LaurentSeries K) ∧
      (G : LaurentSeries K) * thetaL K (jqModC K) ^ 6 = qExpand K N (ι K Δ') := by
  have hmem : PowerSeries.heckeV N (ΔbarPS K) ∈ ModPForms.modPMod N (2 * ((6 : ℕ) : ℤ)) K := by
    have h := heckeV_ΔbarPS_mem N K
    norm_num
    exact h
  obtain ⟨G, hG, hq⟩ := ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod p N hpN K 6 _ hmem
  refine ⟨G, hG, ?_⟩
  rw [ofPowerSeries_heckeV, ← ι_Δ'] at hq
  rw [← hq]
  show _ = (G : LaurentSeries K) * thetaJ K ^ ((6 : ℕ) : ℤ)
  rw [zpow_natCast]
  rfl

end C2B

namespace C2C

p2m_open "ModularCurve~coeffMap_injective AlgebraicCurve P2MW.S_ModularCurve_six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace.ATHETA2Q P2MW.S_ModularCurve_six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace.C2B Polynomial"

section LS

variable (K : Type) [Field K]

set_option maxHeartbeats 6400000 in
theorem ne_algebraMap_of_transcendental {x : LaurentSeries K} (hx : Transcendental K x) (c : K) :
    x ≠ algebraMap K (LaurentSeries K) c := fun h => hx (h ▸ isAlgebraic_algebraMap c)

set_option maxHeartbeats 6400000 in
theorem jqModC_ne_algebraMap (c : K) : jqModC K ≠ algebraMap K (LaurentSeries K) c :=
  ne_algebraMap_of_transcendental K (ModularCurve.transcendental_jqModC K) c

set_option maxHeartbeats 6400000 in
theorem jqNModC_ne_algebraMap (N : ℕ) [NeZero N] (c : K) : jqNModC K N ≠ algebraMap K (LaurentSeries K) c := by
  intro h
  apply jqModC_ne_algebraMap K c
  apply qExpand_injective (R := K) N
  rw [ModularCurve.algebraMap_laurentSeries_eq_single] at h ⊢
  rw [qExpand_single, mul_zero]
  exact h

set_option maxHeartbeats 6400000 in
theorem ι_Δ'_ne_zero : ι K Δ' ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries K => x.coeff ((1 : ℕ) : ℤ)) h
  simp only [HahnSeries.coeff_zero] at h1
  rw [ι_coeff_natCast] at h1
  have h2 : PowerSeries.coeff 1 Δ' = 1 := by
    show PowerSeries.coeff (0 + 1) (PowerSeries.X * dedekindEtaUnit) = 1
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, dedekindEtaUnit, map_pow,
      constantCoeff_etaProd, one_pow]
  rw [h2] at h1
  simp at h1

set_option maxHeartbeats 6400000 in
theorem thetaL_jqModC_ne_zero : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have h6 := thetaL_jqModC_pow_six K
  rw [h, zero_pow (by norm_num)] at h6
  have h1728 : (1728 : LaurentSeries K) = algebraMap K (LaurentSeries K) 1728 := by
    rw [map_ofNat]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero 4 ?_) (pow_ne_zero 3 ?_)) (ι_Δ'_ne_zero K) h6.symm
  · simpa using jqModC_ne_algebraMap K 0
  · rw [h1728, sub_ne_zero]; exact jqModC_ne_algebraMap K 1728

set_option maxHeartbeats 6400000 in

theorem thetaL_jqNModC_pow_six (N : ℕ) [NeZero N] :
    thetaL K (jqNModC K N) ^ 6 =
      (N : LaurentSeries K) ^ 6 * (jqNModC K N ^ 4 * (jqNModC K N - 1728) ^ 3 * qExpand K N (ι K Δ')) := by
  rw [jqNModC, ModularCurve.thetaL_qExpand, HahnSeries.single_zero_natCast, mul_pow, ← map_pow (qExpand K N),
    thetaL_jqModC_pow_six]
  simp only [map_mul, map_pow, map_sub, map_ofNat]

end LS

section Curve

variable (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (K : Type) [Field K] [CharP K p]

set_option maxHeartbeats 6400000 in

theorem mem_of_isIntegral_adjoin (x : ↥(modularFunctionFieldC K N))
    (hx : IsIntegral (Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K))) (x : LaurentSeries K))
    (w : Place K ↥(modularFunctionFieldC K N)) (hw : jGeomGen K N ∈ w.toValuationSubring) : x ∈ w.toValuationSubring := by
  classical

  set S : Subalgebra K ↥(modularFunctionFieldC K N) := Algebra.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N)) with hS
  have hval : S.map (modularFunctionFieldC K N).val = Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
    rw [hS]
    erw [AlgHom.map_adjoin (modularFunctionFieldC K N).val ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))]
    rw [Set.image_singleton]; rfl
  have hinj : Function.Injective (modularFunctionFieldC K N).val := Subtype.val_injective
  let e : S ≃ₐ[K] ↥(S.map (modularFunctionFieldC K N).val) := Subalgebra.equivMapOfInjective S _ hinj
  let φ : ↥(Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K))) →+* ↥(modularFunctionFieldC K N) :=
    (S.val.toRingHom).comp ((e.symm.toAlgHom.toRingHom).comp (Subalgebra.inclusion hval.ge).toRingHom)
  have hφ : ∀ c, ((φ c : ↥(modularFunctionFieldC K N)) : LaurentSeries K) = (c : LaurentSeries K) := by
    intro c
    have h1 : ((Subalgebra.inclusion hval.ge c : ↥(S.map (modularFunctionFieldC K N).val)) : LaurentSeries K) = c := rfl
    have h2 : ∀ s : S, ((e s : ↥(S.map (modularFunctionFieldC K N).val)) : LaurentSeries K) = ((s : ↥(modularFunctionFieldC K N)) : LaurentSeries K) :=
      fun s => rfl
    show (((e.symm (Subalgebra.inclusion hval.ge c)) : S) : ↥(modularFunctionFieldC K N)).val = _
    rw [← h1, ← h2, AlgEquiv.apply_symm_apply]
  have key : ∀ y : ↥(modularFunctionFieldC K N), y ∈ S → y ∈ w.toValuationSubring := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz => rw [Set.mem_singleton_iff] at hz; subst hz; exact hw
    | algebraMap c => exact w.algebraMap_mem' c
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  have hSw : ∀ s : S, (s : ↥(modularFunctionFieldC K N)) ∈ w.toValuationSubring := fun s => key s.1 s.2
  obtain ⟨P, hPm, hPx⟩ := hx
  refine Place.mem_of_eval_monic_eq_zero w (P := P.map φ) (hPm.map φ) (fun i => ?_) ?_
  · rw [Polynomial.coeff_map]
    exact hSw _
  · apply hinj
    have e1 : Polynomial.eval x (P.map φ) = P.eval₂ φ x := Polynomial.eval_map _ _
    have e2 := Polynomial.hom_eval₂ P φ (modularFunctionFieldC K N).val.toRingHom x
    have e3 : ((modularFunctionFieldC K N).val.toRingHom).comp φ =
        algebraMap (↥(Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K)))) (LaurentSeries K) := RingHom.ext hφ
    show (modularFunctionFieldC K N).val.toRingHom (Polynomial.eval x (P.map φ)) = (modularFunctionFieldC K N).val.toRingHom 0
    rw [map_zero, e1, e2, e3]
    exact hPx

end Curve

end C2C

namespace C2D

p2m_open "ModularCurve~coeffMap_injective AlgebraicCurve P2MW.S_ModularCurve_six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace.ATHETA2Q P2MW.S_ModularCurve_six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace.C2B P2MW.S_ModularCurve_six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace.C2C"

section OrdLemmas

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

set_option maxHeartbeats 6400000 in
theorem ord_one' : v.ord (1 : F) = 0 := by
  have h := v.ord_mul (one_ne_zero) (one_ne_zero (α := F))
  rw [mul_one] at h
  omega

set_option maxHeartbeats 6400000 in
theorem ord_pow' {f : F} (hf : f ≠ 0) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  induction n with
  | zero => rw [pow_zero, ord_one']; simp
  | succ n ih => rw [pow_succ, v.ord_mul (pow_ne_zero n hf) hf, ih]; push_cast; ring

set_option maxHeartbeats 6400000 in
theorem ord_algebraMap' {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have h1 : 0 ≤ v.ord (algebraMap K F c) :=
    (Place.mem_iff_ord_nonneg v ((map_ne_zero _).2 hc)).1 (v.algebraMap_mem' c)
  have h2 : 0 ≤ v.ord (algebraMap K F c⁻¹) :=
    (Place.mem_iff_ord_nonneg v ((map_ne_zero _).2 (inv_ne_zero hc))).1 (v.algebraMap_mem' c⁻¹)
  have h3 : v.ord (algebraMap K F c) + v.ord (algebraMap K F c⁻¹) = 0 := by
    rw [← v.ord_mul ((map_ne_zero _).2 hc) ((map_ne_zero _).2 (inv_ne_zero hc)), ← map_mul,
      mul_inv_cancel₀ hc, map_one, ord_one']
  omega

end OrdLemmas

variable (N : ℕ) [NeZero N] (K : Type) [Field K]

set_option maxHeartbeats 6400000 in

theorem ge_direction (p : ℕ) [Fact p.Prime] [CharP K p] (hpN : ¬ p ∣ N) (h : ↥(modularFunctionFieldC K N))
    (hh : (h : LaurentSeries K) * thetaL K (jqModC K) = thetaL K (jqNModC K N))
    (w : Place K ↥(modularFunctionFieldC K N)) (hw : IsAffineGeomPlace K N w) :
    4 * w.ord (jNGeomGen K N) + 3 * w.ord (jNGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) 1728) ≤
      6 * w.ord h + 4 * w.ord (jGeomGen K N)
        + 3 * w.ord (jGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) 1728) := by
  obtain ⟨G, ⟨hG1, -⟩, hGq⟩ := exists_G p N hpN K
  set jF := jGeomGen K N with hjFdef
  set jNF := jNGeomGen K N with hjNFdef
  set c : ↥(modularFunctionFieldC K N) := algebraMap K ↥(modularFunctionFieldC K N) 1728 with hcdef
  have hcoe_c : ((c : ↥(modularFunctionFieldC K N)) : LaurentSeries K) = 1728 := by
    rw [hcdef]
    show algebraMap K (LaurentSeries K) 1728 = 1728
    rw [map_ofNat]
  have hcoe_j : ((jF : ↥(modularFunctionFieldC K N)) : LaurentSeries K) = jqModC K := rfl
  have hcoe_jN : ((jNF : ↥(modularFunctionFieldC K N)) : LaurentSeries K) = jqNModC K N := rfl
  have hcoe_N : (((N : ↥(modularFunctionFieldC K N))) : LaurentSeries K) = (N : LaurentSeries K) := by
    rw [show (N : ↥(modularFunctionFieldC K N)) = algebraMap K _ N from (map_natCast _ N).symm]
    show algebraMap K (LaurentSeries K) N = N
    rw [map_natCast]

  have hNK : (N : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p N]; exact hpN
  have hNF : (N : ↥(modularFunctionFieldC K N)) ≠ 0 := by
    rw [show (N : ↥(modularFunctionFieldC K N)) = algebraMap K _ N from (map_natCast _ N).symm]
    exact (map_ne_zero _).2 hNK
  have hNL : (N : LaurentSeries K) ≠ 0 := by
    rw [show (N : LaurentSeries K) = algebraMap K _ N from (map_natCast _ N).symm]
    exact (map_ne_zero _).2 hNK
  have h1728 : (1728 : LaurentSeries K) = algebraMap K (LaurentSeries K) 1728 := (map_ofNat _ _).symm
  have hj : jF ≠ 0 := by
    intro e; have e' := congrArg Subtype.val e
    rw [hcoe_j, ZeroMemClass.coe_zero, ← map_zero (algebraMap K (LaurentSeries K))] at e'
    exact jqModC_ne_algebraMap K 0 e'
  have hjc : jF - c ≠ 0 := by
    rw [sub_ne_zero]; intro e; have e' := congrArg Subtype.val e
    rw [hcoe_j, hcoe_c, h1728] at e'
    exact jqModC_ne_algebraMap K 1728 e'
  have hjN : jNF ≠ 0 := by
    intro e; have e' := congrArg Subtype.val e
    rw [hcoe_jN, ZeroMemClass.coe_zero, ← map_zero (algebraMap K (LaurentSeries K))] at e'
    exact jqNModC_ne_algebraMap K N 0 e'
  have hjNc : jNF - c ≠ 0 := by
    rw [sub_ne_zero]; intro e; have e' := congrArg Subtype.val e
    rw [hcoe_jN, hcoe_c, h1728] at e'
    exact jqNModC_ne_algebraMap K N 1728 e'
  have hθ : thetaL K (jqModC K) ≠ 0 := thetaL_jqModC_ne_zero K
  have hjqN : jqNModC K N ≠ 0 := by
    have := jqNModC_ne_algebraMap K N 0; rwa [map_zero] at this
  have hjqNc : jqNModC K N - 1728 ≠ 0 := by
    rw [h1728, sub_ne_zero]; exact jqNModC_ne_algebraMap K N 1728
  have hΔN : qExpand K N (ι K Δ') ≠ 0 := fun e =>
    ι_Δ'_ne_zero K (qExpand_injective (R := K) N (by rw [e, map_zero]))
  have hθN : thetaL K (jqNModC K N) ≠ 0 := by
    intro e
    have h6 := thetaL_jqNModC_pow_six K N
    rw [e, zero_pow (by norm_num)] at h6
    exact mul_ne_zero (pow_ne_zero 6 hNL) (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 hjqN) (pow_ne_zero 3 hjqNc)) hΔN) h6.symm
  have hh0 : h ≠ 0 := by
    intro e; rw [e, ZeroMemClass.coe_zero, zero_mul] at hh; exact hθN hh.symm

  have key : G * ((N : ↥(modularFunctionFieldC K N)) ^ 6 * jNF ^ 4 * (jNF - c) ^ 3) = h ^ 6 := by
    apply Subtype.val_injective
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub, hcoe_c, hcoe_jN, hcoe_N]
    apply mul_right_cancel₀ (pow_ne_zero 6 hθ)
    calc (G : LaurentSeries K) * ((N : LaurentSeries K) ^ 6 * jqNModC K N ^ 4 * (jqNModC K N - 1728) ^ 3) * thetaL K (jqModC K) ^ 6
          = ((N : LaurentSeries K) ^ 6 * jqNModC K N ^ 4 * (jqNModC K N - 1728) ^ 3) *
              ((G : LaurentSeries K) * thetaL K (jqModC K) ^ 6) := by ring
      _ = thetaL K (jqNModC K N) ^ 6 := by rw [hGq, thetaL_jqNModC_pow_six]; ring
      _ = ((h : LaurentSeries K) * thetaL K (jqModC K)) ^ 6 := by rw [hh]
      _ = (h : LaurentSeries K) ^ 6 * thetaL K (jqModC K) ^ 6 := mul_pow _ _ _

  have hU : G ^ 6 * jF ^ 24 * (jF - c) ^ 18 ∈ w.toValuationSubring := by
    apply mem_of_isIntegral_adjoin N K _ _ w hw.1
    have e : (((G ^ 6 * jF ^ 24 * (jF - c) ^ 18 : ↥(modularFunctionFieldC K N))) : LaurentSeries K) =
        (G : LaurentSeries K) ^ 6 * jqModC K ^ (4 * 6) * (jqModC K - algebraMap K (LaurentSeries K) 1728) ^ (3 * 6) := by
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub, hcoe_c, hcoe_j, ← h1728]
    rw [e]; exact hG1
  have hB : (N : ↥(modularFunctionFieldC K N)) ^ 6 * jNF ^ 4 * (jNF - c) ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hNF) (pow_ne_zero _ hjN)) (pow_ne_zero _ hjNc)
  have hG0 : G ≠ 0 := by
    intro e; rw [e, zero_mul] at key; exact pow_ne_zero 6 hh0 key.symm
  have hUne : G ^ 6 * jF ^ 24 * (jF - c) ^ 18 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj)) (pow_ne_zero _ hjc)
  have hordU : 0 ≤ w.ord (G ^ 6 * jF ^ 24 * (jF - c) ^ 18) := (Place.mem_iff_ord_nonneg w hUne).1 hU

  have eq2 : h ^ 36 * jF ^ 24 * (jF - c) ^ 18 =
      (G ^ 6 * jF ^ 24 * (jF - c) ^ 18) * ((N : ↥(modularFunctionFieldC K N)) ^ 6 * jNF ^ 4 * (jNF - c) ^ 3) ^ 6 := by
    rw [show h ^ 36 = (h ^ 6) ^ 6 by ring, ← key]; ring
  have hordN : w.ord (N : ↥(modularFunctionFieldC K N)) = 0 := by
    rw [show (N : ↥(modularFunctionFieldC K N)) = algebraMap K _ N from (map_natCast _ N).symm]
    exact ord_algebraMap' w hNK
  have hL : w.ord (h ^ 36 * jF ^ 24 * (jF - c) ^ 18) = 36 * w.ord h + 24 * w.ord jF + 18 * w.ord (jF - c) := by
    rw [w.ord_mul (mul_ne_zero (pow_ne_zero _ hh0) (pow_ne_zero _ hj)) (pow_ne_zero _ hjc),
      w.ord_mul (pow_ne_zero _ hh0) (pow_ne_zero _ hj), ord_pow' w hh0, ord_pow' w hj, ord_pow' w hjc]
    push_cast; ring
  have hR : w.ord ((G ^ 6 * jF ^ 24 * (jF - c) ^ 18) * ((N : ↥(modularFunctionFieldC K N)) ^ 6 * jNF ^ 4 * (jNF - c) ^ 3) ^ 6)
      = w.ord (G ^ 6 * jF ^ 24 * (jF - c) ^ 18) + 6 * (4 * w.ord jNF + 3 * w.ord (jNF - c)) := by
    rw [w.ord_mul hUne (pow_ne_zero _ hB), ord_pow' w hB,
      w.ord_mul (mul_ne_zero (pow_ne_zero _ hNF) (pow_ne_zero _ hjN)) (pow_ne_zero _ hjNc),
      w.ord_mul (pow_ne_zero _ hNF) (pow_ne_zero _ hjN), ord_pow' w hNF, ord_pow' w hjN, ord_pow' w hjNc, hordN]
    push_cast; ring
  have hfin := congrArg w.ord eq2
  rw [hL, hR] at hfin
  omega

end C2D

namespace OggUnit

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective KaehlerDifferential IsLocalRing"

section Values

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

set_option maxHeartbeats 6400000 in
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

set_option maxHeartbeats 6400000 in
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

set_option maxHeartbeats 6400000 in
theorem isCurveOver_cast {L : Type*} [Field L] [Algebra K L]
    {E E' : IntermediateField K L} (h : E = E') (hE : IsCurveOver K ↥E) : IsCurveOver K ↥E' := by
  subst h; exact hE

set_option maxHeartbeats 6400000 in
theorem cast_ne_zero_of_lt (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] {n : ℕ} (h0 : n ≠ 0) (hn : n < p) :
    ((n : ℕ) : K) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff K p] at h
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h) (not_le.mpr hn)

end Values

section LevelN

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

set_option maxHeartbeats 6400000 in
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

set_option maxHeartbeats 6400000 in
theorem jNGeomGen_mem_of_jGeomGen_mem (x : Place K ↥(modularFunctionFieldC K N))
    (hj : jGeomGen K N ∈ x.toValuationSubring) : jNGeomGen K N ∈ x.toValuationSubring :=
  x.mem_toValuationSubring_of_isIntegral_adjoin hj (isIntegral_jNGeomGen K N)

set_option maxHeartbeats 6400000 in
theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (hg : Function.Injective g) :
    Function.Injective (coeffMap g) := fun b c h =>
  HahnSeries.ext (funext fun k => hg (by rw [← coeffMap_coeff, ← coeffMap_coeff, h]))

set_option maxHeartbeats 6400000 in
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

set_option maxHeartbeats 6400000 in
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

set_option maxHeartbeats 6400000 in
theorem jGeomGen_mem_of_jNGeomGen_mem (x : Place K ↥(modularFunctionFieldC K N))
    (hj : jNGeomGen K N ∈ x.toValuationSubring) : jGeomGen K N ∈ x.toValuationSubring := by
  rcases Nat.lt_or_ge 1 N with hN | hN
  · exact x.mem_toValuationSubring_of_isIntegral_adjoin hj (isIntegral_jGeomGen K N hN)
  · have h1 : N = 1 := le_antisymm hN (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
    subst h1
    rwa [jNGeomGen_one] at hj

set_option maxHeartbeats 6400000 in
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

set_option maxHeartbeats 6400000 in
theorem thetaL_coeff' (x : LaurentSeries K) (n : ℤ) :
    (thetaL K x).coeff n = (n : K) * x.coeff n := by
  rw [thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp only [Nat.cast_one, sub_add_cancel, Ring.choose_one_right, zsmul_eq_mul]

set_option maxHeartbeats 6400000 in
theorem thetaL_jqModC_ne_zero : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries K => x.coeff (-1)) h
  beta_reduce at h1
  rw [thetaL_coeff', coeff_jqModC_neg_one, HahnSeries.coeff_zero] at h1
  norm_num at h1

variable {K N} in
set_option maxHeartbeats 6400000 in
theorem thetaL_jqNModC_ne_zero (hN : (N : K) ≠ 0) : thetaL K (jqNModC K N) ≠ 0 := by
  rw [jqNModC, thetaL_qExpand]
  refine mul_ne_zero ?_ ?_
  · intro h
    have := congrArg (fun x : LaurentSeries K => x.coeff 0) h
    simp only [HahnSeries.coeff_single_same, HahnSeries.coeff_zero] at this
    exact hN this
  · exact (map_ne_zero (qExpand K N)).mpr (thetaL_jqModC_ne_zero K)

end Theta

section Unit

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
  (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]

set_option maxHeartbeats 6400000 in

def u (h : ↥(modularFunctionFieldC K N)) : ↥(modularFunctionFieldC K N) :=
  (N : ↥(modularFunctionFieldC K N)) ^ 6 * jNGeomGen K N ^ 4
      * (jNGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) 1728) ^ 3
    / (h ^ 6 * jGeomGen K N ^ 4 * (jGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) 1728) ^ 3)

set_option maxHeartbeats 6400000 in
theorem ord_sub_algebraMap_of_ord_neg {F : Type*} [Field F] [Algebra K F] (x : Place K F) {f : F}
    (hf : x.ord f < 0) (c : K) : x.ord (f - algebraMap K F c) = x.ord f := by
  by_cases hc : c = 0
  · rw [hc, map_zero, sub_zero]
  have hf0 : f ≠ 0 := fun h => by rw [h, x.ord_zero] at hf; exact lt_irrefl _ hf
  rw [sub_eq_add_neg]
  refine x.ord_add_eq_of_lt hf0 (neg_ne_zero.2 ((map_ne_zero _).2 hc)) ?_
  rw [x.ord_neg, x.ord_algebraMap]; exact hf

set_option maxHeartbeats 6400000 in
include hpN in

theorem ord_u (h : ↥(modularFunctionFieldC K N)) (hh0 : h ≠ 0) (w : Place K ↥(modularFunctionFieldC K N)) :
    w.ord (u N K h) = 4 * w.ord (jNGeomGen K N) + 3 * w.ord (jNGeomGen K N - algebraMap K _ 1728)
      - 6 * w.ord h - 4 * w.ord (jGeomGen K N) - 3 * w.ord (jGeomGen K N - algebraMap K _ 1728) := by
  let F : Type := ↥(modularFunctionFieldC K N)
  have hN : (N : K) ≠ 0 := fun h0 => hpN ((CharP.cast_eq_zero_iff K p N).1 h0)
  have hNF : (N : F) ≠ 0 := by
    rw [show (N : F) = algebraMap K F (N : K) from (map_natCast _ N).symm]; exact (map_ne_zero _).mpr hN
  have hj0 : jGeomGen K N ≠ 0 := by simpa using jGeomGen_sub_algebraMap_ne_zero K N 0
  have hjN0 : jNGeomGen K N ≠ 0 := by simpa using jNGeomGen_sub_algebraMap_ne_zero K N 0
  have hj1 := jGeomGen_sub_algebraMap_ne_zero K N 1728
  have hjN1 := jNGeomGen_sub_algebraMap_ne_zero K N 1728
  have hordN : w.ord ((N : F) ^ 6) = 0 := by
    rw [show (N : F) = algebraMap K F (N : K) from (map_natCast _ N).symm, ← map_pow, w.ord_algebraMap]
  unfold u
  rw [div_eq_mul_inv, w.ord_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hNF) (pow_ne_zero _ hjN0)) (pow_ne_zero _ hjN1))
      (inv_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hh0) (pow_ne_zero _ hj0)) (pow_ne_zero _ hj1))),
    w.ord_inv, w.ord_mul (mul_ne_zero (pow_ne_zero _ hNF) (pow_ne_zero _ hjN0)) (pow_ne_zero _ hjN1),
    w.ord_mul (pow_ne_zero _ hNF) (pow_ne_zero _ hjN0),
    w.ord_mul (mul_ne_zero (pow_ne_zero _ hh0) (pow_ne_zero _ hj0)) (pow_ne_zero _ hj1),
    w.ord_mul (pow_ne_zero _ hh0) (pow_ne_zero _ hj0), hordN]
  simp only [← zpow_natCast, Place.ord_zpow]
  push_cast
  ring

set_option maxHeartbeats 6400000 in
include hpN in
theorem u_ne_zero (h : ↥(modularFunctionFieldC K N)) (hh0 : h ≠ 0) : u N K h ≠ 0 := by
  let F : Type := ↥(modularFunctionFieldC K N)
  have hN : (N : K) ≠ 0 := fun h0 => hpN ((CharP.cast_eq_zero_iff K p N).1 h0)
  have hNF : (N : F) ≠ 0 := by
    rw [show (N : F) = algebraMap K F (N : K) from (map_natCast _ N).symm]; exact (map_ne_zero _).mpr hN
  have hj0 : jGeomGen K N ≠ 0 := by simpa using jGeomGen_sub_algebraMap_ne_zero K N 0
  have hjN0 : jNGeomGen K N ≠ 0 := by simpa using jNGeomGen_sub_algebraMap_ne_zero K N 0
  unfold u
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hNF) (pow_ne_zero _ hjN0))
    (pow_ne_zero _ (jNGeomGen_sub_algebraMap_ne_zero K N 1728)))
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hh0) (pow_ne_zero _ hj0)) (pow_ne_zero _ (jGeomGen_sub_algebraMap_ne_zero K N 1728)))

set_option maxHeartbeats 12800000 in
include hp5 hpN in

theorem ord_u_le_at_cusp (h : ↥(modularFunctionFieldC K N))
    (hh : (h : LaurentSeries K) * thetaL K (jqModC K) = thetaL K (jqNModC K N))
    (w : Place K ↥(modularFunctionFieldC K N)) (hw : w.ord (jGeomGen K N) < 0) :
    w.ord (u N K h) ≤ w.ord (jNGeomGen K N) - w.ord (jGeomGen K N) := by
  classical
  haveI : PerfectField K := IsAlgClosed.perfectField K
  let F : Type := ↥(modularFunctionFieldC K N)
  have hN : (N : K) ≠ 0 := fun h0 => hpN ((CharP.cast_eq_zero_iff K p N).1 h0)
  set j : F := jGeomGen K N with hjdef
  set jN : F := jNGeomGen K N with hjNdef
  have hj0 : j ≠ 0 := by simpa using jGeomGen_sub_algebraMap_ne_zero K N 0
  have hjN0 : jN ≠ 0 := by simpa using jNGeomGen_sub_algebraMap_ne_zero K N 0

  have hjmem : j ∉ w.toValuationSubring := fun hm => by
    have := (w.mem_iff_ord_nonneg hj0).mp hm; omega
  have hjNmem : jN ∉ w.toValuationSubring := fun hm => hjmem (jGeomGen_mem_of_jNGeomGen_mem K N w hm)
  have hwN : w.ord jN < 0 := by
    by_contra hge; push Not at hge; exact hjNmem ((w.mem_iff_ord_nonneg hjN0).mpr hge)

  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  obtain ⟨hfin, hsep⟩ := finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC K N data
    (isSeparable_jqNModC_of_natCast_ne_zero K N hN)
  haveI : FiniteDimensional ↥(IntermediateField.adjoin K ({j} : Set F)) F := hfin
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin K ({j} : Set F)) F := hsep
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K ({j} : Set F)) F := Algebra.IsAlgebraic.of_finite _ _

  have hθj : thetaL K (jqModC K) ≠ 0 := thetaL_jqModC_ne_zero K
  have hθjN : thetaL K (jqNModC K N) ≠ 0 := thetaL_jqNModC_ne_zero hN
  have hh0 : h ≠ 0 := by
    intro h0
    have : (h : LaurentSeries K) = 0 := by rw [h0]; rfl
    rw [this, zero_mul] at hh
    exact hθjN hh.symm
  have hjtr : Transcendental K j := by
    intro halg
    exact transcendental_jqModC K (IntermediateField.isAlgebraic_iff.mp halg)
  have hDj : KaehlerDifferential.D K F j ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K j hjtr
  have hspan := KaehlerDifferential.span_D_eq_top_of_transcendental K j hjtr
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : F, c₀ • KaehlerDifferential.D K F j = KaehlerDifferential.D K F jN := by
    have : KaehlerDifferential.D K F jN ∈ Submodule.span F ({KaehlerDifferential.D K F j} : Set (Ω[F⁄K])) := by
      rw [hspan]; exact Submodule.mem_top
    exact Submodule.mem_span_singleton.mp this
  have hc₀h : c₀ = h := by
    apply Subtype.ext
    rw [coe_eq_thetaL_div_of_D_eq_smul K (modularFunctionFieldC K N) jN j c₀ hc₀.symm hθj]
    change thetaL K (jqNModC K N) / thetaL K (jqModC K) = (h : LaurentSeries K)
    rw [div_eq_iff hθj]
    exact hh.symm
  have hD : KaehlerDifferential.D K F jN = h • KaehlerDifferential.D K F j := by rw [← hc₀h]; exact hc₀.symm

  have htame : (((w.ord (j - algebraMap K F 0)).natAbs : ℕ) : K) ≠ 0 := by
    rw [map_zero, sub_zero]
    exact natAbs_ord_jGeomGen_cast_ne_zero_of_ord_neg p K N hN w hw
  have hδ : w.ordDiff (KaehlerDifferential.D K F j) = w.ord j - 1 := by
    have := Place.ordDiff_D_eq_ord_sub_algebraMap_sub_one_of_cast_natAbs_ne_zero j w (f := j) (c := 0)
      (by rw [map_zero, sub_zero]; exact hw.ne) htame
    rwa [map_zero, sub_zero] at this
  have hDjN : KaehlerDifferential.D K F jN ≠ 0 := by rw [hD]; exact smul_ne_zero hh0 hDj
  have hδN : w.ordDiff (KaehlerDifferential.D K F jN) = w.ord h + (w.ord j - 1) := by
    rw [hD, Place.ordDiff_smul_of_perfectField j w hh0 hDj, hδ]
  have hδN_le : w.ord jN - 1 ≤ w.ordDiff (KaehlerDifferential.D K F jN) :=
    Place.ord_sub_one_le_ordDiff_D_of_perfectField j w hDjN
  have hordh : w.ord jN - w.ord j ≤ w.ord h := by linarith

  have h1 : w.ord (j - algebraMap K F 1728) = w.ord j := ord_sub_algebraMap_of_ord_neg K w hw 1728
  have h2 : w.ord (jN - algebraMap K F 1728) = w.ord jN := ord_sub_algebraMap_of_ord_neg K w hwN 1728
  rw [ord_u p N hpN K h hh0 w, h1, h2]
  linarith

end Unit

section Degree

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
  (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]

set_option maxHeartbeats 6400000 in
theorem finrank_adjoin_congr {L : Type*} [Field L] [Algebra K L] {E₁ E₂ : IntermediateField K L} (hE : E₁ = E₂)
    (x : ↥E₁) (y : ↥E₂) (hxy : (x : L) = (y : L)) :
    Module.finrank ↥(IntermediateField.adjoin K ({x} : Set ↥E₁)) ↥E₁
      = Module.finrank ↥(IntermediateField.adjoin K ({y} : Set ↥E₂)) ↥E₂ := by
  subst hE
  obtain rfl : x = y := Subtype.ext hxy
  rfl

set_option maxHeartbeats 6400000 in
include hpN in
theorem finrank_adjoin_jGeomGen :
    Module.finrank ↥(IntermediateField.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N)))
      ↥(modularFunctionFieldC K N) = dedekindPsi N := by
  have hN : (N : K) ≠ 0 := fun h0 => hpN ((CharP.cast_eq_zero_iff K p N).1 h0)
  have hCF := modularFunctionFieldC_eq_modularFunctionFieldFullC K p N hpN
  exact (finrank_adjoin_congr K hCF (jGeomGen K N) ⟨jqModC K, jqModC_mem_full K N⟩ rfl).trans
    (finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN)

set_option maxHeartbeats 6400000 in
include hpN in
theorem finrank_adjoin_jNGeomGen :
    Module.finrank ↥(IntermediateField.adjoin K ({jNGeomGen K N} : Set ↥(modularFunctionFieldC K N)))
      ↥(modularFunctionFieldC K N) = dedekindPsi N := by
  have hN : (N : K) ≠ 0 := fun h0 => hpN ((CharP.cast_eq_zero_iff K p N).1 h0)
  have hCF := modularFunctionFieldC_eq_modularFunctionFieldFullC K p N hpN
  exact (finrank_adjoin_congr K hCF (jNGeomGen K N)
    ⟨jqNModC K N, modularFunctionFieldC_le_full K N (jqNModC_mem K N)⟩ rfl).trans
    (finrank_adjoin_jqNModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN)

set_option maxHeartbeats 12800000 in
include hp5 hpN in

theorem ord_u_eq_zero_of_forall_nonpos (h : ↥(modularFunctionFieldC K N))
    (hh : (h : LaurentSeries K) * thetaL K (jqModC K) = thetaL K (jqNModC K N))
    (hM1 : ∀ w : Place K ↥(modularFunctionFieldC K N), IsAffineGeomPlace K N w → w.ord (u N K h) ≤ 0)
    (w : Place K ↥(modularFunctionFieldC K N)) (hw : IsAffineGeomPlace K N w) : w.ord (u N K h) = 0 := by
  classical
  haveI : PerfectField K := IsAlgClosed.perfectField K
  let F : Type := ↥(modularFunctionFieldC K N)
  have hN : (N : K) ≠ 0 := fun h0 => hpN ((CharP.cast_eq_zero_iff K p N).1 h0)
  haveI hcurve : IsCurveOver K F :=
    isCurveOver_cast (modularFunctionFieldC_eq_modularFunctionFieldFullC K p N hpN).symm
      (isCurveOver_modularFunctionFieldFullC K N)
  have hdeg1 : ∀ v : Place K F, v.deg = 1 := fun v => IsCurveOver.deg_eq_one_of_isAlgClosed v
  set j : F := jGeomGen K N with hjdef
  set jN : F := jNGeomGen K N with hjNdef
  have hj0 : j ≠ 0 := by simpa using jGeomGen_sub_algebraMap_ne_zero K N 0
  have hjN0 : jN ≠ 0 := by simpa using jNGeomGen_sub_algebraMap_ne_zero K N 0
  have hθjN : thetaL K (jqNModC K N) ≠ 0 := thetaL_jqNModC_ne_zero hN
  have hh0 : h ≠ 0 := by
    intro h0
    have : (h : LaurentSeries K) = 0 := by rw [h0]; rfl
    rw [this, zero_mul] at hh
    exact hθjN hh.symm
  have hu0 : u N K h ≠ 0 := u_ne_zero p N hpN K h hh0

  obtain ⟨Du, hDu, hDudeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (u N K h) hu0
  obtain ⟨Dj, hDj, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) j hj0
  obtain ⟨DjN, hDjN, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) jN hjN0

  let P : Divisor K F := Finsupp.mapRange (fun n : ℤ => max 0 (-n)) (by simp) Dj
  let PN : Divisor K F := Finsupp.mapRange (fun n : ℤ => max 0 (-n)) (by simp) DjN
  have hP : ∀ v, P v = max 0 (-v.ord j) := fun v => by
    show max 0 (-(Dj v)) = _; rw [hDj v]
  have hPN : ∀ v, PN v = max 0 (-v.ord jN) := fun v => by
    show max 0 (-(DjN v)) = _; rw [hDjN v]
  have hjtr : Transcendental K j := by
    intro halg
    exact transcendental_jqModC K (IntermediateField.isAlgebraic_iff.mp halg)
  have hjNtr : Transcendental K jN := by
    intro halg
    exact transcendental_jqNModC K N (IntermediateField.isAlgebraic_iff.mp halg)
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  haveI : FiniteDimensional ↥(IntermediateField.adjoin K ({j} : Set F)) F :=
    (finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC K N data
      (isSeparable_jqNModC_of_natCast_ne_zero K N hN)).1
  haveI : FiniteDimensional ↥(IntermediateField.adjoin K ({jN} : Set F)) F :=
    Module.finite_of_finrank_pos (by rw [hjNdef, finrank_adjoin_jNGeomGen p N hpN K]; exact dedekindPsi_pos N (NeZero.ne N))
  have hdegP : Divisor.degree P = (Module.finrank ↥(IntermediateField.adjoin K ({j} : Set F)) F : ℤ) :=
    degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental j hjtr P hP
  have hdegPN : Divisor.degree PN = (Module.finrank ↥(IntermediateField.adjoin K ({jN} : Set F)) F : ℤ) :=
    degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental jN hjNtr PN hPN
  have hdegeq : Divisor.degree P = Divisor.degree PN := by
    rw [hdegP, hdegPN, hjdef, hjNdef, finrank_adjoin_jGeomGen p N hpN K, finrank_adjoin_jNGeomGen p N hpN K]

  set G : Divisor K F := P - PN - Du with hGdef
  have hGdeg : Divisor.degree G = 0 := by
    rw [hGdef, map_sub, map_sub, hdegeq, hDudeg]; ring
  have hGnonneg : ∀ v, 0 ≤ G v := by
    intro v
    show 0 ≤ (P - PN - Du) v
    rw [Finsupp.sub_apply, Finsupp.sub_apply, hP, hPN, hDu]
    by_cases hv : 0 ≤ v.ord j
    ·
      have hvmem : j ∈ v.toValuationSubring := (v.mem_iff_ord_nonneg hj0).mpr hv
      have hvNmem : jN ∈ v.toValuationSubring := jNGeomGen_mem_of_jGeomGen_mem K N v hvmem
      have hvN : 0 ≤ v.ord jN := (v.mem_iff_ord_nonneg hjN0).mp hvNmem
      have := hM1 v ⟨hvmem, hvNmem⟩
      rw [max_eq_left (by omega), max_eq_left (by omega)]
      linarith
    · push Not at hv
      have hb := ord_u_le_at_cusp p hp5 N hpN K h hh v hv
      have hvNmem : jN ∉ v.toValuationSubring := fun hm =>
        (not_le.mpr hv) ((v.mem_iff_ord_nonneg hj0).mp (jGeomGen_mem_of_jNGeomGen_mem K N v hm))
      have hvN : v.ord jN < 0 := by
        by_contra hge; push Not at hge; exact hvNmem ((v.mem_iff_ord_nonneg hjN0).mpr hge)
      rw [max_eq_right (by omega), max_eq_right (by omega)]
      linarith

  have hGzero : ∀ v, G v = 0 := by
    have hsum : Divisor.degree G = G.support.sum (fun v => G v) := by
      rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp [hdeg1 v]
    rw [hGdeg] at hsum
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hGnonneg v)).mp hsum.symm
    intro v
    by_cases hv : v ∈ G.support
    · exact hall v hv
    · exact Finsupp.notMem_support_iff.mp hv

  have hG := hGzero w
  have hv : 0 ≤ w.ord j := (w.mem_iff_ord_nonneg hj0).mp hw.1
  have hvN : 0 ≤ w.ord jN := (w.mem_iff_ord_nonneg hjN0).mp hw.2
  have : (P - PN - Du) w = 0 := hG
  rw [Finsupp.sub_apply, Finsupp.sub_apply, hP, hPN, hDu, max_eq_left (by omega), max_eq_left (by omega)] at this
  linarith

set_option maxHeartbeats 6400000 in
include hp5 hpN in

theorem card_of_M1 (h : ↥(modularFunctionFieldC K N))
    (hh : (h : LaurentSeries K) * thetaL K (jqModC K) = thetaL K (jqNModC K N))
    (hM1 : ∀ w : Place K ↥(modularFunctionFieldC K N), IsAffineGeomPlace K N w → w.ord (u N K h) ≤ 0)
    (w : Place K ↥(modularFunctionFieldC K N)) (hw : IsAffineGeomPlace K N w) :
    6 * w.ord h + 4 * w.ord (jGeomGen K N)
        + 3 * w.ord (jGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) 1728)
      = 4 * w.ord (jNGeomGen K N)
        + 3 * w.ord (jNGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) 1728) := by
  have hN : (N : K) ≠ 0 := fun h0 => hpN ((CharP.cast_eq_zero_iff K p N).1 h0)
  have hθjN : thetaL K (jqNModC K N) ≠ 0 := thetaL_jqNModC_ne_zero hN
  have hh0 : h ≠ 0 := by
    intro h0
    have : (h : LaurentSeries K) = 0 := by rw [h0]; rfl
    rw [this, zero_mul] at hh
    exact hθjN hh.symm
  have h0 := ord_u_eq_zero_of_forall_nonpos p hp5 N hpN K h hh hM1 w hw
  rw [ord_u p N hpN K h hh0 w] at h0
  linarith

end Degree

end OggUnit

p2m_open "ModularCurve~coeffMap_injective" in open AlgebraicCurve  in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (h : ↥(modularFunctionFieldC K N))
    (hh : (h : LaurentSeries K) * thetaL K (jqModC K) = thetaL K (jqNModC K N))
    (w : Place K ↥(modularFunctionFieldC K N)) (hw : IsAffineGeomPlace K N w) :
    6 * w.ord h + 4 * w.ord (jGeomGen K N)
        + 3 * w.ord (jGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) 1728)
      = 4 * w.ord (jNGeomGen K N)
        + 3 * w.ord (jNGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) 1728) :=
  by
  have hN : (N : K) ≠ 0 := fun h0 => hpN ((CharP.cast_eq_zero_iff K p N).1 h0)
  have hθjN : thetaL K (jqNModC K N) ≠ 0 := OggUnit.thetaL_jqNModC_ne_zero hN
  have hh0 : h ≠ 0 := by
    intro h0
    have : (h : LaurentSeries K) = 0 := by rw [h0]; rfl
    rw [this, zero_mul] at hh
    exact hθjN hh.symm
  refine OggUnit.card_of_M1 p hp5 N hpN K h hh ?_ w hw
  intro w' hw'
  have h1 := C2D.ge_direction N K p hpN h hh w' hw'
  have h2 := OggUnit.ord_u p N hpN K h hh0 w'
  linarith

end
end S_ModularCurve_six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace
end P2MW
export P2MW.S_ModularCurve_six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace (solution)
