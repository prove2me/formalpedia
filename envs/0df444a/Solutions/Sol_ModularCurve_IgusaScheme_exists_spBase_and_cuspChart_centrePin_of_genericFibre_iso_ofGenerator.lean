-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_spBase_and_cuspChart_centrePin_of_genericFibre_iso_ofGenerator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/7b7c35e3-24d1-5d41-a0c9-158d0fda3709

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued
import Theorems.Thm_ModularCurve_IgusaScheme_exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing_apply_tmul
import Theorems.Thm_ModularCurve_IgusaScheme_exists_fibreModel_cuspChart_of_chartAlg_of_lift
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piFin_eq_coeffRed
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseInf
import Theorems.Thm_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iota0
import Theorems.Thm_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iotaInf
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_jqModC_ne_zero
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jqModC
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_eq_modularFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_isSeparable_adjoin_jqModC_of_isAlgebraic
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ValuationSubring_exists_ratLocalizedAt_ringHom_of_liesOverPrime
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_spBase_and_cuspChart_centrePin_of_genericFibre_iso_ofGenerator
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine"
p2m_attr_erase "instance" "ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero"
p2m_attr_erase "simp" "compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one"
p2m_attr_erase "simp" "TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve~jBar AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme ModularCurve.CharPModel ModularCurve.CharPReduction"

open scoped TensorProduct

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace D628

universe uK uL
namespace IgusaSide

variable {N : ℕ} [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]

theorem ιFin_eq_ιInf_iff (x₀ : ModularCurve.IgusaScheme.XFin N ℓ) (xi : ModularCurve.IgusaScheme.XInf N ℓ) :
    (ModularCurve.IgusaScheme.ιFin N ℓ).base x₀ = (ModularCurve.IgusaScheme.ιInf N ℓ).base xi ↔
      ∃ w : ModularCurve.IgusaScheme.XMid N ℓ,
        (ModularCurve.IgusaScheme.fFin N ℓ).base w = x₀ ∧ (ModularCurve.IgusaScheme.fInf N ℓ).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (F := span (ModularCurve.IgusaScheme.fFin N ℓ) (ModularCurve.IgusaScheme.fInf N ℓ))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · exact match fi, fj, h₁, h₂ with
        | .init _, .init _, h₁, h₂ => ⟨w, h₁, h₂⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨w, rfl, rfl⟩
    change (ModularCurve.IgusaScheme.fFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ).base w =
      (ModularCurve.IgusaScheme.fInf N ℓ ≫ ModularCurve.IgusaScheme.ιInf N ℓ).base w
    rw [ModularCurve.IgusaScheme.glue_condition]

set_option synthInstance.maxHeartbeats 1600000 in
theorem range_fInf : Set.range (ModularCurve.IgusaScheme.fInf N ℓ).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf N ℓ) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(chartAlgInf N ℓ))) : Set (PrimeSpectrum ↥(chartAlgInf N ℓ))) := by
  letI := (ModularCurve.IgusaScheme.inclInf N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf N ℓ
  exact PrimeSpectrum.localization_away_comap_range ↥(chartAlgMid N ℓ) (jInvChartInf N ℓ)

theorem ιInf_mem_range_ιFin_iff (xi : ModularCurve.IgusaScheme.XInf N ℓ) :
    (ModularCurve.IgusaScheme.ιInf N ℓ).base xi ∈ Set.range (ModularCurve.IgusaScheme.ιFin N ℓ).base ↔
      jInvChartInf N ℓ ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (ιFin_eq_ιInf_iff x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(ModularCurve.IgusaScheme.fFin N ℓ).base w, (ιFin_eq_ιInf_iff _ _).mpr ⟨w, rfl, rfl⟩⟩

theorem exists_eq_comp_of_closedPoint_mem {X U : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R]
    (ι : U ⟶ X) [IsOpenImmersion ι] (f : Spec (CommRingCat.of R) ⟶ X)
    (h : f.base (IsLocalRing.closedPoint R) ∈ Set.range ι.base) :
    ∃ g : Spec (CommRingCat.of R) ⟶ U, g ≫ ι = f := by
  have hrange : Set.range f.base ⊆ Set.range ι.base := by
    rintro _ ⟨q, rfl⟩
    have hs : f.base q ⤳ f.base (IsLocalRing.closedPoint R) :=
      (IsLocalRing.specializes_closedPoint q).map f.base.hom.continuous
    exact hs.mem_open ι.isOpenEmbedding.isOpen_range h
  exact ⟨IsOpenImmersion.lift ι f hrange, IsOpenImmersion.lift_fac ι f hrange⟩

theorem exists_eq_SpecMap_comp_of_closedPoint_mem {X : Scheme.{0}} {R B : Type} [CommRing R] [IsLocalRing R]
    [CommRing B] (ι : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ι] (f : Spec (CommRingCat.of R) ⟶ X)
    (h : f.base (IsLocalRing.closedPoint R) ∈ Set.range ι.base) :
    ∃ χ : B →+* R, Spec.map (CommRingCat.ofHom χ) ≫ ι = f := by
  obtain ⟨g, hg⟩ := exists_eq_comp_of_closedPoint_mem ι f h
  exact ⟨(Spec.preimage g).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage, hg]⟩

theorem ringHom_eq_of_SpecMap_comp_eq {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}}
    (ι : Spec (CommRingCat.of A) ⟶ X) [Mono ι] (ψ ψ' : A →+* B)
    (h : Spec.map (CommRingCat.ofHom ψ') ≫ ι = Spec.map (CommRingCat.ofHom ψ) ≫ ι) : ψ' = ψ := by
  have h1 : Spec.map (CommRingCat.ofHom ψ') = Spec.map (CommRingCat.ofHom ψ) := (cancel_mono ι).mp h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

theorem comp_algebraMap_eq_of_ιFin {R : Type} [CommRing R] (ρ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* R)
    (χ : ↥(chartAlgFin N ℓ) →+* R)
    (h : (Spec.map (CommRingCat.ofHom χ) ≫ ModularCurve.IgusaScheme.ιFin N ℓ) ≫ igusaTo N ℓ =
      Spec.map (CommRingCat.ofHom ρ)) :
    χ.comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ)) = ρ := by
  rw [Category.assoc, ModularCurve.IgusaScheme.ιFin_igusaTo, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem comp_algebraMap_eq_of_ιInf {R : Type} [CommRing R] (ρ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* R)
    (χ : ↥(chartAlgInf N ℓ) →+* R)
    (h : (Spec.map (CommRingCat.ofHom χ) ≫ ModularCurve.IgusaScheme.ιInf N ℓ) ≫ igusaTo N ℓ =
      Spec.map (CommRingCat.ofHom ρ)) :
    χ.comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ)) = ρ := by
  rw [Category.assoc, ModularCurve.IgusaScheme.ιInf_igusaTo, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem exists_mid_of_SpecMap_ιFin_eq_SpecMap_ιInf {F' : Type} [Field F']
    (α : ↥(chartAlgFin N ℓ) →+* F') (β : ↥(chartAlgInf N ℓ) →+* F')
    (h : Spec.map (CommRingCat.ofHom α) ≫ ModularCurve.IgusaScheme.ιFin N ℓ =
      Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.IgusaScheme.ιInf N ℓ) :
    ∃ w : ↥(chartAlgMid N ℓ) →+* F',
      w.comp (ModularCurve.IgusaScheme.inclFin N ℓ).toRingHom = α ∧
      w.comp (ModularCurve.IgusaScheme.inclInf N ℓ).toRingHom = β := by

  have hpt : (ModularCurve.IgusaScheme.ιFin N ℓ).base ((Spec.map (CommRingCat.ofHom α)).base (IsLocalRing.closedPoint F')) =
      (ModularCurve.IgusaScheme.ιInf N ℓ).base ((Spec.map (CommRingCat.ofHom β)).base (IsLocalRing.closedPoint F')) := by
    have := congrArg (fun f : Spec (CommRingCat.of F') ⟶ ModularCurve.IgusaScheme N ℓ =>
      f.base (IsLocalRing.closedPoint F')) h
    exact this
  obtain ⟨w0, hw0, -⟩ := (ιFin_eq_ιInf_iff _ _).mp hpt
  haveI : IsOpenImmersion (ModularCurve.IgusaScheme.fFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ) := inferInstance
  have hmem : (Spec.map (CommRingCat.ofHom α) ≫ ModularCurve.IgusaScheme.ιFin N ℓ).base (IsLocalRing.closedPoint F') ∈
      Set.range (ModularCurve.IgusaScheme.fFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ).base :=
    ⟨w0, by
      show (ModularCurve.IgusaScheme.ιFin N ℓ).base ((ModularCurve.IgusaScheme.fFin N ℓ).base w0) =
        (ModularCurve.IgusaScheme.ιFin N ℓ).base ((Spec.map (CommRingCat.ofHom α)).base (IsLocalRing.closedPoint F'))
      rw [hw0]⟩
  obtain ⟨w, hw⟩ := exists_eq_SpecMap_comp_of_closedPoint_mem
    (ModularCurve.IgusaScheme.fFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ)
    (Spec.map (CommRingCat.ofHom α) ≫ ModularCurve.IgusaScheme.ιFin N ℓ) hmem
  refine ⟨w, ?_, ?_⟩
  · apply ringHom_eq_of_SpecMap_comp_eq (ModularCurve.IgusaScheme.ιFin N ℓ)
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    show Spec.map (CommRingCat.ofHom w) ≫ ModularCurve.IgusaScheme.fFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ = _
    exact hw
  · apply ringHom_eq_of_SpecMap_comp_eq (ModularCurve.IgusaScheme.ιInf N ℓ)
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    show Spec.map (CommRingCat.ofHom w) ≫ ModularCurve.IgusaScheme.fInf N ℓ ≫ ModularCurve.IgusaScheme.ιInf N ℓ = _
    rw [← ModularCurve.IgusaScheme.glue_condition]
    exact hw.trans h

end IgusaSide

section Glued

variable (K : Type uK) [Field K] {L : Type uK} [Field L] [Algebra K L] (t : L)

private def _root_.D628.toAlgHom {R : Type uK} [CommRing R] [Algebra K R] (φ : R →+* K)
    (hφ : φ.comp (algebraMap K R) = RingHom.id K) : R →ₐ[K] K :=
  { φ with commutes' := fun c => RingHom.congr_fun hφ c }

p2m_export "D628" "toAlgHom"
@[scoped simp]
theorem toAlgHom_toRingHom {R : Type uK} [CommRing R] [Algebra K R] (φ : R →+* K)
    (hφ : φ.comp (algebraMap K R) = RingHom.id K) : (toAlgHom K φ hφ).toRingHom = φ :=
  rfl

variable [Fact (t ≠ 0)]

theorem exists_algHom_eq_SpecMap_comp_ι₀
    (x : Spec (CommRingCat.of K) ⟶ CurveModel.glued K t) (hx2 : x ≫ CurveModel.gluedToBase K t = 𝟙 _)
    (hx : x.base (IsLocalRing.closedPoint K) ∈ Set.range (CurveModel.ι₀ K t).base) :
    ∃ φ : ↥(CurveModel.chartRing K ({t} : Set L)) →ₐ[K] K,
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ CurveModel.ι₀ K t = x := by
  have hrange : Set.range x.base ⊆ Set.range (CurveModel.ι₀ K t).base := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [hp]
    exact hx
  have hfac := IsOpenImmersion.lift_fac (CurveModel.ι₀ K t) x hrange
  have h1 : IsOpenImmersion.lift (CurveModel.ι₀ K t) x hrange ≫
      (CurveModel.ι₀ K t ≫ CurveModel.gluedToBase K t) = 𝟙 _ := by
    rw [← Category.assoc, hfac]
    exact hx2
  rw [CurveModel.ι₀_gluedToBase, ← Spec.map_preimage (IsOpenImmersion.lift (CurveModel.ι₀ K t) x hrange),
    ← Spec.map_comp] at h1
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective (h1.trans (Spec.map_id _).symm))
  refine ⟨toAlgHom K (Spec.preimage (IsOpenImmersion.lift (CurveModel.ι₀ K t) x hrange)).hom h2, ?_⟩
  rw [toAlgHom_toRingHom, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem exists_algHom_eq_SpecMap_comp_ιInf
    (x : Spec (CommRingCat.of K) ⟶ CurveModel.glued K t) (hx2 : x ≫ CurveModel.gluedToBase K t = 𝟙 _)
    (hx : x.base (IsLocalRing.closedPoint K) ∈ Set.range (CurveModel.ιInf K t).base) :
    ∃ φ : ↥(CurveModel.chartRing K ({t⁻¹} : Set L)) →ₐ[K] K,
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ CurveModel.ιInf K t = x := by
  have hrange : Set.range x.base ⊆ Set.range (CurveModel.ιInf K t).base := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [hp]
    exact hx
  have hfac := IsOpenImmersion.lift_fac (CurveModel.ιInf K t) x hrange
  have h1 : IsOpenImmersion.lift (CurveModel.ιInf K t) x hrange ≫
      (CurveModel.ιInf K t ≫ CurveModel.gluedToBase K t) = 𝟙 _ := by
    rw [← Category.assoc, hfac]
    exact hx2
  rw [CurveModel.ιInf_gluedToBase, ← Spec.map_preimage (IsOpenImmersion.lift (CurveModel.ιInf K t) x hrange),
    ← Spec.map_comp] at h1
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective (h1.trans (Spec.map_id _).symm))
  refine ⟨toAlgHom K (Spec.preimage (IsOpenImmersion.lift (CurveModel.ιInf K t) x hrange)).hom h2, ?_⟩
  rw [toAlgHom_toRingHom, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem base_closedPoint_eq_of_eq_SpecMap_comp {R : Type uK} [CommRing R]
    (ι : Spec (CommRingCat.of R) ⟶ CurveModel.glued K t) (φ : R →+* K)
    (x : Spec (CommRingCat.of K) ⟶ CurveModel.glued K t) (hx : Spec.map (CommRingCat.ofHom φ) ≫ ι = x) :
    x.base (IsLocalRing.closedPoint K) = ι.base ((Spec.map (CommRingCat.ofHom φ)).base (IsLocalRing.closedPoint K)) ∧
    ((Spec.map (CommRingCat.ofHom φ)).base (IsLocalRing.closedPoint K)).asIdeal = RingHom.ker φ := by
  constructor
  · rw [← hx]; rfl
  · show Ideal.comap φ (IsLocalRing.maximalIdeal K) = RingHom.ker φ
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]

end Glued

section GluedZero

variable (K : Type) [Field K] {L : Type} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]

theorem mem_range_ιFin_iff_of_pins {N : ℕ} [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (g : CurveModel.glued K t ⟶ ModularCurve.IgusaScheme N ℓ)
    (rF : ↥(chartAlgFin N ℓ) →+* ↥(CurveModel.chartRing K ({t} : Set L)))
    (rI : ↥(chartAlgInf N ℓ) →+* ↥(CurveModel.chartRing K ({t⁻¹} : Set L)))
    (hF : CurveModel.ι₀ K t ≫ g = Spec.map (CommRingCat.ofHom rF) ≫ ModularCurve.IgusaScheme.ιFin N ℓ)
    (hI : CurveModel.ιInf K t ≫ g = Spec.map (CommRingCat.ofHom rI) ≫ ModularCurve.IgusaScheme.ιInf N ℓ)
    (hjI : rI (jInvChartInf N ℓ) = CurveModel.tInvChart K t) (y : CurveModel.glued K t) :
    g.base y ∈ Set.range (ModularCurve.IgusaScheme.ιFin N ℓ).base ↔ y ∈ Set.range (CurveModel.ι₀ K t).base := by
  rcases CurveModel.mem_range_ι₀_or_mem_range_ιInf K t y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · refine ⟨fun _ => ⟨x₀, rfl⟩, fun _ => ⟨(Spec.map (CommRingCat.ofHom rF)).base x₀, ?_⟩⟩
    change (Spec.map (CommRingCat.ofHom rF) ≫ ModularCurve.IgusaScheme.ιFin N ℓ).base x₀ = (CurveModel.ι₀ K t ≫ g).base x₀
    rw [hF]
  · have hz : g.base ((CurveModel.ιInf K t).base z) =
        (ModularCurve.IgusaScheme.ιInf N ℓ).base ((Spec.map (CommRingCat.ofHom rI)).base z) := by
      change (CurveModel.ιInf K t ≫ g).base z = (Spec.map (CommRingCat.ofHom rI) ≫ ModularCurve.IgusaScheme.ιInf N ℓ).base z
      rw [hI]
    rw [hz, IgusaSide.ιInf_mem_range_ιFin_iff, CurveModel.ιInf_mem_range_ι₀_iff]
    show jInvChartInf N ℓ ∉ z.asIdeal.comap rI ↔ _
    rw [Ideal.mem_comap]
    exact not_congr (iff_of_eq (congrArg (· ∈ z.asIdeal) hjI))

end GluedZero

namespace IgusaSide

variable {N : ℕ} [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]

set_option synthInstance.maxHeartbeats 1600000 in
theorem range_fFin : Set.range (ModularCurve.IgusaScheme.fFin N ℓ).base =
    ((PrimeSpectrum.basicOpen (jChartFin N ℓ) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(chartAlgFin N ℓ))) : Set (PrimeSpectrum ↥(chartAlgFin N ℓ))) := by
  letI := (ModularCurve.IgusaScheme.inclFin N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin N ℓ
  exact PrimeSpectrum.localization_away_comap_range ↥(chartAlgMid N ℓ) (jChartFin N ℓ)

theorem ιFin_mem_range_ιInf_iff (x₀ : ModularCurve.IgusaScheme.XFin N ℓ) :
    (ModularCurve.IgusaScheme.ιFin N ℓ).base x₀ ∈ Set.range (ModularCurve.IgusaScheme.ιInf N ℓ).base ↔
      jChartFin N ℓ ∉ x₀.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fFin, Set.mem_range]
  constructor
  · rintro ⟨xi, h⟩
    obtain ⟨w, hw, -⟩ := (ιFin_eq_ιInf_iff x₀ xi).mp h.symm
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(ModularCurve.IgusaScheme.fInf N ℓ).base w, ((ιFin_eq_ιInf_iff _ _).mpr ⟨w, rfl, rfl⟩).symm⟩

end IgusaSide

section GluedInf

variable (K : Type) [Field K] {L : Type} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]

theorem mem_range_ιInf_iff_of_pins {N : ℕ} [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (g : CurveModel.glued K t ⟶ ModularCurve.IgusaScheme N ℓ)
    (rF : ↥(chartAlgFin N ℓ) →+* ↥(CurveModel.chartRing K ({t} : Set L)))
    (rI : ↥(chartAlgInf N ℓ) →+* ↥(CurveModel.chartRing K ({t⁻¹} : Set L)))
    (hF : CurveModel.ι₀ K t ≫ g = Spec.map (CommRingCat.ofHom rF) ≫ ModularCurve.IgusaScheme.ιFin N ℓ)
    (hI : CurveModel.ιInf K t ≫ g = Spec.map (CommRingCat.ofHom rI) ≫ ModularCurve.IgusaScheme.ιInf N ℓ)
    (hjF : rF (jChartFin N ℓ) = CurveModel.tChart K t) (y : CurveModel.glued K t) :
    g.base y ∈ Set.range (ModularCurve.IgusaScheme.ιInf N ℓ).base ↔ y ∈ Set.range (CurveModel.ιInf K t).base := by
  rcases CurveModel.mem_range_ι₀_or_mem_range_ιInf K t y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · have hx : g.base ((CurveModel.ι₀ K t).base x₀) =
        (ModularCurve.IgusaScheme.ιFin N ℓ).base ((Spec.map (CommRingCat.ofHom rF)).base x₀) := by
      change (CurveModel.ι₀ K t ≫ g).base x₀ = (Spec.map (CommRingCat.ofHom rF) ≫ ModularCurve.IgusaScheme.ιFin N ℓ).base x₀
      rw [hF]
    rw [hx, IgusaSide.ιFin_mem_range_ιInf_iff, CurveModel.ι₀_mem_range_ιInf_iff]
    show jChartFin N ℓ ∉ x₀.asIdeal.comap rF ↔ _
    rw [Ideal.mem_comap]
    exact not_congr (iff_of_eq (congrArg (· ∈ x₀.asIdeal) hjF))
  · refine ⟨fun _ => ⟨z, rfl⟩, fun _ => ⟨(Spec.map (CommRingCat.ofHom rI)).base z, ?_⟩⟩
    change (Spec.map (CommRingCat.ofHom rI) ≫ ModularCurve.IgusaScheme.ιInf N ℓ).base z = (CurveModel.ιInf K t ≫ g).base z
    rw [hI]

end GluedInf

section Model

variable (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
  [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]

abbrev jt : ↥(modularFunctionFieldFullC (ResidueField ↥A) p) :=
  ⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) p⟩

theorem jt_ne_zero : jt p A ≠ 0 := fun h =>
  jqModC_ne_zero (ResidueField ↥A) (congrArg Subtype.val h)

scoped instance fact_jt_ne_zero : Fact (jt p A ≠ 0) := ⟨jt_ne_zero p A⟩

theorem transcendental_jt : Transcendental (ResidueField ↥A) (jt p A) := fun h =>
  transcendental_jqModC (ResidueField ↥A)
    ((isAlgebraic_algHom_iff (modularFunctionFieldFullC (ResidueField ↥A) p).val Subtype.val_injective).mpr h)

theorem finiteDimensional_adjoin_jt (hℓp : ¬ ℓ ∣ p) (hA : A.LiesOverPrime ℓ) :
    FiniteDimensional ↥(IntermediateField.adjoin (ResidueField ↥A) ({jt p A} : Set ↥(modularFunctionFieldFullC (ResidueField ↥A) p)))
      ↥(modularFunctionFieldFullC (ResidueField ↥A) p) := by
  have key : ∀ (E : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))
      (hE : E = modularFunctionFieldC (ResidueField ↥A) p) (hx : jqModC (ResidueField ↥A) ∈ E),
      FiniteDimensional ↥(IntermediateField.adjoin (ResidueField ↥A) ({(⟨jqModC (ResidueField ↥A), hx⟩ : ↥E)} : Set ↥E)) ↥E := by
    rintro E rfl hx
    exact finiteDimensional_adjoin_jqModC (N := p) A
  exact key _ (modularFunctionFieldFullC_eq_modularFunctionFieldC_residueField p ℓ hℓp A hA) _

theorem isSeparable_adjoin_jt (hℓp : ¬ ℓ ∣ p) (hA : A.LiesOverPrime ℓ) :
    Algebra.IsSeparable
      ↥(IntermediateField.adjoin (ResidueField ↥A) ({jt p A} : Set ↥(modularFunctionFieldFullC (ResidueField ↥A) p)))
      ↥(modularFunctionFieldFullC (ResidueField ↥A) p) := by
  haveI := finiteDimensional_adjoin_jt p ℓ A hℓp hA
  exact isSeparable_adjoin_jqModC_of_isAlgebraic (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p)
    (jqModC_mem_full (ResidueField ↥A) p)

end Model

section QExp

variable (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
  [CharP (ResidueField ↥A) ℓ]

abbrev bar (b : ↥(modularFunctionFieldFull p)) : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (b : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) b.2⟩

theorem coe_bar (b : ↥(modularFunctionFieldFull p)) :
    ((bar p b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (b : LaurentSeries ℚ) :=
  rfl

def barHom : ↥(modularFunctionFieldFull p) →+* laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p) where
  toFun := bar p
  map_one' := Subtype.ext (by simp [coe_bar])
  map_mul' x y := Subtype.ext (by simp [coe_bar])
  map_zero' := Subtype.ext (by simp [coe_bar])
  map_add' x y := Subtype.ext (by simp [coe_bar])

@[scoped simp] theorem barHom_apply (b : ↥(modularFunctionFieldFull p)) : barHom p b = bar p b := rfl

theorem bar_jFull : bar p (jFull p) = CharPModel.jBar p := Subtype.ext rfl

theorem bar_jFull_inv : bar p (jFull p)⁻¹ = (CharPModel.jBar p)⁻¹ := by
  rw [← bar_jFull, ← barHom_apply, ← barHom_apply, map_inv₀]

theorem bar_mem_integralCoeffs_fin (fm : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (hfin : ∀ b : ↥(chartAlgFin p ℓ), bar p (b : ↥(modularFunctionFieldFull p)) ∈ fm.BFin) (b : ↥(chartAlgFin p ℓ)) :
    ((bar p (b : ↥(modularFunctionFieldFull p)) : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      integralCoeffs A.toSubring :=
  ModularCurve.mem_integralCoeffs_of_integral_affineBaseFin A p _ (fm.integralFin ⟨_, hfin b⟩)

theorem bar_mem_integralCoeffs_inf (fm : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (hinf : ∀ b : ↥(chartAlgInf p ℓ), bar p (b : ↥(modularFunctionFieldFull p)) ∈ fm.BInf) (b : ↥(chartAlgInf p ℓ)) :
    ((bar p (b : ↥(modularFunctionFieldFull p)) : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      integralCoeffs A.toSubring :=
  ModularCurve.mem_integralCoeffs_of_integral_affineBaseInf A p _ (fm.integralInf ⟨_, hinf b⟩)

theorem coe_piFin_bar_eq (fm fm' : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (hfin : ∀ b : ↥(chartAlgFin p ℓ), bar p (b : ↥(modularFunctionFieldFull p)) ∈ fm.BFin)
    (hfin' : ∀ b : ↥(chartAlgFin p ℓ), bar p (b : ↥(modularFunctionFieldFull p)) ∈ fm'.BFin) (b : ↥(chartAlgFin p ℓ)) :
    ((fm.piFin ⟨_, hfin b⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) p)) : LaurentSeries (ResidueField ↥A)) =
      ((fm'.piFin ⟨_, hfin' b⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) p)) : LaurentSeries (ResidueField ↥A)) := by
  rw [FibreModel.coe_piFin_eq_coeffRed p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A) fm ⟨_, hfin b⟩
      (bar_mem_integralCoeffs_fin p ℓ A fm hfin b),
    FibreModel.coe_piFin_eq_coeffRed p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A) fm' ⟨_, hfin' b⟩
      (bar_mem_integralCoeffs_fin p ℓ A fm' hfin' b)]

theorem hsep_data (hℓp : ¬ ℓ ∣ p) :
    ((((Classical.choice (ModularCurve.nonempty_modularPolynomialData p)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
      (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable) := by
  have hpκ : (p : ResidueField ↥A) ≠ 0 := fun h0 => hℓp ((CharP.cast_eq_zero_iff (ResidueField ↥A) ℓ p).1 h0)
  exact ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero (ResidueField ↥A) p _ hpκ

theorem coe_piInf_bar_eq (hℓp : ¬ ℓ ∣ p) (fm fm' : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (cc : fm.CuspChart) (cc' : fm'.CuspChart)
    (hinf : ∀ b : ↥(chartAlgInf p ℓ), bar p (b : ↥(modularFunctionFieldFull p)) ∈ fm.BInf)
    (hinf' : ∀ b : ↥(chartAlgInf p ℓ), bar p (b : ↥(modularFunctionFieldFull p)) ∈ fm'.BInf) (b : ↥(chartAlgInf p ℓ)) :
    ((fm.piInf ⟨_, hinf b⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) p)) : LaurentSeries (ResidueField ↥A)) =
      ((fm'.piInf ⟨_, hinf' b⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) p)) : LaurentSeries (ResidueField ↥A)) := by
  rw [FibreModel.coe_piInf_eq_coeffRed_of_cuspChart p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A) fm cc _
      (hsep_data p ℓ A hℓp) ⟨_, hinf b⟩ (bar_mem_integralCoeffs_inf p ℓ A fm hinf b),
    FibreModel.coe_piInf_eq_coeffRed_of_cuspChart p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A) fm' cc' _
      (hsep_data p ℓ A hℓp) ⟨_, hinf' b⟩ (bar_mem_integralCoeffs_inf p ℓ A fm' hinf' b)]

theorem coeffRed_jBar (fm : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (hmem : ((CharPModel.jBar p : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ integralCoeffs A.toSubring) :
    coeffRed A.toSubring (IsLocalRing.residue ↥A) ⟨_, hmem⟩ = jqModC (ResidueField ↥A) := by
  rw [← FibreModel.coe_piFin_eq_coeffRed p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A) fm ⟨_, fm.jBar_mem⟩ hmem,
    fm.piFin_j]

theorem coe_piFin_eq_coe_piInf_mul_pow (hℓp : ¬ ℓ ∣ p) (fm : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (cc : fm.CuspChart)
    (hfin : ∀ b : ↥(chartAlgFin p ℓ), bar p (b : ↥(modularFunctionFieldFull p)) ∈ fm.BFin)
    (hinf : ∀ b : ↥(chartAlgInf p ℓ), bar p (b : ↥(modularFunctionFieldFull p)) ∈ fm.BInf)
    (b : ↥(chartAlgFin p ℓ)) (b' : ↥(chartAlgInf p ℓ)) (n : ℕ)
    (h : (b : ↥(modularFunctionFieldFull p)) = (b' : ↥(modularFunctionFieldFull p)) * jFull p ^ n) :
    ((fm.piFin ⟨_, hfin b⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) p)) : LaurentSeries (ResidueField ↥A)) =
      ((fm.piInf ⟨_, hinf b'⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) p)) : LaurentSeries (ResidueField ↥A)) *
        jqModC (ResidueField ↥A) ^ n := by
  have hF := bar_mem_integralCoeffs_fin p ℓ A fm hfin b
  have hI := bar_mem_integralCoeffs_inf p ℓ A fm hinf b'
  have hJ : ((CharPModel.jBar p : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ integralCoeffs A.toSubring :=
    ModularCurve.mem_integralCoeffs_of_integral_affineBaseFin A p _ (fm.integralFin ⟨_, fm.jBar_mem⟩)
  rw [FibreModel.coe_piFin_eq_coeffRed p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A) fm ⟨_, hfin b⟩ hF,
    FibreModel.coe_piInf_eq_coeffRed_of_cuspChart p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A) fm cc _
      (hsep_data p ℓ A hℓp) ⟨_, hinf b'⟩ hI,
    ← coeffRed_jBar p ℓ A fm hJ, ← map_pow, ← map_mul]
  congr 1
  apply Subtype.ext
  show ((bar p (b : ↥(modularFunctionFieldFull p)) : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) : LaurentSeries (AlgebraicClosure ℚ)) =
    ((bar p (b' : ↥(modularFunctionFieldFull p)) : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) : LaurentSeries (AlgebraicClosure ℚ)) *
      ((CharPModel.jBar p : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) : LaurentSeries (AlgebraicClosure ℚ)) ^ n
  rw [← bar_jFull, ← SubmonoidClass.coe_pow, ← MulMemClass.coe_mul, ← barHom_apply, ← barHom_apply,
    ← barHom_apply, ← map_pow, ← map_mul, ← h]

end QExp

section Setup

variable (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
  [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
  (ρ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A)
  (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))

include hℓp hA hρ in

theorem special_setup
    [hfdK : FiniteDimensional
      ↥(IntermediateField.adjoin (ResidueField ↥A) ({jt p A} : Set ↥(modularFunctionFieldFullC (ResidueField ↥A) p))) ↥(modularFunctionFieldFullC (ResidueField ↥A) p)] :
    letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∃ (P : closedPoints (CurveModel.glued (ResidueField ↥A) (jt p A)) → Place (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p))
      (_ : IsProper (CurveModel.gluedToBase (ResidueField ↥A) (jt p A)))
      (_ : SmoothOfRelativeDimension 1 (CurveModel.gluedToBase (ResidueField ↥A) (jt p A)))
      (_ : Function.Bijective P)
      (_ : ∀ z : closedPoints (CurveModel.glued (ResidueField ↥A) (jt p A)),
        (((CurveModel.gluedFunctionFieldEquiv (ResidueField ↥A) (jt p A)).symm :
            (CurveModel.glued (ResidueField ↥A) (jt p A)).functionField ≃+* ↥(modularFunctionFieldFullC (ResidueField ↥A) p)).toRingHom.comp
          (algebraMap ((CurveModel.glued (ResidueField ↥A) (jt p A)).presheaf.stalk z.1)
            (CurveModel.glued (ResidueField ↥A) (jt p A)).functionField)).range =
        (P z).toValuationSubring.toSubring)
      (_ : ∀ F : Finset (CurveModel.glued (ResidueField ↥A) (jt p A)),
        ∃ U : (CurveModel.glued (ResidueField ↥A) (jt p A)).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
      (fm₀ : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A)) (_ : fm₀.CuspChart)
      (hfin₀ : ∀ b : ↥(chartAlgFin p ℓ), bar p (b : ↥(modularFunctionFieldFull p)) ∈ fm₀.BFin)
      (hinf₀ : ∀ b : ↥(chartAlgInf p ℓ), bar p (b : ↥(modularFunctionFieldFull p)) ∈ fm₀.BInf)
      (esF : ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin p ℓ) ≃ₐ[ResidueField ↥A]
        ↥(CurveModel.chartRing (ResidueField ↥A) ({jt p A} : Set ↥(modularFunctionFieldFullC (ResidueField ↥A) p))))
      (esI : ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf p ℓ) ≃ₐ[ResidueField ↥A]
        ↥(CurveModel.chartRing (ResidueField ↥A) ({(jt p A)⁻¹} : Set ↥(modularFunctionFieldFullC (ResidueField ↥A) p))))
      (_ : ∀ b : ↥(chartAlgFin p ℓ),
        (((esF ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b)).1 : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) : LaurentSeries (ResidueField ↥A)) =
          ((fm₀.piFin ⟨_, hfin₀ b⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) p)) : LaurentSeries (ResidueField ↥A)))
      (_ : ∀ b : ↥(chartAlgInf p ℓ),
        (((esI ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b)).1 : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) : LaurentSeries (ResidueField ↥A)) =
          ((fm₀.piInf ⟨_, hinf₀ b⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) p)) : LaurentSeries (ResidueField ↥A)))
      (es : CurveModel.glued (ResidueField ↥A) (jt p A) ⟶
        pullback (igusaTo p ℓ) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) (_ : IsIso es),
      es ≫ pullback.snd (igusaTo p ℓ) _ = CurveModel.gluedToBase (ResidueField ↥A) (jt p A) ∧
      CurveModel.ι₀ (ResidueField ↥A) (jt p A) ≫ es ≫ pullback.fst (igusaTo p ℓ) _ =
        Spec.map (CommRingCat.ofHom (esF.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ResidueField ↥A) (B := ↥(chartAlgFin p ℓ))).toRingHom)) ≫
          ModularCurve.IgusaScheme.ιFin p ℓ ∧
      CurveModel.ιInf (ResidueField ↥A) (jt p A) ≫ es ≫ pullback.fst (igusaTo p ℓ) _ =
        Spec.map (CommRingCat.ofHom (esI.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ResidueField ↥A) (B := ↥(chartAlgInf p ℓ))).toRingHom)) ≫
          ModularCurve.IgusaScheme.ιInf p ℓ := by
  letI instAlg : Algebra ↥(GaloisRep.ratLocalizedAt ℓ) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra

  obtain ⟨fm₀, cc₀, hfin₀, hinf₀, -, -⟩ :=
    ModularCurve.IgusaScheme.exists_fibreModel_cuspChart_of_chartAlg_of_lift p ℓ hℓp A hA

  obtain ⟨⟨esF, hesF⟩, ⟨esI, hesI⟩⟩ :=
    ModularCurve.IgusaScheme.exists_algEquiv_residueField_tensor_chartAlg_chartRing_apply_tmul p ℓ hℓp A hA ρ hρ
      fm₀ hfin₀ hinf₀
  have hesF1 : ∀ b : ↥(chartAlgFin p ℓ),
      (((esF ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b)).1 : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) : LaurentSeries (ResidueField ↥A)) =
        ((fm₀.piFin ⟨_, hfin₀ b⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) p)) : LaurentSeries (ResidueField ↥A)) := by
    intro b; rw [hesF 1 b, map_one, one_mul]
  have hesI1 : ∀ b : ↥(chartAlgInf p ℓ),
      (((esI ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b)).1 : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) : LaurentSeries (ResidueField ↥A)) =
        ((fm₀.piInf ⟨_, hinf₀ b⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) p)) : LaurentSeries (ResidueField ↥A)) := by
    intro b; rw [hesI 1 b, map_one, one_mul]

  have hj : ((esF ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jChartFin p ℓ)) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) = jt p A := by
    apply Subtype.ext
    rw [hesF1]
    have hb : (⟨_, hfin₀ (jChartFin p ℓ)⟩ : fm₀.BFin) = ⟨CharPModel.jBar p, fm₀.jBar_mem⟩ :=
      Subtype.ext (bar_jFull p)
    rw [hb, fm₀.piFin_j]
  have hjInv : ((esI ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jInvChartInf p ℓ)) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) = (jt p A)⁻¹ := by
    apply Subtype.ext
    rw [hesI1]
    have hb : (⟨_, hinf₀ (jInvChartInf p ℓ)⟩ : fm₀.BInf) = ⟨(CharPModel.jBar p)⁻¹, fm₀.jInvBar_mem⟩ :=
      Subtype.ext (bar_jFull_inv p)
    rw [hb, fm₀.piInf_jInv]
    rfl
  have hcompat : ∀ (b : ↥(chartAlgFin p ℓ)) (b' : ↥(chartAlgInf p ℓ)) (n : ℕ),
      ((b : ↥(modularFunctionFieldFull p)) = (b' : ↥(modularFunctionFieldFull p)) * jFull p ^ n) →
      ((esF ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) =
        (esI ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b') : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) * jt p A ^ n) := by
    intro b b' n h
    apply Subtype.ext
    rw [hesF1, MulMemClass.coe_mul, SubmonoidClass.coe_pow, hesI1]
    exact coe_piFin_eq_coe_piInf_mul_pow p ℓ A hℓp fm₀ cc₀ hfin₀ hinf₀ b b' n h

  haveI := isSeparable_adjoin_jt p ℓ A hℓp hA
  obtain ⟨hPr, hSm, ⟨P, hPbij, hPst⟩, hAff⟩ :=
    AlgebraicCurve.CurveModel.isProper_smooth_places_affineCover_glued (ResidueField ↥A)
      (L := ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) (jt p A) (transcendental_jt p A)

  obtain ⟨es, hes_iso, hes, hpinF, hpinI⟩ :=
    ModularCurve.IgusaScheme.exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing p ℓ (ResidueField ↥A)
      (jt p A) esF esI hj hjInv hcompat
  exact ⟨P, hPr, hSm, hPbij, hPst, hAff, fm₀, cc₀, hfin₀, hinf₀, esF, esI, hesF1, hesI1, es, hes_iso, hes, hpinF, hpinI⟩

end Setup

section Pins

variable (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
  [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
  (ρ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A)
  (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))

include hℓp hA hρ in

theorem exists_Ms_es_centrePins :
    ∃ (Ms : CurveModel (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p))
    (es : Ms.C ⟶ pullback (igusaTo p ℓ) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ))))
    (_ : IsIso es)
    (_ : es ≫ pullback.snd (igusaTo p ℓ) _ = Ms.toBase),
      (∀ (fm : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A)) (cc : fm.CuspChart)
          (hfin : ∀ b : chartAlgFin p ℓ, bar p (b : ↥(modularFunctionFieldFull p)) ∈ fm.BFin)
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Ms.C // q ≫ Ms.toBase = 𝟙 _})
          (β : ↥(chartAlgFin p ℓ) →+* ResidueField ↥A),
          y.1 ≫ es ≫ pullback.fst (igusaTo p ℓ) _ =
            Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.IgusaScheme.ιFin p ℓ →
          ∀ b : ↥(chartAlgFin p ℓ),
            (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) ∈
              (Ms.pointEquivPlace y).toValuationSubring ∧
            (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) -
                algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) (β b) ∈
              (Ms.pointEquivPlace y).toValuationSubring.nonunits) ∧
      (∀ (fm : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A)) (cc : fm.CuspChart)
          (hinf : ∀ b : chartAlgInf p ℓ, bar p (b : ↥(modularFunctionFieldFull p)) ∈ fm.BInf)
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Ms.C // q ≫ Ms.toBase = 𝟙 _})
          (β : ↥(chartAlgInf p ℓ) →+* ResidueField ↥A),
          y.1 ≫ es ≫ pullback.fst (igusaTo p ℓ) _ =
            Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.IgusaScheme.ιInf p ℓ →
          ∀ b : ↥(chartAlgInf p ℓ),
            (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piInf ⟨_, hinf b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) ∈
              (Ms.pointEquivPlace y).toValuationSubring ∧
            (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piInf ⟨_, hinf b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) -
                algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) (β b) ∈
              (Ms.pointEquivPlace y).toValuationSubring.nonunits) := by
  letI instAlg : Algebra ↥(GaloisRep.ratLocalizedAt ℓ) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  haveI hfdK := finiteDimensional_adjoin_jt p ℓ A hℓp hA
  obtain ⟨P, hPr, hSm, hPbij, hPst, hAff, fm₀, cc₀, hfin₀, hinf₀, esF, esI, hesF, hesI, es, hes_iso, hes, hpinF, hpinI⟩ :=
    special_setup p ℓ hℓp A hA ρ hρ

  let Ms : CurveModel (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) :=
    { C := CurveModel.glued (ResidueField ↥A) (jt p A)
      toBase := CurveModel.gluedToBase (ResidueField ↥A) (jt p A)
      isProper := hPr
      smooth := hSm
      ffEquiv := CurveModel.gluedFunctionFieldEquiv (ResidueField ↥A) (jt p A)
      ffEquiv_algebraMap := CurveModel.gluedFunctionFieldEquiv_algebraMap (ResidueField ↥A) (jt p A)
      placeOfPoint := P
      placeOfPoint_bijective := hPbij
      range_stalk_eq := hPst
      finset_subset_affineOpen := hAff }

  set rF : ↥(chartAlgFin p ℓ) →+* ↥(CurveModel.chartRing (ResidueField ↥A) ({jt p A} : Set ↥(modularFunctionFieldFullC (ResidueField ↥A) p))) :=
    esF.toAlgHom.toRingHom.comp (Algebra.TensorProduct.includeRight
      (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ResidueField ↥A) (B := ↥(chartAlgFin p ℓ))).toRingHom with hrF
  set rI : ↥(chartAlgInf p ℓ) →+* ↥(CurveModel.chartRing (ResidueField ↥A) ({(jt p A)⁻¹} : Set ↥(modularFunctionFieldFullC (ResidueField ↥A) p))) :=
    esI.toAlgHom.toRingHom.comp (Algebra.TensorProduct.includeRight
      (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ResidueField ↥A) (B := ↥(chartAlgInf p ℓ))).toRingHom with hrI
  have rF_apply : ∀ b, rF b = esF ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b) := fun b => rfl
  have rI_apply : ∀ b, rI b = esI ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b) := fun b => rfl
  have hjF : rF (jChartFin p ℓ) = CurveModel.tChart (ResidueField ↥A) (jt p A) := by
    apply Subtype.ext
    apply Subtype.ext
    rw [rF_apply, hesF]
    have hb : (⟨_, hfin₀ (jChartFin p ℓ)⟩ : fm₀.BFin) = ⟨CharPModel.jBar p, fm₀.jBar_mem⟩ := Subtype.ext (bar_jFull p)
    rw [hb, fm₀.piFin_j]
    rfl
  have hjI : rI (jInvChartInf p ℓ) = CurveModel.tInvChart (ResidueField ↥A) (jt p A) := by
    apply Subtype.ext
    apply Subtype.ext
    rw [rI_apply, hesI]
    have hb : (⟨_, hinf₀ (jInvChartInf p ℓ)⟩ : fm₀.BInf) = ⟨(CharPModel.jBar p)⁻¹, fm₀.jInvBar_mem⟩ :=
      Subtype.ext (bar_jFull_inv p)
    rw [hb, fm₀.piInf_jInv]
    rfl
  have hF' : CurveModel.ι₀ (ResidueField ↥A) (jt p A) ≫ (es ≫ pullback.fst (igusaTo p ℓ) _) =
      Spec.map (CommRingCat.ofHom rF) ≫ ModularCurve.IgusaScheme.ιFin p ℓ := hpinF
  have hI' : CurveModel.ιInf (ResidueField ↥A) (jt p A) ≫ (es ≫ pullback.fst (igusaTo p ℓ) _) =
      Spec.map (CommRingCat.ofHom rI) ≫ ModularCurve.IgusaScheme.ιInf p ℓ := hpinI
  refine ⟨Ms, es, hes_iso, hes, ?_, ?_⟩
  ·
    intro fm cc hfin y β hy b

    have hy0 : (es ≫ pullback.fst (igusaTo p ℓ) _).base (y.1.base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈
        Set.range (ModularCurve.IgusaScheme.ιFin p ℓ).base := by
      refine ⟨(Spec.map (CommRingCat.ofHom β)).base (IsLocalRing.closedPoint (ResidueField ↥A)), ?_⟩
      change (Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.IgusaScheme.ιFin p ℓ).base _ = (y.1 ≫ es ≫ pullback.fst (igusaTo p ℓ) _).base _
      rw [hy]
    have hy1 : y.1.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (CurveModel.ι₀ (ResidueField ↥A) (jt p A)).base :=
      (mem_range_ιFin_iff_of_pins (ResidueField ↥A) (jt p A) _ rF rI hF' hI' hjI _).mp hy0
    obtain ⟨χ, hχ⟩ := exists_algHom_eq_SpecMap_comp_ι₀ (ResidueField ↥A) (jt p A) y.1 y.2 hy1

    have hβ : β = χ.toRingHom.comp rF := by
      apply IgusaSide.ringHom_eq_of_SpecMap_comp_eq (ModularCurve.IgusaScheme.ιFin p ℓ)
      rw [← hy, ← hχ, Category.assoc, hF', ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

    have hcl : y.1.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ closedPoints (CurveModel.glued (ResidueField ↥A) (jt p A)) :=
      (pointEquivClosedPoint Ms.toBase y).2
    let z : closedPoints (CurveModel.glued (ResidueField ↥A) (jt p A)) := ⟨_, hcl⟩
    have hz : z.1 = (CurveModel.ι₀ (ResidueField ↥A) (jt p A)).base
        ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base (IsLocalRing.closedPoint (ResidueField ↥A))) :=
      (base_closedPoint_eq_of_eq_SpecMap_comp (ResidueField ↥A) (jt p A) _ χ.toRingHom y.1 hχ).1
    have hplace : Ms.pointEquivPlace y = P z := rfl
    obtain ⟨hmem, hnon⟩ :=
      AlgebraicCurve.CurveModel.coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iota0 (ResidueField ↥A)
        (jt p A) P hPst χ z hz (esF ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b))

    have hval : (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) =
        (esF ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b)).1 := by
      apply Subtype.ext
      rw [IntermediateField.coe_inclusion, hesF, coe_piFin_bar_eq p ℓ A fm fm₀ hfin hfin₀ b]
    have hχb : χ (esF ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b)) = β b := by
      rw [hβ]; rfl
    rw [hplace, hval, ← hχb]
    exact ⟨hmem, hnon⟩
  ·
    intro fm cc hinf y β hy b
    have hy0 : (es ≫ pullback.fst (igusaTo p ℓ) _).base (y.1.base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈
        Set.range (ModularCurve.IgusaScheme.ιInf p ℓ).base := by
      refine ⟨(Spec.map (CommRingCat.ofHom β)).base (IsLocalRing.closedPoint (ResidueField ↥A)), ?_⟩
      change (Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.IgusaScheme.ιInf p ℓ).base _ = (y.1 ≫ es ≫ pullback.fst (igusaTo p ℓ) _).base _
      rw [hy]
    have hy1 : y.1.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (CurveModel.ιInf (ResidueField ↥A) (jt p A)).base :=
      (mem_range_ιInf_iff_of_pins (ResidueField ↥A) (jt p A) _ rF rI hF' hI' hjF _).mp hy0
    obtain ⟨χ, hχ⟩ := exists_algHom_eq_SpecMap_comp_ιInf (ResidueField ↥A) (jt p A) y.1 y.2 hy1
    have hβ : β = χ.toRingHom.comp rI := by
      apply IgusaSide.ringHom_eq_of_SpecMap_comp_eq (ModularCurve.IgusaScheme.ιInf p ℓ)
      rw [← hy, ← hχ, Category.assoc, hI', ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcl : y.1.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ closedPoints (CurveModel.glued (ResidueField ↥A) (jt p A)) :=
      (pointEquivClosedPoint Ms.toBase y).2
    let z : closedPoints (CurveModel.glued (ResidueField ↥A) (jt p A)) := ⟨_, hcl⟩
    have hz : z.1 = (CurveModel.ιInf (ResidueField ↥A) (jt p A)).base
        ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base (IsLocalRing.closedPoint (ResidueField ↥A))) :=
      (base_closedPoint_eq_of_eq_SpecMap_comp (ResidueField ↥A) (jt p A) _ χ.toRingHom y.1 hχ).1
    have hplace : Ms.pointEquivPlace y = P z := rfl
    obtain ⟨hmem, hnon⟩ :=
      AlgebraicCurve.CurveModel.coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iotaInf (ResidueField ↥A)
        (jt p A) P hPst χ z hz (esI ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b))
    have hval : (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piInf ⟨_, hinf b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) =
        (esI ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b)).1 := by
      apply Subtype.ext
      rw [IntermediateField.coe_inclusion, hesI, coe_piInf_bar_eq p ℓ A hℓp fm fm₀ cc cc₀ hinf hinf₀ b]
    have hχb : χ (esI ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b)) = β b := by
      rw [hβ]; rfl
    rw [hplace, hval, ← hχb]
    exact ⟨hmem, hnon⟩

end Pins

section PerA

variable (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
  [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]

include hℓp hA in
theorem perA :
    ∃ (ρ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))
    (Ms : CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p))
    (es : Ms.C ⟶ pullback (igusaTo p ℓ) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ))))
    (hes_iso : IsIso es)
    (hes : es ≫ pullback.snd (igusaTo p ℓ) _ = Ms.toBase),
      (∀ (fm : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A)) (cc : fm.CuspChart)
          (hfin : ∀ b : chartAlgFin p ℓ, (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ fm.BFin)
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Ms.C // q ≫ Ms.toBase = 𝟙 _})
          (β : ↥(chartAlgFin p ℓ) →+* ResidueField ↥A),
          y.1 ≫ es ≫ pullback.fst (igusaTo p ℓ) _ =
            Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.IgusaScheme.ιFin p ℓ →
          ∀ b : ↥(chartAlgFin p ℓ),
            (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) ∈
              (Ms.pointEquivPlace y).toValuationSubring ∧
            (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) -
                algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) (β b) ∈
              (Ms.pointEquivPlace y).toValuationSubring.nonunits) ∧
      (∀ (fm : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A)) (cc : fm.CuspChart)
          (hinf : ∀ b : chartAlgInf p ℓ, (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ fm.BInf)
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Ms.C // q ≫ Ms.toBase = 𝟙 _})
          (β : ↥(chartAlgInf p ℓ) →+* ResidueField ↥A),
          y.1 ≫ es ≫ pullback.fst (igusaTo p ℓ) _ =
            Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.IgusaScheme.ιInf p ℓ →
          ∀ b : ↥(chartAlgInf p ℓ),
            (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piInf ⟨_, hinf b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) ∈
              (Ms.pointEquivPlace y).toValuationSubring ∧
            (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piInf ⟨_, hinf b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) -
                algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) (β b) ∈
              (Ms.pointEquivPlace y).toValuationSubring.nonunits)  := by
  obtain ⟨ρ, hρ⟩ := ValuationSubring.exists_ratLocalizedAt_ringHom_of_liesOverPrime ℓ A hA
  obtain ⟨Ms, es, hes_iso, hes, hF, hI⟩ := exists_Ms_es_centrePins p ℓ hℓp A hA ρ hρ
  exact ⟨ρ, hρ, Ms, es, hes_iso, hes, hF, hI⟩

end PerA

end D628
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_spBase_and_cuspChart_centrePin_of_genericFibre_iso_ofGenerator.D628"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_spBase_and_cuspChart_centrePin_of_genericFibre_iso_ofGenerator.D628"

set_option autoImplicit false

p2m_open "ModularCurve~jBar" in open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme ModularCurve.CharPModel in

open scoped TensorProduct in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    (htrans : Transcendental (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p))
    [hne : Fact (ModularCurve.CharPModel.jBar p ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p)))
      (modularFunctionFieldBar p)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p)))
      (modularFunctionFieldBar p)]
    (eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin p ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p))))
    (hFin : ∀ b : chartAlgFin p ℓ, ((eFin (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p)))) : modularFunctionFieldBar p)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ : modularFunctionFieldBar p))
    (eInf : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf p ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p))))
    (hInf : ∀ b : chartAlgInf p ℓ, ((eInf (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p)))) : modularFunctionFieldBar p)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ : modularFunctionFieldBar p)) :
    let Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p) :=
      CurveModel.ofGenerator (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p) htrans
    ∀ (eη : Mη.C ⟶ pullback (igusaTo p ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) (_ : IsIso eη)
      (heη : eη ≫ pullback.snd (igusaTo p ℓ) _ = Mη.toBase)
      (hchartFin : AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ)
          (ModularCurve.CharPModel.jBar p) ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
            (B := ↥(chartAlgFin p ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιFin p ℓ)
      (hchartInf : AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ)
          (ModularCurve.CharPModel.jBar p) ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
            (B := ↥(chartAlgInf p ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιInf p ℓ),
    ∃ (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ → (↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ), (Ms A hA).C ⟶ pullback (igusaTo p ℓ) (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ),
      es A hA ≫ pullback.snd (igusaTo p ℓ) _ = (Ms A hA).toBase),
    ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
      [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)],
      ∀ (fm : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A)) (cc : fm.CuspChart)
        (hfin : ∀ b : chartAlgFin p ℓ, (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ fm.BFin)
        (hinf : ∀ b : chartAlgInf p ℓ, (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ fm.BInf),
      (∀ (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C // q ≫ (Ms A hA).toBase = 𝟙 _})
          (β : ↥(chartAlgFin p ℓ) →+* ResidueField ↥A),
          y.1 ≫ es A hA ≫ pullback.fst (igusaTo p ℓ) _ =
            Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.IgusaScheme.ιFin p ℓ →
          ∀ b : ↥(chartAlgFin p ℓ),
            (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) ∈
              ((Ms A hA).pointEquivPlace y).toValuationSubring ∧
            (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) -
                algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) (β b) ∈
              ((Ms A hA).pointEquivPlace y).toValuationSubring.nonunits) ∧
      (∀ (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C // q ≫ (Ms A hA).toBase = 𝟙 _})
          (β : ↥(chartAlgInf p ℓ) →+* ResidueField ↥A),
          y.1 ≫ es A hA ≫ pullback.fst (igusaTo p ℓ) _ =
            Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.IgusaScheme.ιInf p ℓ →
          ∀ b : ↥(chartAlgInf p ℓ),
            (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piInf ⟨_, hinf b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) ∈
              ((Ms A hA).pointEquivPlace y).toValuationSubring ∧
            (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piInf ⟨_, hinf b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) -
                algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) (β b) ∈
              ((Ms A hA).pointEquivPlace y).toValuationSubring.nonunits) := by
  intro Mη eη heη_iso heη hchartFin hchartInf
  choose ρ hρ Ms es hes_iso hes hpin using fun (A : ValuationSubring (AlgebraicClosure ℚ))
      (hA : A.LiesOverPrime ℓ) =>
    letI : CharP (ResidueField ↥A) ℓ := ValuationSubring.charP_residueField_of_liesOverPrime ℓ A hA
    letI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
    D628.perA p ℓ hℓp A hA
  exact ⟨ρ, hρ, Ms, es, hes_iso, hes, fun A hA _ _ fm cc hfin hinf =>
    ⟨(hpin A hA).1 fm cc hfin, (hpin A hA).2 fm cc hinf⟩⟩

end S_ModularCurve_IgusaScheme_exists_spBase_and_cuspChart_centrePin_of_genericFibre_iso_ofGenerator
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_spBase_and_cuspChart_centrePin_of_genericFibre_iso_ofGenerator (solution)
