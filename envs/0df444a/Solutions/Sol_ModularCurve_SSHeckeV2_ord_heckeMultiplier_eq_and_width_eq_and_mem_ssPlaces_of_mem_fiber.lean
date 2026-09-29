-- Prove2me | solution 1 for ModularCurve.SSHeckeV2.ord_heckeMultiplier_eq_and_width_eq_and_mem_ssPlaces_of_mem_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/710b8335-ceda-5259-a2a6-dfbb88491b50

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_CanonicalDivisor
import Theorems.Thm_ModularCurve_restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces
import Theorems.Thm_ModularCurve_exists_ramificationIndexAlong_mul_eq_placeWidth_restrictAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_ModularCurve_ord_heckeMultiplier_eq
import Theorems.Thm_ModularCurve_SSHeckeV2_heckeMultiplier_spec
import Theorems.Thm_ModularCurve_SSHeckeV2_coe_heckeMultiplier_mul_thetaL_eq_smul_qExpand_of_ne_zero
import Theorems.Thm_ModularCurve_ordDifferential_D_jGeomGen_eq_of_not_dvd_of_cast_natAbs_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_eq_ordDifferential_of_perfectField
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_ModularCurve_thetaL_jqNModC_ne_zero
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSHeckeV2_ord_heckeMultiplier_eq_and_width_eq_and_mem_ssPlaces_of_mem_fiber
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.Affine.Point.instFinite GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one"
p2m_attr_erase "simp" "AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve

noncomputable section

namespace HWS

variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
  (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime]

theorem jGeomGen_transcendental (M : ℕ) [NeZero M] : Transcendental K (jGeomGen K M) := by
  intro halg
  exact transcendental_jqModC K (IntermediateField.isAlgebraic_iff.1 halg)

theorem fd_and_sep (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    FiniteDimensional (IntermediateField.adjoin K ({jGeomGen K M} : Set ↥(modularFunctionFieldC K M))) ↥(modularFunctionFieldC K M) ∧
    Algebra.IsSeparable (IntermediateField.adjoin K ({jGeomGen K M} : Set ↥(modularFunctionFieldC K M))) ↥(modularFunctionFieldC K M) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData M
  exact finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC K M data
    (isSeparable_jqNModC_of_natCast_ne_zero K M hM)

theorem fd_and_sep_of_eq (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (S : IntermediateField K (LaurentSeries K)) (hS : S = modularFunctionFieldC K M) (hj : jqModC K ∈ S) :
    FiniteDimensional (IntermediateField.adjoin K ({(⟨jqModC K, hj⟩ : ↥S)} : Set ↥S)) ↥S ∧
    Algebra.IsSeparable (IntermediateField.adjoin K ({(⟨jqModC K, hj⟩ : ↥S)} : Set ↥S)) ↥S := by
  subst hS; exact fd_and_sep K M hM

include hp in
theorem roof_eq (hpNl : ¬ p ∣ N * ℓ) :
    charLDegeneracyRoof K N ℓ = (haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩; modularFunctionFieldC K (N * ℓ)) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩
  rw [charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul K p N ℓ hpNl,
    ← modularFunctionFieldC_eq_modularFunctionFieldFullC K p (N * ℓ) hpNl]

include hp in
theorem ordDiff_D_jGeomGen (hp5 : 5 ≤ p) (hN : (N : K) ≠ 0) (z : Place K ↥(modularFunctionFieldC K N)) (hz : IsAffineGeomPlace K N z) :
    z.ordDiff (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) = (placeRamificationJ N z : ℤ) - 1 := by
  haveI := isCurveOver_modularFunctionFieldC_of_perfectField K N
  haveI : FiniteDimensional (IntermediateField.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))) ↥(modularFunctionFieldC K N) :=
    (fd_and_sep K N hN).1
  haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))) ↥(modularFunctionFieldC K N) :=
    (fd_and_sep K N hN).2
  haveI : Algebra.EssFiniteType K ↥(modularFunctionFieldC K N) :=
    essFiniteType_of_transcendental_of_finiteDimensional (jGeomGen_transcendental K N) inferInstance
  haveI : ∀ w : Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  haveI : Nontrivial (Ω[↥(modularFunctionFieldC K N)⁄K]) :=
    ⟨⟨_, 0, KaehlerDifferential.D_ne_zero_of_transcendental K (jGeomGen K N) (jGeomGen_transcendental K N)⟩⟩
  rw [Place.ordDiff_eq_ordDifferential_of_perfectField]
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).2 h)
  exact (ordDifferential_D_jGeomGen_eq_of_not_dvd_of_cast_natAbs_ne_zero p hp5 N hpN K z).1 hz

include hp hℓ in
theorem main (hp5 : 5 ≤ p) (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (x : Place K ↥(modularFunctionFieldC K N)) (hx : x ∈ ssPlaces p N K)
    (S : Finset (Place K ↥(charLDegeneracyRoof K N ℓ)))
    (hSx : ∀ y : Place K ↥(charLDegeneracyRoof K N ℓ), y ∈ S ↔ y.restrictAlong (heckeAlphaC K N ℓ) hα = x) :
    (∀ y ∈ S,
      y.ord (heckeMultiplier N K ℓ)
        = (Place.ramificationIndexAlong (heckeBetaC K N ℓ) y : ℤ)
            * (placeRamificationJ N (y.restrictAlong (heckeBetaC K N ℓ) hβ) : ℤ)
          - (Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) * (placeRamificationJ N x : ℤ)) ∧
    (∀ y ∈ S,
      (Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) * (placeWidth N (y.restrictAlong (heckeBetaC K N ℓ) hβ) : ℤ)
        = (Place.ramificationIndexAlong (heckeBetaC K N ℓ) y : ℤ) * (placeWidth N x : ℤ)) ∧
    (∀ y ∈ S, y.restrictAlong (heckeBetaC K N ℓ) hβ ∈ ssPlaces p N K) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).2 h)
  have hℓK : (ℓ : K) ≠ 0 := by
    intro h; have := (CharP.cast_eq_zero_iff K p ℓ).1 h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hp.out hℓ.out).1 this).symm
  have hNl : ((N * ℓ : ℕ) : K) ≠ 0 := by push_cast; exact mul_ne_zero hN hℓK
  have hpNl : ¬ p ∣ N * ℓ := fun h => hNl ((CharP.cast_eq_zero_iff K p _).2 h)

  have hyα : ∀ y ∈ S, y.restrictAlong (heckeAlphaC K N ℓ) hα ∈ ssPlaces p N K := fun y hy => by rw [(hSx y).1 hy]; exact hx
  have hSres : ∀ y ∈ S, y.restrictAlong (heckeBetaC K N ℓ) hβ ∈ ssPlaces p N K := fun y hy =>
    (restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces p hp5 K N ℓ hN hℓN hℓp hα hβ y).1 (hyα y hy)
  have hTK2 : ∀ y ∈ S, ∃ w : ℕ, 1 ≤ w ∧
      Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y * w = placeWidth N x ∧
      Place.ramificationIndexAlong (heckeBetaC K N ℓ) y * w = placeWidth N (y.restrictAlong (heckeBetaC K N ℓ) hβ) := by
    intro y hy
    obtain ⟨w, hw, h1, h2⟩ := exists_ramificationIndexAlong_mul_eq_placeWidth_restrictAlong_heckeAlphaC_heckeBetaC
      p hp5 K N ℓ hN hℓN hℓp hα hβ y (hyα y hy)
    rw [(hSx y).1 hy] at h1
    exact ⟨w, hw, h1, h2⟩
  have hW : ∀ y ∈ S,
      (Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) * (placeWidth N (y.restrictAlong (heckeBetaC K N ℓ) hβ) : ℤ)
        = (Place.ramificationIndexAlong (heckeBetaC K N ℓ) y : ℤ) * (placeWidth N x : ℤ) := by
    intro y hy
    obtain ⟨w, hw, h1, h2⟩ := hTK2 y hy
    have := congrArg (fun n : ℕ => (n : ℤ)) h1; have := congrArg (fun n : ℕ => (n : ℤ)) h2
    push_cast at *
    rw [← h1, ← h2]; push_cast; ring

  have hu3 : ∀ z : Place K ↥(modularFunctionFieldC K N), placeWidth N z ≤ 3 := by
    intro z; unfold placeWidth
    exact le_trans (Nat.div_le_self _ _) (by unfold jWidth; split_ifs <;> norm_num)
  have hecast : ∀ e w u : ℕ, 1 ≤ w → e * w = u → 1 ≤ u → u ≤ 3 → ((e : ℕ) : K) ≠ 0 := by
    intro e w u hw hewu hu1 hu h0
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h; simp at hewu; omega
      · exact h
    have he3 : e ≤ 3 := by nlinarith
    have hpe : p ∣ e := (CharP.cast_eq_zero_iff K p e).1 h0
    have := Nat.le_of_dvd he1 hpe
    omega
  have hu1 : ∀ z : Place K ↥(modularFunctionFieldC K N), z ∈ ssPlaces p N K → 1 ≤ placeWidth N z := by
    intro z hz
    obtain ⟨hrat, haff, -⟩ := hz
    have hepos : 0 < placeRamificationJ N z := by
      have h := ord_sub_evalAt_pos_of_isRational hrat haff.1 (jGeomGen_sub_algebraMap_ne_zero K N (z.evalAt (jGeomGen K N)))
      unfold placeRamificationJ; omega
    have hdvd := placeRamificationJ_dvd_jWidth_of_ord_pos hp5 hpN hepos
    have hWpos : 0 < jWidth (z.evalAt (jGeomGen K N)) := by unfold jWidth; split_ifs <;> norm_num
    unfold placeWidth
    exact Nat.div_pos (Nat.le_of_dvd hWpos hdvd) hepos
  refine ⟨?_, hW, hSres⟩
  intro y hy
  letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
  haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ)

  have hspec := SSHeckeV2.heckeMultiplier_spec p hp5 K N hN ℓ hℓN hℓK
  rw [KaehlerDifferential.map_D] at hspec
  have hD : KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jGeomGen K N))
      = heckeMultiplier N K ℓ • pullbackDiff (heckeAlphaC K N ℓ)
          (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) := by
    rw [pullbackDiff_D]; exact hspec

  haveI : FiniteDimensional (IntermediateField.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))) ↥(modularFunctionFieldC K N) :=
    (fd_and_sep K N hN).1
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))) ↥(modularFunctionFieldC K N) :=
    Algebra.IsAlgebraic.of_finite _ _
  set xα : ↥(charLDegeneracyRoof K N ℓ) := heckeAlphaC K N ℓ (jGeomGen K N) with hxα
  have hxcoe : (xα : LaurentSeries K) = jqModC K := coe_heckeAlphaC K N ℓ (jGeomGen K N)
  have hjmem : jqModC K ∈ charLDegeneracyRoof K N ℓ := hxcoe ▸ xα.2
  have hxeq : xα = ⟨jqModC K, hjmem⟩ := Subtype.ext hxcoe
  have hfs := fd_and_sep_of_eq K (N * ℓ) hNl _ (roof_eq p K N ℓ hpNl) hjmem
  haveI : FiniteDimensional ↥(IntermediateField.adjoin K ({xα} : Set ↥(charLDegeneracyRoof K N ℓ))) ↥(charLDegeneracyRoof K N ℓ) := by
    rw [hxeq]; exact hfs.1
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin K ({xα} : Set ↥(charLDegeneracyRoof K N ℓ))) ↥(charLDegeneracyRoof K N ℓ) := by
    rw [hxeq]; exact hfs.2

  have hxt : Transcendental K xα := by
    intro halg; exact transcendental_jqModC K (hxcoe ▸ IntermediateField.isAlgebraic_iff.1 halg)
  have hDα : KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) xα ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental K xα hxt
  have hhq := SSHeckeV2.coe_heckeMultiplier_mul_thetaL_eq_smul_qExpand_of_ne_zero p hp5 K N hN ℓ hℓN hℓK
  have hT0 : thetaL K (jqModC K) ≠ 0 := by
    have h1 := ModularCurve.thetaL_jqNModC_ne_zero K 1 (by simp); rwa [jqNModC_one] at h1
  have hh0 : heckeMultiplier N K ℓ ≠ 0 := by
    intro h0
    rw [h0, ZeroMemClass.coe_zero, zero_mul] at hhq
    have : qExpand K ℓ (thetaL K (jqModC K)) = 0 := by
      have := hhq.symm; rwa [smul_eq_zero, or_iff_right hℓK] at this
    exact hT0 (qExpand_injective (R := K) ℓ (by rw [this, map_zero]))
  have hDβ : KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jGeomGen K N)) ≠ 0 := by
    rw [hD, pullbackDiff_D]; exact smul_ne_zero hh0 hDα

  obtain ⟨w, hw, h1, h2⟩ := hTK2 y hy
  have heα := hecast _ _ _ hw h1 (hu1 x hx) (hu3 x)
  have heβ := hecast _ _ _ hw h2 (hu1 _ (hSres y hy)) (hu3 _)

  have H := ord_heckeMultiplier_eq K N ℓ hℓN hα hβ (heckeMultiplier N K ℓ) hD hDα hDβ y heα heβ
  rw [H, ordDiff_D_jGeomGen p K N hp5 hN _ (hSres y hy).2.1, (hSx y).1 hy, ordDiff_D_jGeomGen p K N hp5 hN x hx.2.1]
  ring

end HWS

end

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (x : Place K ↥(modularFunctionFieldC K N)) (hx : x ∈ ssPlaces p N K)
    (S : Finset (Place K ↥(charLDegeneracyRoof K N ℓ)))
    (hSx : ∀ y : Place K ↥(charLDegeneracyRoof K N ℓ), y ∈ S ↔ y.restrictAlong (heckeAlphaC K N ℓ) hα = x) :
    (∀ y ∈ S,
      y.ord (ModularCurve.heckeMultiplier N K ℓ)
        = (Place.ramificationIndexAlong (heckeBetaC K N ℓ) y : ℤ)
            * (placeRamificationJ N (y.restrictAlong (heckeBetaC K N ℓ) hβ) : ℤ)
          - (Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) * (placeRamificationJ N x : ℤ)) ∧
    (∀ y ∈ S,
      (Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) * (placeWidth N (y.restrictAlong (heckeBetaC K N ℓ) hβ) : ℤ)
        = (Place.ramificationIndexAlong (heckeBetaC K N ℓ) y : ℤ) * (placeWidth N x : ℤ)) ∧
    (∀ y ∈ S, y.restrictAlong (heckeBetaC K N ℓ) hβ ∈ ssPlaces p N K) :=
  HWS.main p K N ℓ hp5 hN hℓN hℓp hα hβ x hx S hSx

end S_ModularCurve_SSHeckeV2_ord_heckeMultiplier_eq_and_width_eq_and_mem_ssPlaces_of_mem_fiber
end P2MW
export P2MW.S_ModularCurve_SSHeckeV2_ord_heckeMultiplier_eq_and_width_eq_and_mem_ssPlaces_of_mem_fiber (solution)
