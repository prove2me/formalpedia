-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_ringHom_residue_eq_and_mem_iff_of_branchPlace_igusaEnd_igusaBranch_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/4deefdd8-afee-54ed-8899-5064e4c84cf6

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_iff_map_mem_of_forall_place_eq_of_testFamily
import Theorems.Thm_ModularCurve_FullLevel_exists_rational_integral_cuspRegular_evalAt_ne_of_isRational_of_ne
import Theorems.Thm_ModularCurve_exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jqModC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_ringHom_residue_eq_and_mem_iff_of_branchPlace_igusaEnd_igusaBranch_of_prime
p2m_attr_erase "instance" "AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace IgOverSAux

theorem residue_algebraMap_place {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    IsLocalRing.residue ↥v.toValuationSubring (algebraMap K ↥v.toValuationSubring c) =
      algebraMap K v.ResidueField c :=
  Ideal.Quotient.mk_algebraMap K _ c

theorem mem_and_evalAt_eq_of_sub_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {x : F} {c : K} (h : x - algebraMap K F c ∈ v.toValuationSubring.nonunits) :
    x ∈ v.toValuationSubring ∧ v.evalAt x = c := by
  have hmem : x - algebraMap K F c ∈ v.toValuationSubring := v.toValuationSubring.nonunits_subset h
  have hx : x ∈ v.toValuationSubring := by
    have := add_mem hmem (v.algebraMap_mem' c)
    rwa [sub_add_cancel] at this
  refine ⟨hx, ?_⟩
  rw [v.evalAt_of_mem hx]
  have hmax : (⟨x - algebraMap K F c, hmem⟩ : ↥v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    ValuationSubring.coe_mem_nonunits_iff.mp h
  have h1 : (⟨x, hx⟩ : ↥v.toValuationSubring) =
      ⟨x - algebraMap K F c, hmem⟩ + algebraMap K ↥v.toValuationSubring c := by
    apply Subtype.ext
    rw [AddMemClass.coe_add, Place.coe_algebraMap, sub_add_cancel]
  rw [h1, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, zero_add, residue_algebraMap_place,
    v.residueInv_algebraMap]

theorem sub_algebraMap_evalAt_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {x : F} (hx : x ∈ v.toValuationSubring) :
    x - algebraMap K F (v.evalAt x) ∈ v.toValuationSubring.nonunits := by
  have hmem : x - algebraMap K F (v.evalAt x) ∈ v.toValuationSubring := sub_mem hx (v.algebraMap_mem' _)
  have h1 : (⟨_, hmem⟩ : ↥v.toValuationSubring) = ⟨x, hx⟩ - algebraMap K ↥v.toValuationSubring (v.evalAt x) := by
    apply Subtype.ext
    rw [AddSubgroupClass.coe_sub, Place.coe_algebraMap]
  have : ((⟨_, hmem⟩ : ↥v.toValuationSubring) : F) ∈ v.toValuationSubring.nonunits := by
    rw [ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, h1, map_sub,
      residue_algebraMap_place, v.algebraMap_evalAt hv hx, sub_self]
  exact this

theorem coeffEmb_jq_eq (A : ValuationSubring (AlgebraicClosure ℚ)) :
    coeffEmb (AlgebraicClosure ℚ) jq = coeffMap A.subtype (jqModC A) := by
  show (jq).map (algebraMap ℚ (AlgebraicClosure ℚ)) = (jqModC A).map A.subtype
  rw [← jqModC_rat, map_jqModC, map_jqModC]

theorem inv_mem_of_isUnit {F : Type*} [Field F] (S : ValuationSubring F) (t : ↥S) (ht : IsUnit t) :
    ((t : F))⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := ht
  have h : ((u⁻¹ : (↥S)ˣ) : ↥S) * t = 1 := by rw [← hu, Units.inv_mul]
  have h' : (((u⁻¹ : (↥S)ˣ) : ↥S) : F) * (t : F) = 1 := by
    have := congrArg Subtype.val h; simpa using this
  rw [← eq_inv_of_mul_eq_one_left h']
  exact ((u⁻¹ : (↥S)ˣ) : ↥S).2

end IgOverSAux

open IgOverSAux

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 48000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (hGU : ∀ V : ValuationSubring ↥(modularFunctionFieldBar M'),
        (∀ a : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') a ∈ V ↔ a ∈ A) →
        ∀ hj : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ V,
          (∀ p : Polynomial (AlgebraicClosure ℚ), (∀ n, p.coeff n ∈ A) →
            (∃ hm : Polynomial.aeval (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) p ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
              ∀ n, ∃ hc : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (p.coeff n) ∈ V, (⟨_, hc⟩ : ↥V) ∈ maximalIdeal ↥V) →
          ∀ f : ↥(modularFunctionFieldBar M'), f ∈ V ↔ f ∈ R₀.integers)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →

      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
    ∀ (W₀ : ValuationSubring ↥F₀),

      ((∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) ∧
      IsDiscreteValuationRing ↥W₀ ∧
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)})) →

    ∀ (O : Subring ↥F₀) [IsLocalRing ↥O] [IsNoetherianRing ↥O],
      (∀ f : ↥F₀, f ∈ O → f ∈ W₀) →
      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ O) →
      (∀ (f : ↥F₀) (hf : f ∈ O), ∃ (x : ↥k₀) (hx : algebraMap ↥k₀ ↥F₀ x ∈ O), (x : (AlgebraicClosure ℚ)) ∈ A ∧
              ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) →

      (∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ O ∧ h ∈ O ∧ h ≠ 0 ∧ f * h = g) →
    ∀ (E₀ : ℕ) (_ : 1 ≤ E₀) (hπO : algebraMap ↥k₀ ↥F₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
      (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
      (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ),
      cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) →
      (∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥F₀ x ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                  UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩)) →
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) →
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) →
      ((cy : ↥F₀) ∈ W₀) → (∀ hcy : (cy : ↥F₀) ∈ W₀, (⟨(cy : ↥F₀), hcy⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) →
      (∀ hcx : (cx : ↥F₀) ∈ W₀, (⟨(cx : ↥F₀), hcx⟩ : ↥W₀) ∉ maximalIdeal ↥W₀) →

    ∀ (Wx : ValuationSubring ↥F₀),
                (∀ f : ↥F₀, f ∈ O → f ∈ Wx) →
                (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ Wx) →
                IsDiscreteValuationRing ↥Wx →
                (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hπW⟩ : ↥Wx)}) →
                (∃ t : ↥Wx, ∀ p : Polynomial ↥k₀, (∀ n, ((p.coeff n : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                  (∃ hm : Polynomial.aeval (t : ↥F₀) p ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ n, ∃ hc : algebraMap ↥k₀ ↥F₀ (p.coeff n) ∈ Wx, (⟨_, hc⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                (∀ hcx : (cx : ↥F₀) ∈ Wx, (⟨(cx : ↥F₀), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                (∀ hcy : (cy : ↥F₀) ∈ Wx, (⟨(cy : ↥F₀), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) →
                (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
                  (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
                  (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                    0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                      ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
                    0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                      ↥(modularFunctionFieldBar M'))) →
                  ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
                    (⟨_, hF⟩ : ↥F₀) ∈ Wx ∧
                    (∀ hW : (⟨_, hF⟩ : ↥F₀) ∈ Wx, (⟨_, hW⟩ : ↥Wx) ∈ maximalIdeal ↥Wx ↔
                      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0) ∧
                    ((R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                      (⟨_, hF⟩ : ↥F₀) ∈ O ∧
                      ∀ (hO : (⟨_, hF⟩ : ↥F₀) ∈ O) (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) (hcO : algebraMap ↥k₀ ↥F₀ c ∈ O),
                        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                        ¬ IsUnit ((⟨_, hO⟩ : ↥O) - ⟨_, hcO⟩))) →

    ∀ (FI : Type) [Field FI] [Algebra (ResidueField ↥A) FI] (Rx : RegularProlongation A ↥(fieldBar q M') FI),
      (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ Rx.integers ↔ f ∈ Wx)) →

      (∀ f : ↥(modularFunctionFieldBar M'),
        (IntermediateField.inclusion hle f : ↥(fieldBar q M')) ∈ Rx.integers ↔ f ∈ R₀.integers) →
    ∀ (bx : Place (ResidueField ↥A) FI), bx.IsRational →

      (∀ (f : ↥F₀) (_ : f ∈ O) (hR : (f : ↥(fieldBar q M')) ∈ Rx.integers), Rx.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ bx.toValuationSubring) →
      (∀ (f : ↥F₀) (hf : f ∈ O) (hR : (f : ↥(fieldBar q M')) ∈ Rx.integers), ¬ IsUnit (⟨f, hf⟩ : ↥O) →
          ∃ hm : Rx.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ bx.toValuationSubring,
            (⟨_, hm⟩ : ↥bx.toValuationSubring) ∈ maximalIdeal ↥bx.toValuationSubring) →

      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* FI,
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : ↥(fieldBar q M')) ∈ Rx.integers,
            Rx.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ bx.toValuationSubring) := by
  intro F₀ hK1 hLD W₀ hK2 O _ _ hOW hOk hOres hFrac E₀ hE₀ hπO cx cy u ι γU γV hrel hιc hιx hιy hcyW hcyWm hcxWm
    Wx hOWx hWxk hWxd hWxu hWxt hcxWxm hcyWxm hlaws FI _ _ Rx hRx hint bx hbxrat c1 c2
  classical
  have hqp : q.Prime := Fact.out

  have hAq : ((q : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    have : (((q : ℕ) : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by push_cast; rfl
    rw [this]; exact hA
  haveI : CharP (ResidueField ↥A) q := IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal (↥A) q hAq
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  have hM'κ : ((M' : ℕ) : ResidueField ↥A) ≠ 0 := fun h => hqM' ((CharP.cast_eq_zero_iff (ResidueField ↥A) q M').mp h)
  have hrat : ∀ v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'), v.IsRational := by
    obtain ⟨inst, hst, -, hfin, -⟩ :=
      exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable (ResidueField ↥A) M' hM'κ
    letI := inst
    haveI := hst
    haveI := hfin
    intro v
    exact Place.isRational_of_isAlgClosed v
  have hss : IsSupersingularPlace q M' (ResidueField A)
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) := (hW _).mp s.2
  have hsrat := hss.1
  have hjs : jGeomGen (ResidueField A) M' ∈
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring := hss.2.1.1

  have hinclR : ∀ x : ↥R₀.integers, (IntermediateField.inclusion hle (x : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ Rx.integers :=
    fun x => (hint x).mpr x.2
  let ι₀ : ↥R₀.integers →+* ↥Rx.integers :=
    { toFun := fun x => ⟨IntermediateField.inclusion hle (x : ↥(modularFunctionFieldBar M')), hinclR x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hι₀ : ∀ x : ↥R₀.integers, ((ι₀ x : ↥Rx.integers) : ↥(fieldBar q M')) = IntermediateField.inclusion hle (x : ↥(modularFunctionFieldBar M')) :=
    fun x => rfl
  let ψ : ↥R₀.integers →+* FI := Rx.residue.comp ι₀
  have hψ : ∀ x, ψ x = Rx.residue (ι₀ x) := fun x => rfl

  have hkerle : RingHom.ker R₀.residue ≤ RingHom.ker ψ := by
    intro x hx
    rw [R₀.ker_residue] at hx
    rw [RingHom.mem_ker, hψ, ← RingHom.mem_ker, Rx.ker_residue, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    intro hu
    apply hx
    have hx0 : (x : ↥(modularFunctionFieldBar M')) ≠ 0 := by
      intro h0
      have : ι₀ x = 0 := Subtype.ext (by rw [hι₀, h0, map_zero]; rfl)
      rw [this] at hu; exact not_isUnit_zero hu
    have hinv : ((IntermediateField.inclusion hle (x : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')))⁻¹ ∈ Rx.integers := by
      have := inv_mem_of_isUnit Rx.integers (ι₀ x) hu
      rwa [hι₀] at this
    rw [← map_inv₀, hint] at hinv
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩
  let jj : ↥(modularFunctionFieldC (ResidueField A) M') →+* FI := (R₀.residue.liftOfSurjective R₀.residue_surjective) ⟨ψ, hkerle⟩
  have hjj : ∀ x : ↥R₀.integers, jj (R₀.residue x) = ψ x :=
    fun x => RingHom.liftOfSurjective_comp_apply R₀.residue R₀.residue_surjective ⟨ψ, hkerle⟩ x

  have hjconst : ∀ c : ResidueField ↥A, jj (algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField A) M') c) = algebraMap (ResidueField ↥A) FI c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    rw [← R₀.residue_algebraMap a, hjj, hψ, ← Rx.residue_algebraMap a]
    congr 1
  let φ : ↥(modularFunctionFieldC (ResidueField A) M') →ₐ[ResidueField ↥A] FI :=
    { toRingHom := jj, commutes' := hjconst }
  have hφ : ∀ g, φ g = jj g := fun g => rfl

  let T : Set ↥(modularFunctionFieldC (ResidueField A) M') :=
    {t | t ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ∧
      ∃ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) ∧
        t = R₀.residue ⟨_, hgi⟩}

  have hjA : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [← coeffEmb_jq_eq]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
  obtain ⟨hjint, hjres⟩ := hR₀ (jqModC ↥A) hjA
  have hjeq : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) = ⟨coeffMap A.subtype (jqModC ↥A), hjA⟩ := Subtype.ext (coeffEmb_jq_eq A)
  have hjint' : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers := by rw [hjeq]; exact hjint
  have hjbar : R₀.residue ⟨_, hjint'⟩ = jGeomGen (ResidueField A) M' := by
    apply Subtype.ext
    have : (⟨_, hjint'⟩ : ↥R₀.integers) = ⟨_, hjint⟩ := Subtype.ext hjeq
    rw [this, hjres]
    exact map_jqModC _
  have hjT : jGeomGen (ResidueField A) M' ∈ T :=
    ⟨hjs, jq, modularFunctionField_le_full M' (jq_mem M'), hjint', fun P h => h, hjbar.symm⟩

  have hread : ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
      (hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀)
      (hR : (((⟨_, hF⟩ : ↥F₀) : ↥(fieldBar q M'))) ∈ Rx.integers),
      Rx.residue ⟨((⟨_, hF⟩ : ↥F₀) : ↥(fieldBar q M')), hR⟩ = jj (R₀.residue ⟨_, hgi⟩) := by
    intro g hg hgi hF hR
    rw [hjj, hψ]
    exact congrArg Rx.residue (Subtype.ext rfl)

  have hT_T : ∀ t ∈ T, φ t ∈ bx.toValuationSubring := by
    rintro t ⟨hts, g, hg, hgi, hcusp, rfl⟩
    obtain ⟨hF, -, -, hval⟩ := hlaws g hg hgi hcusp
    obtain ⟨hO_, -⟩ := hval hts
    have hR : (((⟨_, hF⟩ : ↥F₀) : ↥(fieldBar q M'))) ∈ Rx.integers := (hRx _).mpr (hOWx _ hO_)
    have := c1 _ hO_ hR
    rwa [hread g hg hgi hF hR] at this

  have hvan : ∀ t ∈ T, ∀ c : ResidueField A,
      t - algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') c ∈
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring.nonunits →
      φ t - algebraMap (ResidueField A) FI c ∈ bx.toValuationSubring.nonunits := by
    rintro t ⟨hts, g, hg, hgi, hcusp, rfl⟩ c hc

    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective c
    obtain ⟨c₀, hc₀A, hdA, hdm⟩ := hκ (a : AlgebraicClosure ℚ) a.2
    have hc₀ : IsLocalRing.residue ↥A ⟨(c₀ : AlgebraicClosure ℚ), hc₀A⟩ = c := by
      rw [← ha, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      have : (⟨(c₀ : AlgebraicClosure ℚ), hc₀A⟩ : ↥A) - a = -⟨_, hdA⟩ :=
        Subtype.ext (show (c₀ : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ) = -((a : AlgebraicClosure ℚ) - c₀) by ring)
      rw [this]; exact neg_mem hdm
    have heval := (mem_and_evalAt_eq_of_sub_mem_nonunits _ hc).2
    obtain ⟨hF, -, -, hval⟩ := hlaws g hg hgi hcusp
    obtain ⟨hO_, hconst⟩ := hval hts
    have hc₀O : algebraMap ↥k₀ ↥F₀ c₀ ∈ O := (hOk c₀).mp hc₀A
    have hnu := hconst hO_ c₀ hc₀A hc₀O (by rw [hc₀, heval])

    have hfO : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c₀ ∈ O := O.sub_mem hO_ hc₀O
    have hnu' : ¬ IsUnit (⟨(⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c₀, hfO⟩ : ↥O) := by
      have : (⟨(⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c₀, hfO⟩ : ↥O) = ⟨_, hO_⟩ - ⟨_, hc₀O⟩ := Subtype.ext rfl
      rw [this]; exact hnu
    have hR : ((((⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c₀ : ↥F₀)) : ↥(fieldBar q M')) ∈ Rx.integers := (hRx _).mpr (hOWx _ hfO)
    obtain ⟨hm, hmax⟩ := c2 _ hfO hR hnu'

    have hR1 : (((⟨_, hF⟩ : ↥F₀) : ↥(fieldBar q M'))) ∈ Rx.integers := (hRx _).mpr (hOWx _ hO_)
    have hR2 : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c₀ : AlgebraicClosure ℚ) ∈ Rx.integers :=
      (Rx.algebraMap_mem_iff _).mpr hc₀A
    have hcoe : ((((⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c₀ : ↥F₀)) : ↥(fieldBar q M')) =
        (((⟨_, hF⟩ : ↥F₀) : ↥(fieldBar q M'))) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c₀ : AlgebraicClosure ℚ) := rfl
    have hsplit : (⟨_, hR⟩ : ↥Rx.integers) = ⟨_, hR1⟩ - ⟨_, hR2⟩ := Subtype.ext hcoe
    have hres : Rx.residue ⟨_, hR⟩ = φ (R₀.residue ⟨_, hgi⟩) - algebraMap (ResidueField A) FI c := by
      rw [hsplit, map_sub, hread g hg hgi hF hR1, ← hc₀, ← Rx.residue_algebraMap ⟨(c₀ : AlgebraicClosure ℚ), hc₀A⟩]
      rfl
    have hnon : ((⟨_, hm⟩ : ↥bx.toValuationSubring) : FI) ∈ bx.toValuationSubring.nonunits :=
      ValuationSubring.coe_mem_nonunits_iff.mpr hmax
    rw [← hres]; exact hnon

  have hO' : ∃ t ∈ T, ∃ c : ResidueField A,
      t - algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') c ∈
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring.nonunits ∧
      t ≠ algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') c := by
    refine ⟨_, hjT, (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
      (jGeomGen (ResidueField A) M'), sub_algebraMap_evalAt_mem_nonunits _ hsrat hjs, ?_⟩
    intro h
    apply transcendental_jqModC (ResidueField ↥A)
    have h' := congrArg Subtype.val h
    rw [SubalgebraClass.coe_algebraMap] at h'
    change jqModC (ResidueField ↥A) = _ at h'
    rw [h']
    exact isAlgebraic_algebraMap _

  have hsep : ∀ s' : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'),
      (∀ t ∈ T, t ∈ s'.toValuationSubring) →
      (∀ t ∈ T, ∀ c : ResidueField A,
        t - algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') c ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring.nonunits →
        t - algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') c ∈ s'.toValuationSubring.nonunits) →
      s' = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) := by
    intro s' hT' hvan'
    by_contra hne
    have hjs' := hT' _ hjT
    obtain ⟨g, hg, hgi, hcusp, hgs, -, hne'⟩ :=
      exists_rational_integral_cuspRegular_evalAt_ne_of_isRational_of_ne q M' hqM' A hA R₀ hR₀
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) s' hsrat (hrat s') hjs hjs' (Ne.symm hne)
    have ht : R₀.residue ⟨_, hgi⟩ ∈ T := ⟨hgs, g, hg, hgi, hcusp, rfl⟩
    have h1 := hvan' _ ht _ (sub_algebraMap_evalAt_mem_nonunits _ hsrat hgs)
    exact hne' (mem_and_evalAt_eq_of_sub_mem_nonunits _ h1).2.symm

  haveI := finiteDimensional_adjoin_jqModC (N := M') A
  refine ⟨jj, ?_, ?_⟩
  · intro f hf
    exact ⟨hinclR ⟨f, hf⟩, (hjj ⟨f, hf⟩).symm⟩
  · intro g
    have key := AlgebraicCurve.Place.mem_toValuationSubring_iff_map_mem_of_forall_place_eq_of_testFamily
      ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) M'⟩ : ↥(modularFunctionFieldC (ResidueField A) M')))
      φ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) bx T hT_T hvan hO' hsep g
    rw [hφ] at key
    exact key

end S_ModularCurve_FullLevel_exists_ringHom_residue_eq_and_mem_iff_of_branchPlace_igusaEnd_igusaBranch_of_prime
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_ringHom_residue_eq_and_mem_iff_of_branchPlace_igusaEnd_igusaBranch_of_prime (solution)
