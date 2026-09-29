-- Prove2me | solution 1 for ModularCurve.FullLevel.typeII_exhaustion_of_placeCover_of_componentChart_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/3fa6fb71-bdc8-520c-b100-d7b690940702

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_FullLevel_exists_testFamily_forall_isRational_tube_of_forall_evalAt_mem_maximalIdeal
import Theorems.Thm_AlgebraicCurve_ComponentChart_exists_mem_dom_forall_isUnit_evalAt_of_forall_isUnit
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_typeII_exhaustion_of_placeCover_of_componentChart_of_eq_two_of_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
p2m_attr_erase "simp" "ModularCurve.cuspCount_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_typeII_exhaustion_of_placeCover_of_componentChart_of_eq_two_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_typeII_exhaustion_of_placeCover_of_componentChart_of_eq_two_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar jq jq_mem modularFunctionField_le_full coeffMap coeffEmb coeffEmb_mem_laurentBaseChange instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable modularFunctionFieldC ssPlaces isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField FullLevel.exists_testFamily_forall_isRational_tube_of_forall_evalAt_mem_maximalIdeal"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "levelH fieldBar exists_testFamily_forall_isRational_tube_of_forall_evalAt_mem_maximalIdeal"
namespace WClassCharted
p2m_open "ModularCurve.FullLevel ModularCurve"

local notation "𝕂" => AlgebraicClosure ℚ

section Generic
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_iff (P : Place K F) (x : F) : 0 ≤ P.ord x ↔ x ∈ P.toValuationSubring := by
  constructor
  · intro h
    by_cases hx : x = 0
    · rw [hx]; exact zero_mem _
    · exact P.mem_of_ord_nonneg hx h
  · exact fun h => P.ord_nonneg_of_mem h

theorem evalAt_eq_iff (P : Place K F) (hP : P.IsRational) {f : F} (hf : f ∈ P.toValuationSubring) (c : K) :
    P.evalAt f = c ↔ IsLocalRing.residue P.toValuationSubring ⟨f, hf⟩ = algebraMap K P.ResidueField c := by
  constructor
  · rintro rfl; exact (P.algebraMap_evalAt hP hf).symm
  · intro h
    apply P.algebraMap_residueField_injective
    rw [P.algebraMap_evalAt hP hf, h]

theorem evalAt_add (P : Place K F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring)
    (hg : g ∈ P.toValuationSubring) : P.evalAt (f + g) = P.evalAt f + P.evalAt g := by
  rw [evalAt_eq_iff P hP (add_mem hf hg), map_add, P.algebraMap_evalAt hP hf, P.algebraMap_evalAt hP hg, ← map_add]
  rfl

theorem evalAt_mul (P : Place K F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring)
    (hg : g ∈ P.toValuationSubring) : P.evalAt (f * g) = P.evalAt f * P.evalAt g := by
  rw [evalAt_eq_iff P hP (mul_mem hf hg), map_mul, P.algebraMap_evalAt hP hf, P.algebraMap_evalAt hP hg, ← map_mul]
  rfl

theorem evalAt_sub (P : Place K F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring)
    (hg : g ∈ P.toValuationSubring) : P.evalAt (f - g) = P.evalAt f - P.evalAt g := by
  rw [evalAt_eq_iff P hP (sub_mem hf hg), map_sub, P.algebraMap_evalAt hP hf, P.algebraMap_evalAt hP hg, ← map_sub]
  rfl

private theorem _root_.ModularCurve.FullLevel.WClassCharted.algebraMap_mem (P : Place K F) (c : K) : algebraMap K F c ∈ P.toValuationSubring :=
  (algebraMap K P.toValuationSubring c).2

p2m_export "ModularCurve.FullLevel.WClassCharted" "algebraMap_mem"
theorem evalAt_algebraMap (P : Place K F) (hP : P.IsRational) (c : K) :
    P.evalAt (algebraMap K F c) = c := by
  rw [evalAt_eq_iff P hP (algebraMap_mem P c)]
  exact (IsScalarTower.algebraMap_apply K (↥P.toValuationSubring) P.ResidueField c).symm

theorem evalAt_sum (P : Place K F) (hP : P.IsRational) {ι : Type*} (t : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ t, f i ∈ P.toValuationSubring) :
    P.evalAt (∑ i ∈ t, f i) = ∑ i ∈ t, P.evalAt (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [evalAt_eq_iff P hP (zero_mem _), map_zero]; rfl
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalAt_add P hP (hf a (Finset.mem_insert_self a t))
        (sum_mem fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

end Generic

def Small (A : ValuationSubring 𝕂) (x : 𝕂) : Prop := ∃ h : x ∈ A, (⟨x, h⟩ : ↥A) ∈ maximalIdeal ↥A

theorem Small.mem {A : ValuationSubring 𝕂} {x : 𝕂} (h : Small A x) : x ∈ A := h.1

theorem Small.zero (A : ValuationSubring 𝕂) : Small A 0 := ⟨zero_mem _, by
  have : (⟨(0:𝕂), zero_mem A⟩ : ↥A) = 0 := rfl
  rw [this]; exact Ideal.zero_mem _⟩

theorem Small.add {A : ValuationSubring 𝕂} {x y : 𝕂} (hx : Small A x) (hy : Small A y) : Small A (x + y) := by
  obtain ⟨hx, hx'⟩ := hx; obtain ⟨hy, hy'⟩ := hy
  refine ⟨add_mem hx hy, ?_⟩
  have : (⟨x + y, add_mem hx hy⟩ : ↥A) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [this]; exact Ideal.add_mem _ hx' hy'

theorem Small.mul_left {A : ValuationSubring 𝕂} {x y : 𝕂} (hy : y ∈ A) (hx : Small A x) : Small A (y * x) := by
  obtain ⟨hx, hx'⟩ := hx
  refine ⟨mul_mem hy hx, ?_⟩
  have : (⟨y * x, mul_mem hy hx⟩ : ↥A) = ⟨y, hy⟩ * ⟨x, hx⟩ := rfl
  rw [this]; exact Ideal.mul_mem_left _ _ hx'

theorem Small.mul_right {A : ValuationSubring 𝕂} {x y : 𝕂} (hx : Small A x) (hy : y ∈ A) : Small A (x * y) := by
  rw [mul_comm]; exact hx.mul_left hy

theorem Small.sum {A : ValuationSubring 𝕂} {ι : Type*} (t : Finset ι) (f : ι → 𝕂) (hf : ∀ i ∈ t, Small A (f i)) :
    Small A (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Small.zero A
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

section Places
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finite_ord_ne_zero [HasPrincipalDivisors K F] (f : F) (hf : f ≠ 0) :
    Set.Finite {P : Place K F | P.ord f ≠ 0} := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
  refine D.support.finite_toSet.subset fun P hP => ?_
  simp only [Set.mem_setOf_eq] at hP
  exact Finsupp.mem_support_iff.2 (by rw [hD]; exact hP)

theorem isRational_of_isAlgClosed' [IsAlgClosed K] [IsCurveOver K F] (P : Place K F) : P.IsRational := by
  haveI : Module.Finite K P.ResidueField := IsCurveOver.finite_residueField P
  haveI : Algebra.IsIntegral K P.ResidueField := Algebra.IsIntegral.of_finite K P.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := P.ResidueField)).2

theorem exists_transcendental_of_isCurveOver [PerfectField K] [IsCurveOver K F] : ∃ x : F, Transcendental K x := by
  by_contra h
  push_neg at h
  haveI : Algebra.IsAlgebraic K F :=
    ⟨fun x => by have := h x; unfold Transcendental at this; push_neg at this; exact this⟩
  haveI : Algebra.IsSeparable K F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyUnramified K F := Algebra.FormallyUnramified.of_isSeparable K F
  have hs : Subsingleton (Ω[F⁄K]) := Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  exact not_nontrivial_iff_subsingleton.mpr hs (IsCurveOver.instNontrivialKaehler)

theorem infinite_places [IsAlgClosed K] [IsCurveOver K F] [Algebra.EssFiniteType K F] :
    Set.Infinite (Set.univ : Set (Place K F)) := by
  classical
  haveI : PerfectField K := IsAlgClosed.perfectField K
  obtain ⟨t, ht⟩ := exists_transcendental_of_isCurveOver (K := K) (F := F)
  haveI := AlgebraicCurve.IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType ht

  have key : ∀ c : K, ∃ P : Place K F, t - algebraMap K F c ∈ P.toValuationSubring.nonunits := by
    intro c
    let S : Subring F := (Algebra.adjoin K ({t} : Set F)).toSubring
    have htmem : t ∈ Algebra.adjoin K ({t} : Set F) := Algebra.self_mem_adjoin_singleton K t
    have htS : t - algebraMap K F c ∈ S := sub_mem htmem (Subalgebra.algebraMap_mem _ c)

    let φ : Algebra.adjoin K ({t} : Set F) →ₐ[K] K :=
      (Polynomial.aeval c).comp (Polynomial.algEquivOfTranscendental K t ht).symm.toAlgHom
    have hφt : φ ⟨t, htmem⟩ = c := by
      show Polynomial.aeval c ((Polynomial.algEquivOfTranscendental K t ht).symm ⟨t, htmem⟩) = c
      rw [Polynomial.algEquivOfTranscendental_symm_gen]; simp
    let I : Ideal S := Ideal.span {⟨t - algebraMap K F c, htS⟩}
    have hI : I ≠ ⊤ := by
      intro hI
      have h1 : (⟨t - algebraMap K F c, htS⟩ : S) ∈ RingHom.ker φ.toRingHom := by
        rw [RingHom.mem_ker]
        show φ ⟨t - algebraMap K F c, htS⟩ = 0
        have : (⟨t - algebraMap K F c, htS⟩ : Algebra.adjoin K ({t} : Set F)) =
            ⟨t, htmem⟩ - algebraMap K _ c := Subtype.ext rfl
        rw [this, map_sub, hφt, AlgHom.commutes]; simp
      have hle : I ≤ RingHom.ker φ.toRingHom := (Ideal.span_singleton_le_iff_mem _).2 h1
      exact (RingHom.ker_ne_top φ.toRingHom) (top_le_iff.1 (hI ▸ hle))
    obtain ⟨B, hSB, hIB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
    have htB : t - algebraMap K F c ∈ B.nonunits :=
      hIB ⟨⟨_, htS⟩, Ideal.subset_span (Set.mem_singleton _), rfl⟩
    have hBK : ∀ a : K, algebraMap K F a ∈ B := fun a => hSB (Subalgebra.algebraMap_mem _ a)
    have htc : t - algebraMap K F c ≠ 0 := by
      intro h0
      apply ht
      have : t = algebraMap K F c := sub_eq_zero.1 h0
      rw [this]; exact isAlgebraic_algebraMap c
    have hmemB : t - algebraMap K F c ∈ B := B.nonunits_le htB
    have hBtop : B ≠ ⊤ := by
      intro hB
      have hlt := (B.mem_nonunits_iff).1 htB
      have hinv : (t - algebraMap K F c)⁻¹ ∈ B := by rw [hB]; exact Subring.mem_top _
      have hu : IsUnit (⟨_, hmemB⟩ : B) :=
        IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ htc))
      rw [ValuationSubring.valuation_eq_one_iff] at hu
      exact (lt_irrefl _) (hu ▸ hlt)
    obtain ⟨P, hP⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional t B hBK hBtop
    exact ⟨P, hP.symm ▸ htB⟩
  choose Pl hPl using key
  refine Set.infinite_of_injective_forall_mem (f := Pl) ?_ (fun _ => Set.mem_univ _)
  intro c c' hcc
  by_contra hne

  have h1 := (ValuationSubring.mem_nonunits_iff _).1 (hPl c)
  have h2 := (ValuationSubring.mem_nonunits_iff _).1 (hPl c')
  rw [← hcc] at h2
  set V := (Pl c).toValuationSubring with hV
  have hsub : algebraMap K F (c' - c) = (t - algebraMap K F c) - (t - algebraMap K F c') := by
    rw [map_sub]; ring
  have hlt : V.valuation (algebraMap K F (c' - c)) < 1 := by
    rw [hsub, sub_eq_add_neg]
    refine lt_of_le_of_lt (V.valuation.map_add _ _) (max_lt h1 ?_)
    rwa [Valuation.map_neg]
  have hne' : c' - c ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hu : IsUnit (⟨algebraMap K F (c' - c), (Pl c).algebraMap_mem' _⟩ : V) :=
    IsUnit.of_mul_eq_one ⟨algebraMap K F (c' - c)⁻¹, (Pl c).algebraMap_mem' _⟩
      (Subtype.ext (by
        show algebraMap K F (c' - c) * algebraMap K F (c' - c)⁻¹ = 1
        rw [← map_mul, mul_inv_cancel₀ hne', map_one]))
  rw [ValuationSubring.valuation_eq_one_iff] at hu
  exact (lt_irrefl _) (hu ▸ hlt)

end Places

end ModularCurve.FullLevel.WClassCharted

open ModularCurve.FullLevel.WClassCharted in
set_option maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
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
    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A ↥(fieldBar q M') FSS)
    (h0 : ∃ t : FSS, Transcendental (ResidueField A) t)
    (C : ComponentChart A ↥(fieldBar q M') FSS)
    (hCR : C.integers = R.integers)
    (hCres : ∀ (f : ↥(fieldBar q M')) (hC : f ∈ C.integers) (hR : f ∈ R.integers), C.residue ⟨f, hC⟩ = R.residue ⟨f, hR⟩)
    (N : Finset (Place (ResidueField A) FSS))
    (Dx : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M')))
    (T : Place (ResidueField A) FSS → ↥(fieldBar q M'))
    (hdisc : ∀ Q : Place (ResidueField A) FSS, Q ∉ N → R.IsResidueDisc Q (Dx Q) (T Q))
    (hdom : ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ C.dom ↔ ∃ Q, Q ∉ N ∧ P ∈ Dx Q)
    (An : ↥N → Annulus A ↥(fieldBar q M'))
    (hatt : ∀ x : ↥N, ((An x).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
      ∃ hz : (An x).param ∈ R.integers, (x : Place (ResidueField A) FSS).ord (R.residue ⟨(An x).param, hz⟩) = 1 ∧
        ∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers), R.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ (An x).dom, P.ord f = 0) →
          ∀ P ∈ (An x).dom,
            ∃ h : P.evalAt f * (P.evalAt (An x).param) ^ (-((x : Place (ResidueField A) FSS).ord (R.residue ⟨f, hf⟩))) ∈ A,
              IsUnit (⟨_, h⟩ : A))

    (hAnD : ∀ x : ↥N, ∀ Q : Place (ResidueField A) FSS, Q ∉ N → ∀ P, P ∈ (An x).dom → P ∉ Dx Q)
    (hAnAn : ∀ x x' : ↥N, ∀ P, P ∈ (An x).dom → P ∈ (An x').dom → x = x')

    (hcover : ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
      (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P'.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A, IsLocalRing.residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
              (⟨_, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) →
      (∃ Q, Q ∉ N ∧ P ∈ Dx Q) ∨ ∃ x : ↥N, P ∈ (An x).dom)

    (F₁ : Type) [Field F₁] [Algebra (ResidueField A) F₁]
    [IsCurveOver (ResidueField A) F₁] [Algebra.EssFiniteType (ResidueField A) F₁]
    (C₁ : ComponentChart A ↥(fieldBar q M') F₁)

    (hOs : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          (IntermediateField.inclusion hle f : fieldBar q M') ∈ C₁.integers ∧
          ∀ a : A, residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
                - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ C₁.integers,
              (⟨_, h⟩ : ↥C₁.integers) ∈ maximalIdeal ↥C₁.integers)) :

    (∀ f : ↥(fieldBar q M'), (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ C₁.integers) ∨
      ∃ x : ↥N, (∀ f : ↥(fieldBar q M'), (∀ P ∈ (An x).dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ C₁.integers) := by
  classical

  haveI : PerfectField (AlgebraicClosure ℚ) := IsAlgClosed.perfectField _
  obtain ⟨hcurve, hfinT⟩ :=
    ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M')
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(fieldBar q M') := hcurve
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  have hfin : ∀ f : ↥(fieldBar q M'), f ≠ 0 → Set.Finite {P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') | P.ord f ≠ 0} :=
    fun f hf => finite_ord_ne_zero f hf
  have hfinb : ∀ g : F₁, g ≠ 0 → Set.Finite {Q : Place (ResidueField ↥A) F₁ | Q.ord g ≠ 0} :=
    fun g hg => finite_ord_ne_zero g hg
  have hinf : Set.Infinite (Set.univ : Set (Place (ResidueField ↥A) F₁)) := infinite_places
  have hrat : ∀ P ∈ C₁.dom, P.IsRational := fun P _ => isRational_of_isAlgClosed' P

  set O : ValuationSubring ↥(fieldBar q M') := C₁.integers with hO
  have hOA : ∀ x : (AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x ∈ O ↔ x ∈ A := C₁.algebraMap_mem_iff
  have unit_of_res : ∀ (f : ↥(fieldBar q M')) (h : f ∈ C₁.integers), C₁.residue ⟨f, h⟩ ≠ 0 → IsUnit (⟨f, h⟩ : ↥O) := by
    intro f h hres
    by_contra hu
    apply hres
    have hm : (⟨f, h⟩ : ↥C₁.integers) ∈ maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 hu
    rw [← C₁.ker_residue] at hm
    exact hm

  have big : ∀ g : ↥(fieldBar q M'), g ∉ O → ∃ u : ↥(fieldBar q M'), (∃ h : u ∈ O, IsUnit (⟨u, h⟩ : ↥O)) ∧
      ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational → u ∈ P.toValuationSubring →
        (∃ h : P.evalAt u ∈ A, IsUnit (⟨_, h⟩ : ↥A)) → ¬ (g ∈ P.toValuationSubring ∧ P.evalAt g ∈ A) := by
    intro g hg
    have hg0 : g ≠ 0 := by rintro rfl; exact hg (zero_mem _)
    obtain ⟨c, hc, hres⟩ := C₁.exists_smul_mem g hg0
    have hc' : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * g ∈ O := by rw [← Algebra.smul_def]; exact hc
    have hcu : IsUnit (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * g, hc'⟩ : ↥O) := by
      have e : (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * g, hc'⟩ : ↥O) = ⟨c • g, hc⟩ := Subtype.ext (Algebra.smul_def c g).symm
      rw [e]; exact unit_of_res _ hc hres
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hres
      have h0 : ((0 : (AlgebraicClosure ℚ)) • g : ↥(fieldBar q M')) = 0 := zero_smul (AlgebraicClosure ℚ) g
      have : (⟨(0 : (AlgebraicClosure ℚ)) • g, hc⟩ : ↥C₁.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]
    have hcinv : c⁻¹ ∉ A := by
      intro hci
      apply hg
      have : g = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c⁻¹ * (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * g) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      rw [this]; exact mul_mem ((hOA _).2 hci) hc'
    refine ⟨_, ⟨hc', hcu⟩, ?_⟩
    intro P hP huP ⟨huA, huU⟩ ⟨hgP, hgA⟩
    apply hcinv
    have hval : P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * g) = c * P.evalAt g := by
      rw [evalAt_mul P hP (algebraMap_mem P c) hgP, evalAt_algebraMap P hP]
    obtain ⟨w, hw⟩ := huU.exists_right_inv
    have hw' : c * (P.evalAt g * (w : (AlgebraicClosure ℚ))) = 1 := by
      have this' : P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * g) * (w : (AlgebraicClosure ℚ)) = 1 :=
        congrArg Subtype.val hw
      rw [hval, mul_assoc] at this'
      exact this'
    rw [inv_eq_of_mul_eq_one_right hw']
    exact mul_mem hgA w.2

  have small : ∀ v : ↥(fieldBar q M'), (∃ h : v ∈ O, (⟨v, h⟩ : ↥O) ∈ maximalIdeal ↥O) → ∃ u : ↥(fieldBar q M'),
      (∃ h : u ∈ O, IsUnit (⟨u, h⟩ : ↥O)) ∧
      ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational → u ∈ P.toValuationSubring →
        (∃ h : P.evalAt u ∈ A, IsUnit (⟨_, h⟩ : ↥A)) → (v ∈ P.toValuationSubring ∧ Small A (P.evalAt v)) := by
    rintro v ⟨hv, hvm⟩
    by_cases hv0 : v = 0
    · refine ⟨1, ⟨one_mem _, isUnit_one⟩, fun P hP _ _ => ?_⟩
      have h0 : P.evalAt (0 : ↥(fieldBar q M')) = 0 := by
        rw [evalAt_eq_iff P hP (zero_mem _), map_zero]; rfl
      rw [hv0]; exact ⟨zero_mem _, h0.symm ▸ Small.zero A⟩
    obtain ⟨c, hc, hres⟩ := C₁.exists_smul_mem v hv0
    have hc' : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * v ∈ O := by rw [← Algebra.smul_def]; exact hc
    have hcu : IsUnit (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * v, hc'⟩ : ↥O) := by
      have e : (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * v, hc'⟩ : ↥O) = ⟨c • v, hc⟩ := Subtype.ext (Algebra.smul_def c v).symm
      rw [e]; exact unit_of_res _ hc hres
    have hcA : c ∉ A := by
      intro hcA
      apply (IsLocalRing.mem_maximalIdeal _).1 _ hcu
      have e : (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * v, hc'⟩ : ↥O) = ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c, (hOA c).2 hcA⟩ * ⟨v, hv⟩ := rfl
      rw [e]; exact Ideal.mul_mem_left _ _ hvm
    have hc0 : c ≠ 0 := by rintro rfl; exact hcA (zero_mem _)
    have hci : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
    have hcim : (⟨c⁻¹, hci⟩ : ↥A) ∈ maximalIdeal ↥A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply hcA
      obtain ⟨w, hw⟩ := hu.exists_right_inv
      have hw' : c⁻¹ * (w : (AlgebraicClosure ℚ)) = 1 := congrArg Subtype.val hw
      have : c = (w : (AlgebraicClosure ℚ)) := by
        rw [← inv_inv c]; exact inv_eq_of_mul_eq_one_right hw'
      rw [this]; exact w.2
    refine ⟨_, ⟨hc', hcu⟩, ?_⟩
    intro P hP huP ⟨huA, huU⟩
    have hvP : v ∈ P.toValuationSubring := by
      have : v = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c⁻¹ * (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * v) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      rw [this]; exact mul_mem (algebraMap_mem P _) huP
    refine ⟨hvP, ?_⟩
    have hval : P.evalAt v = c⁻¹ * P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * v) := by
      rw [evalAt_mul P hP (algebraMap_mem P c) hvP, evalAt_algebraMap P hP, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    rw [hval]
    exact Small.mul_right ⟨hci, hcim⟩ huA

  by_contra hcon
  rw [not_or, not_exists] at hcon
  obtain ⟨hC, hX⟩ := hcon
  have hC' : ∃ gC : ↥(fieldBar q M'), (∀ P ∈ C.dom, gC ∈ P.toValuationSubring ∧ P.evalAt gC ∈ A) ∧ gC ∉ O := by
    by_contra h'
    exact hC fun f hf => by_contra fun hfO => h' ⟨f, hf, hfO⟩
  have hX' : ∀ x : ↥N, ∃ gx : ↥(fieldBar q M'),
      (∀ P ∈ (An x).dom, gx ∈ P.toValuationSubring ∧ P.evalAt gx ∈ A) ∧ gx ∉ O := by
    intro x
    by_contra h'
    exact hX x fun f hf => by_contra fun hfO => h' ⟨f, hf, hfO⟩
  obtain ⟨gC, hgC, hgCO⟩ := hC'
  choose gX hgX hgXO using hX'
  let gfam : Option ↥N → ↥(fieldBar q M') := fun o => o.elim gC gX
  have hgfam : ∀ o, gfam o ∉ O := by rintro (_ | x); exacts [hgCO, hgXO x]

  obtain ⟨k, w, hw, hwprop, htube⟩ :=
    ModularCurve.FullLevel.exists_testFamily_forall_isRational_tube_of_forall_evalAt_mem_maximalIdeal
      q M' hqM' A hA W hW hle R₀ hR₀ s
  have hwsmall : ∀ j, ∃ hj : (IntermediateField.inclusion hle (w j) : ↥(fieldBar q M')) ∈ O,
      (⟨_, hj⟩ : ↥O) ∈ maximalIdeal ↥O := by
    intro j
    obtain ⟨hreg, hres, hval⟩ := hwprop j
    obtain ⟨hmem, hO'⟩ := hOs (w j) (hw j) hreg hres
    obtain ⟨h, hm⟩ := hO' 0 hval
    refine ⟨hmem, ?_⟩
    have e : (⟨_, h⟩ : ↥O) = ⟨_, hmem⟩ := Subtype.ext (by simp)
    exact e ▸ hm

  choose uG huG hPG using fun o => big (gfam o) (hgfam o)
  choose uW huW hPW using fun j => small _ (hwsmall j)
  let u : Option ↥N ⊕ Fin k → ↥(fieldBar q M') := Sum.elim uG uW
  have hu : ∀ i, ∃ h : u i ∈ C₁.integers, IsUnit (⟨u i, h⟩ : ↥C₁.integers) := by
    rintro (o | j); exacts [huG o, huW j]
  obtain ⟨P, hPdom, hPu⟩ :=
    AlgebraicCurve.ComponentChart.exists_mem_dom_forall_isUnit_evalAt_of_forall_isUnit A hfin hfinb hinf C₁ hrat u hu
  have hP : P.IsRational := hrat P hPdom

  have hwP : ∀ j, (IntermediateField.inclusion hle (w j) : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧
      ∃ hj : P.evalAt (IntermediateField.inclusion hle (w j) : ↥(fieldBar q M')) ∈ A, (⟨_, hj⟩ : ↥A) ∈ maximalIdeal ↥A :=
    fun j => hPW j P hP (hPu (Sum.inr j)).1 (hPu (Sum.inr j)).2
  have hPs := htube P hP hwP

  have hbad : ∀ o, ¬ (gfam o ∈ P.toValuationSubring ∧ P.evalAt (gfam o) ∈ A) :=
    fun o => hPG o P hP (hPu (Sum.inl o)).1 (hPu (Sum.inl o)).2
  rcases hcover P hP hPs with ⟨Q, hQN, hPQ⟩ | ⟨x, hPx⟩
  · exact hbad none (hgC P ((hdom P).2 ⟨Q, hQN, hPQ⟩))
  · exact hbad (some x) (hgX x P hPx)

end S_ModularCurve_FullLevel_typeII_exhaustion_of_placeCover_of_componentChart_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_typeII_exhaustion_of_placeCover_of_componentChart_of_eq_two_of_dvd (solution)
