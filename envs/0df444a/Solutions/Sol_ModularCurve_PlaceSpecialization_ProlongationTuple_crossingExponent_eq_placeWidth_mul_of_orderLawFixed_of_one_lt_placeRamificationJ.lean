-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidth_mul_of_orderLawFixed_of_one_lt_placeRamificationJ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8f25de2a-def4-5798-8460-ed766929cf72

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_nodeIntegersOver_of_mem_modularLocalizedAtPoint
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_qExpand_jqNModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valueIntegralityLaw_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueFst_red_evalAt_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueSnd_red_evalAt_of_orderLawFixed
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidth_mul_of_orderLawFixed_of_one_lt_placeRamificationJ
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of"
p2m_attr_erase "simp" "AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

namespace WidthExt
namespace NatTail

open AlgebraicCurve ModularCurve

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]

omit [IsAlgClosed k] in

private theorem jWidth_eq_three_or_two_or_one (a : k) : jWidth a = 3 ∨ jWidth a = 2 ∨ jWidth a = 1 := by
  unfold jWidth
  split_ifs <;> simp

omit [IsAlgClosed k] in

private theorem eq_jWidth_of_dvd_of_one_lt {r : ℕ} {a : k} (hdvd : r ∣ jWidth a) (hr : 1 < r) : r = jWidth a := by
  rcases jWidth_eq_three_or_two_or_one a with h | h | h <;> rw [h] at hdvd ⊢
  · exact ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left (by omega)
  · exact ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left (by omega)
  · exact absurd (Nat.dvd_one.mp hdvd) (by omega)

private theorem placeRamificationJ_eq_jWidth (hqN : ¬ q ∣ N) (hq : 5 ≤ q)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) (hr : 1 < placeRamificationJ N w) :
    placeRamificationJ N w = jWidth (w.evalAt (jGeomGen k N)) :=
  eq_jWidth_of_dvd_of_one_lt (placeRamificationJ_dvd_jWidth_of_mem_ssPlaces hq hqN hw) hr

private theorem placeWidth_eq_one (hqN : ¬ q ∣ N) (hq : 5 ≤ q)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) (hr : 1 < placeRamificationJ N w) :
    placeWidth N w = 1 := by
  unfold placeWidth
  rw [← placeRamificationJ_eq_jWidth hqN hq w hw hr]
  exact Nat.div_self (by omega)

end WidthExt.NatTail

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace WidthRatio

private theorem inv_mem_of_isUnit {F : Type*} [Field F] {S : ValuationSubring F} {y : F} (hy : y ∈ S)
    (hu : IsUnit (⟨y, hy⟩ : S)) : y⁻¹ ∈ S := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hvF : y * (v : F) = 1 := by
    have h := congrArg Subtype.val hv
    simpa using h
  have hv' : (v : F) = y⁻¹ := eq_inv_of_mul_eq_one_right hvF
  exact hv' ▸ v.2

private theorem inv_mem_subring_of_isUnit {F : Type*} [Field F] {S : Subring F} {y : F} (hy : y ∈ S)
    (hu : IsUnit (⟨y, hy⟩ : S)) : y⁻¹ ∈ S := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hvF : y * (v : F) = 1 := by
    have h := congrArg Subtype.val hv
    simpa using h
  have hv' : (v : F) = y⁻¹ := eq_inv_of_mul_eq_one_right hvF
  exact hv' ▸ v.2

private theorem ratio_eq {F : Type*} [Field F] {x y x' y' a u a' u' : F}
    (hxy : x * y = a * u) (hxy' : x' * y' = a' * u') (hy : y ≠ 0) (hy' : y' ≠ 0) (ha' : a' ≠ 0)
    (hu' : u' ≠ 0) : x * x'⁻¹ = a / a' * (u * u'⁻¹ * (y' * y⁻¹)) := by
  have hx : x = a * u / y := (eq_div_iff hy).mpr hxy
  have hx' : x' = a' * u' / y' := (eq_div_iff hy').mpr hxy'
  rw [hx, hx']
  field_simp

private theorem inv_eq {F : Type*} [Field F] {x' y' a' u' : F} (hxy' : x' * y' = a' * u') (ha' : a' ≠ 0)
    (hu' : u' ≠ 0) : x'⁻¹ = y' * (u'⁻¹ * a'⁻¹) := by
  have hy' : y' ≠ 0 := by
    rintro rfl
    exact mul_ne_zero ha' hu' (by rw [← hxy', mul_zero])
  have hx' : x' = a' * u' / y' := (eq_div_iff hy').mpr hxy'
  rw [hx']
  field_simp

section

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem ord_pow_of_ne_zero (v : Place k (modularFunctionFieldC k N)) {g : ↥(modularFunctionFieldC k N)}
    (hg : g ≠ 0) (n : ℕ) : v.ord (g ^ n) = n * v.ord g := by
  induction n with
  | zero => simp [v.ord_one]
  | succ n ih => rw [pow_succ, v.ord_mul (pow_ne_zero n hg) hg, ih]; push_cast; ring

variable (R : ProlongationTuple P) [PerfectField k] {w : Place k (modularFunctionFieldC k N)}

private structure BranchPair (n : ℕ) where
  x : ↥(modularFunctionFieldBar (N * q))
  y : ↥(modularFunctionFieldBar (N * q))
  x_mem : x ∈ R.nodeIntegers w
  y_mem : y ∈ R.nodeIntegers w
  residue₁_y : R.residue₁ ⟨y, R.mem_integersFst_of_mem_nodeIntegers y_mem⟩ ≠ 0
  residue₂_x : R.residue₂ ⟨x, R.mem_integersSnd_of_mem_nodeIntegers x_mem⟩ ≠ 0
  ord_residue₂_x : (arithFrobC q k N • w).ord (R.residue₂ ⟨x, R.mem_integersSnd_of_mem_nodeIntegers x_mem⟩) = n

variable {R} {n : ℕ} (p p' : BranchPair R (w := w) n)

private theorem isUnit_y_fst : IsUnit (⟨p.y, R.mem_integersFst_of_mem_nodeIntegers p.y_mem⟩ : R.R₁.integers) := by
  apply R.R₁.isUnit_of_residue_ne_zero
  intro h
  apply p.residue₁_y
  rw [residue₁_apply]
  exact (congrArg R.ι h).trans (map_zero _)

private theorem isUnit_x_snd : IsUnit (⟨p.x, R.mem_integersSnd_of_mem_nodeIntegers p.x_mem⟩ : R.R₂.integers) := by
  apply R.R₂.isUnit_of_residue_ne_zero
  intro h
  apply p.residue₂_x
  rw [residue₂_apply]
  exact (congrArg R.ι h).trans (map_zero _)

private theorem y_ne_zero : p.y ≠ 0 := fun h => (isUnit_y_fst p).ne_zero (Subtype.ext h)

private theorem x_ne_zero : p.x ≠ 0 := fun h => (isUnit_x_snd p).ne_zero (Subtype.ext h)

private theorem ratio_x_mem (a a' : AlgebraicClosure ℚ) (u u' : ↥(modularFunctionFieldBar (N * q)))
    (hu : u ∈ R.nodeIntegers w) (hu'i : u'⁻¹ ∈ R.nodeIntegers w)
    (hxy : p.x * p.y = algebraMap (AlgebraicClosure ℚ) _ a * u)
    (hxy' : p'.x * p'.y = algebraMap (AlgebraicClosure ℚ) _ a' * u')
    (ht : a / a' ∈ A) : p.x * p'.x⁻¹ ∈ R.nodeIntegers w := by
  have hxy'0 : p'.x * p'.y ≠ 0 := mul_ne_zero (x_ne_zero p') (y_ne_zero p')
  have ha' : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) a' ≠ 0 := by
    intro h; apply hxy'0; rw [hxy', h, zero_mul]
  have hu'0 : u' ≠ 0 := by
    intro h; apply hxy'0; rw [hxy', h, mul_zero]
  have hr := ratio_eq hxy hxy' (y_ne_zero p) (y_ne_zero p') ha' hu'0
  rw [← map_div₀] at hr
  refine ⟨?_, ?_, fun V hV => ?_⟩
  · rw [hr]
    exact mul_mem ((R.R₁.algebraMap_mem_iff _).mpr ht) (mul_mem (mul_mem (R.mem_integersFst_of_mem_nodeIntegers hu)
      (R.mem_integersFst_of_mem_nodeIntegers hu'i)) (mul_mem (R.mem_integersFst_of_mem_nodeIntegers p'.y_mem)
      (inv_mem_of_isUnit _ (isUnit_y_fst p))))
  · exact mul_mem (R.mem_integersSnd_of_mem_nodeIntegers p.x_mem) (inv_mem_of_isUnit _ (isUnit_x_snd p'))
  · rw [inv_eq hxy' ha' hu'0]
    refine mul_mem (R.mem_toValuationSubring_of_mem_nodeIntegers p.x_mem hV)
      (mul_mem (R.mem_toValuationSubring_of_mem_nodeIntegers p'.y_mem hV)
        (mul_mem (R.mem_toValuationSubring_of_mem_nodeIntegers hu'i hV) ?_))
    rw [← map_inv₀]
    exact V.algebraMap_mem' _

private theorem residue₁_ratio_eq_zero (a a' : AlgebraicClosure ℚ) (u u' : ↥(modularFunctionFieldBar (N * q)))
    (hu : u ∈ R.nodeIntegers w) (hu'i : u'⁻¹ ∈ R.nodeIntegers w)
    (hxy : p.x * p.y = algebraMap (AlgebraicClosure ℚ) _ a * u)
    (hxy' : p'.x * p'.y = algebraMap (AlgebraicClosure ℚ) _ a' * u')
    (ht : a / a' ∈ A) (ht𝔪 : (⟨a / a', ht⟩ : A) ∈ IsLocalRing.maximalIdeal A)
    (h₁ : p.x * p'.x⁻¹ ∈ R.R₁.integers) : R.residue₁ ⟨_, h₁⟩ = 0 := by
  have hxy'0 : p'.x * p'.y ≠ 0 := mul_ne_zero (x_ne_zero p') (y_ne_zero p')
  have ha' : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) a' ≠ 0 := by
    intro h; apply hxy'0; rw [hxy', h, zero_mul]
  have hu'0 : u' ≠ 0 := by
    intro h; apply hxy'0; rw [hxy', h, mul_zero]
  have hr := ratio_eq hxy hxy' (y_ne_zero p) (y_ne_zero p') ha' hu'0
  rw [← map_div₀] at hr
  have hg : u * u'⁻¹ * (p'.y * p.y⁻¹) ∈ R.R₁.integers :=
    mul_mem (mul_mem (R.mem_integersFst_of_mem_nodeIntegers hu) (R.mem_integersFst_of_mem_nodeIntegers hu'i))
      (mul_mem (R.mem_integersFst_of_mem_nodeIntegers p'.y_mem) (inv_mem_of_isUnit _ (isUnit_y_fst p)))
  have hsplit : (⟨_, h₁⟩ : R.R₁.integers)
      = ⟨algebraMap (AlgebraicClosure ℚ) _ (((⟨a / a', ht⟩ : A) : AlgebraicClosure ℚ)),
          (R.R₁.algebraMap_mem_iff _).mpr (⟨a / a', ht⟩ : A).2⟩ * ⟨_, hg⟩ :=
    Subtype.ext (by rw [MulMemClass.coe_mul]; exact hr)
  have hz : R.residue₁ ⟨algebraMap (AlgebraicClosure ℚ) _ (((⟨a / a', ht⟩ : A) : AlgebraicClosure ℚ)),
      (R.R₁.algebraMap_mem_iff _).mpr (⟨a / a', ht⟩ : A).2⟩ = 0 := by
    rw [residue₁_apply, R.R₁.residue_algebraMap ⟨a / a', ht⟩, (IsLocalRing.residue_eq_zero_iff _).mpr ht𝔪, map_zero,
      map_zero]
  rw [hsplit, RingHom.map_mul, hz, zero_mul]

private theorem ord_residue₂_ratio_eq_zero (h₂ : p.x * p'.x⁻¹ ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h₂⟩ ≠ 0 ∧ (arithFrobC q k N • w).ord (R.residue₂ ⟨_, h₂⟩) = 0 := by
  have hx2 := R.mem_integersSnd_of_mem_nodeIntegers p.x_mem
  have hx'2 := R.mem_integersSnd_of_mem_nodeIntegers p'.x_mem
  have hmul : R.residue₂ ⟨_, h₂⟩ * R.residue₂ ⟨_, hx'2⟩ = R.residue₂ ⟨_, hx2⟩ := by
    rw [← RingHom.map_mul]
    exact congrArg _ (Subtype.ext (by rw [MulMemClass.coe_mul]; exact inv_mul_cancel_right₀ (x_ne_zero p') _))
  have hX := p.residue₂_x
  have hX' := p'.residue₂_x
  have hQ : R.residue₂ ⟨_, h₂⟩ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact hX hmul.symm
  refine ⟨hQ, ?_⟩
  have hord := congrArg (arithFrobC q k N • w).ord hmul
  rw [(arithFrobC q k N • w).ord_mul hQ hX', p.ord_residue₂_x, p'.ord_residue₂_x] at hord
  omega

private theorem false_of_div_mem_maximalIdeal (W : Finset (Place k (modularFunctionFieldC k N)))
    (hreg : R.RegularityLaw W) (hw : w ∈ W)
    (a a' : AlgebraicClosure ℚ) (u u' : ↥(modularFunctionFieldBar (N * q)))
    (hu : u ∈ R.nodeIntegers w) (hu'i : u'⁻¹ ∈ R.nodeIntegers w)
    (hxy : p.x * p.y = algebraMap (AlgebraicClosure ℚ) _ a * u)
    (hxy' : p'.x * p'.y = algebraMap (AlgebraicClosure ℚ) _ a' * u')
    (ht : a / a' ∈ A) (ht𝔪 : (⟨a / a', ht⟩ : A) ∈ IsLocalRing.maximalIdeal A) : False := by
  have hmem := ratio_x_mem p p' a a' u u' hu hu'i hxy hxy' ht
  have h₁ := R.mem_integersFst_of_mem_nodeIntegers hmem
  have h₂ := R.mem_integersSnd_of_mem_nodeIntegers hmem
  have hres1 := residue₁_ratio_eq_zero p p' a a' u u' hu hu'i hxy hxy' ht ht𝔪 h₁
  obtain ⟨hρ0, hord⟩ := ord_residue₂_ratio_eq_zero p p' h₂
  have hs : smulNodePair (arithFrobC q k N) w ∈ nodePairsOfPlaces (arithFrobC q k N) W :=
    (mem_nodePairsOfPlaces_iff _ _ _).mpr ⟨w, hw, rfl⟩
  obtain ⟨cv, hv1, hv2⟩ := hreg.2 _ h₁ h₂ _ hs
    (fun V hV => V.ord_nonneg_of_mem (R.mem_toValuationSubring_of_mem_nodeIntegers hmem hV))
  have h00 : (smulNodePair (arithFrobC q k N) w).1.HasValue (0 : ↥(modularFunctionFieldC k N)) (0 : k) := by
    have h := Place.hasValue_algebraMap (smulNodePair (arithFrobC q k N) w).1 (0 : k)
    rwa [map_zero] at h
  rw [hres1] at hv1
  have hcv : cv = 0 := hv1.unique h00
  obtain ⟨hm', hunit⟩ := (arithFrobC q k N • w).exists_isUnit_of_ord_eq_zero hρ0 hord
  obtain ⟨hm, hres⟩ := hv2
  rw [hcv, map_zero] at hres
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hunit hres

private theorem valuation_eq (W : Finset (Place k (modularFunctionFieldC k N)))
    (hreg : R.RegularityLaw W) (hw : w ∈ W)
    (a a' : AlgebraicClosure ℚ) (u u' : ↥(modularFunctionFieldBar (N * q)))
    (hu : u ∈ R.nodeIntegers w) (hui : u⁻¹ ∈ R.nodeIntegers w)
    (hu' : u' ∈ R.nodeIntegers w) (hu'i : u'⁻¹ ∈ R.nodeIntegers w)
    (hxy : p.x * p.y = algebraMap (AlgebraicClosure ℚ) _ a * u)
    (hxy' : p'.x * p'.y = algebraMap (AlgebraicClosure ℚ) _ a' * u') :
    A.valuation a = A.valuation a' := by
  have hxy0 : p.x * p.y ≠ 0 := mul_ne_zero (x_ne_zero p) (y_ne_zero p)
  have hxy'0 : p'.x * p'.y ≠ 0 := mul_ne_zero (x_ne_zero p') (y_ne_zero p')
  have ha : a ≠ 0 := by
    intro h; apply hxy0; rw [hxy, h, map_zero, zero_mul]
  have ha' : a' ≠ 0 := by
    intro h; apply hxy'0; rw [hxy', h, map_zero, zero_mul]
  have hva' : A.valuation a' ≠ 0 := (map_ne_zero _).mpr ha'
  rcases lt_trichotomy (A.valuation (a / a')) 1 with hlt | heq | hgt
  · exfalso
    have ht : a / a' ∈ A := A.mem_of_valuation_le_one _ hlt.le
    exact false_of_div_mem_maximalIdeal p p' W hreg hw a a' u u' hu hu'i hxy hxy' ht
      ((A.valuation_lt_one_iff ⟨a / a', ht⟩).mpr hlt)
  · rwa [map_div₀, div_eq_one_iff_eq hva'] at heq
  · exfalso
    have hlt : A.valuation (a' / a) < 1 := by
      rw [show a' / a = (a / a')⁻¹ by rw [inv_div], map_inv₀]
      exact inv_lt_one_of_one_lt₀ hgt
    have ht : a' / a ∈ A := A.mem_of_valuation_le_one _ hlt.le
    exact false_of_div_mem_maximalIdeal p' p W hreg hw a' a u' u hu' hui hxy' hxy ht
      ((A.valuation_lt_one_iff ⟨a' / a, ht⟩).mpr hlt)

variable {K : IntermediateField ℚ (AlgebraicClosure ℚ)}

omit [PerfectField k] in

private theorem inv_mem_nodeIntegers_of_isUnit {u : ↥(R.nodeIntegersOver K w)} (hu : IsUnit u) :
    (u : ↥(modularFunctionFieldBar (N * q)))⁻¹ ∈ R.nodeIntegers w :=
  R.nodeIntegersOver_le K w (inv_mem_subring_of_isUnit u.2 (by simpa using hu))

private theorem residue₂_x_ne_zero (c : R.NodeCoordinates K w) :
    R.residue₂ ⟨c.x, R.mem_integersSnd_of_mem_nodeIntegers c.x.2.1⟩ ≠ 0 := by
  intro h
  apply c.nodeResidue₂_x_ne_zero
  rw [nodeResidue₂_apply]
  exact h

private theorem _root_.WidthRatio.ord_residue₂_x (c : R.NodeCoordinates K w) :
    (arithFrobC q k N • w).ord (R.residue₂ ⟨c.x, R.mem_integersSnd_of_mem_nodeIntegers c.x.2.1⟩) = 1 := by
  have h := c.x_snd
  rw [nodeResidue₂_apply] at h
  exact h

p2m_export "WidthRatio" "ord_residue₂_x"

private theorem residue₁_y_ne_zero (c : R.NodeCoordinates K w) :
    R.residue₁ ⟨c.y, R.mem_integersFst_of_mem_nodeIntegers c.y.2.1⟩ ≠ 0 := by
  intro h
  apply c.nodeResidue₁_y_ne_zero
  rw [nodeResidue₁_apply]
  exact h

private noncomputable def powPair (c : R.NodeCoordinates K w) (r : ℕ) : BranchPair R (w := w) r where
  x := (c.x : ↥(modularFunctionFieldBar (N * q))) ^ r
  y := (c.y : ↥(modularFunctionFieldBar (N * q))) ^ r
  x_mem := pow_mem c.x.2.1 r
  y_mem := pow_mem c.y.2.1 r
  residue₁_y := by
    have h1 : (⟨(c.y : ↥(modularFunctionFieldBar (N * q))) ^ r,
        R.mem_integersFst_of_mem_nodeIntegers (pow_mem c.y.2.1 r)⟩ : R.R₁.integers)
        = ⟨c.y, R.mem_integersFst_of_mem_nodeIntegers c.y.2.1⟩ ^ r :=
      Subtype.ext (by simp)
    rw [h1, map_pow]
    exact pow_ne_zero r (residue₁_y_ne_zero c)
  residue₂_x := by
    have h1 : (⟨(c.x : ↥(modularFunctionFieldBar (N * q))) ^ r,
        R.mem_integersSnd_of_mem_nodeIntegers (pow_mem c.x.2.1 r)⟩ : R.R₂.integers)
        = ⟨c.x, R.mem_integersSnd_of_mem_nodeIntegers c.x.2.1⟩ ^ r :=
      Subtype.ext (by simp)
    rw [h1, map_pow]
    exact pow_ne_zero r (residue₂_x_ne_zero c)
  ord_residue₂_x := by
    have h1 : (⟨(c.x : ↥(modularFunctionFieldBar (N * q))) ^ r,
        R.mem_integersSnd_of_mem_nodeIntegers (pow_mem c.x.2.1 r)⟩ : R.R₂.integers)
        = ⟨c.x, R.mem_integersSnd_of_mem_nodeIntegers c.x.2.1⟩ ^ r :=
      Subtype.ext (by simp)
    rw [h1, map_pow, ord_pow_of_ne_zero _ (residue₂_x_ne_zero c), ord_residue₂_x c, mul_one]

omit [PerfectField k] in

private theorem coe_eq_of_eq (x y u : ↥(R.nodeIntegersOver K w)) (z : ↥(NodeLocalized.coeffSubring A K)) (m : ℕ)
    (h : x * y = R.nodeConst K w z ^ m * u) :
    (x : ↥(modularFunctionFieldBar (N * q))) * y
      = algebraMap (AlgebraicClosure ℚ) _ ((z : AlgebraicClosure ℚ) ^ m) * u := by
  have h' := congrArg Subtype.val h
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, coe_nodeConst] at h'
  rw [map_pow]
  exact h'

private theorem valuation_pow_mul_eq_of_pair (W : Finset (Place k (modularFunctionFieldC k N)))
    (hreg : R.RegularityLaw W) (hw : w ∈ W)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (c : R.NodeCoordinates K w) (E : ℕ)
    (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (r : ℕ) (G H Wu : ↥(R.nodeIntegersOver K w)) (hWu : IsUnit Wu)
    (hG : R.nodeResidue₂ w ⟨G, G.2.1⟩ ≠ 0)
    (hGord : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨G, G.2.1⟩) = (r : ℤ))
    (hH : R.nodeResidue₁ w ⟨H, H.2.1⟩ ≠ 0)
    (z : ↥(NodeLocalized.coeffSubring A K)) (m : ℕ) (hGH : G * H = R.nodeConst K w z ^ m * Wu) :
    A.valuation (ϖ : AlgebraicClosure ℚ) ^ (r * E) = A.valuation (z : AlgebraicClosure ℚ) ^ m := by
  have hxyF := coe_eq_of_eq c.x c.y u ϖ E hxy
  have hGHF := coe_eq_of_eq G H Wu z m hGH
  have hH' : R.residue₁ ⟨H, R.mem_integersFst_of_mem_nodeIntegers H.2.1⟩ ≠ 0 := by
    rw [nodeResidue₁_apply] at hH; exact hH
  have hG' : R.residue₂ ⟨G, R.mem_integersSnd_of_mem_nodeIntegers G.2.1⟩ ≠ 0 := by
    rw [nodeResidue₂_apply] at hG; exact hG
  have hGord' : (arithFrobC q k N • w).ord (R.residue₂ ⟨G, R.mem_integersSnd_of_mem_nodeIntegers G.2.1⟩) = r := by
    rw [nodeResidue₂_apply] at hGord; exact hGord
  let pG : BranchPair R (w := w) r := ⟨G, H, G.2.1, H.2.1, hH', hG', hGord'⟩
  have hpow : (powPair c r).x * (powPair c r).y
      = algebraMap (AlgebraicClosure ℚ) _ (((ϖ : AlgebraicClosure ℚ) ^ E) ^ r)
          * (u : ↥(modularFunctionFieldBar (N * q))) ^ r := by
    show (c.x : ↥(modularFunctionFieldBar (N * q))) ^ r * (c.y : ↥(modularFunctionFieldBar (N * q))) ^ r = _
    rw [← mul_pow, hxyF, mul_pow, ← map_pow]
  have h := valuation_eq (powPair c r) pG W hreg hw _ _ _ _ (pow_mem (R.nodeIntegersOver_le K w u.2) r)
    (by rw [← inv_pow]; exact pow_mem (inv_mem_nodeIntegers_of_isUnit hu) r) (R.nodeIntegersOver_le K w Wu.2)
    (inv_mem_nodeIntegers_of_isUnit hWu) hpow hGHF
  rw [map_pow, map_pow, map_pow, ← pow_mul, mul_comm E r] at h
  exact h

end

end WidthRatio

namespace RamifiedWidth
namespace P1N

section TV
open Polynomial

variable {T : Type*} [CommRing T]

end TV

section OC
open Finset

variable {B : Type*} [CommRing B]

end OC

section L
open ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple Polynomial

private theorem jqNModC_congr (L : Type*) [CommRing L] {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    jqNModC L n = jqNModC L m := by
  subst h
  rfl

private theorem modularEval_X0 (M : ℕ) [NeZero M] {L : Type*} [CommRing L] (S : Subring L) :
    NodeLocalized.modularEval M S (MvPolynomial.X 0) = jqModC L := by
  simp [NodeLocalized.modularEval]

private theorem modularEval_X1 (M : ℕ) [NeZero M] {L : Type*} [CommRing L] (S : Subring L) :
    NodeLocalized.modularEval M S (MvPolynomial.X 1) = jqNModC L M := by
  simp [NodeLocalized.modularEval, Matrix.cons_val_one]

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]

private theorem coe_jFun : ((jFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
    = jqModC (AlgebraicClosure ℚ) := by
  show coeffEmb (AlgebraicClosure ℚ) jq = _
  exact coeffEmb_jq _

private theorem coe_jQFun : ((jQFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
    = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
  rw [jqNModC_congr (AlgebraicClosure ℚ) (one_mul q)]
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = _
  rw [coeffEmb_qExpand, coeffEmb_jq]
  rfl

end L

section Co
open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

end Co

end RamifiedWidth.P1N

namespace RamifiedWidth
namespace S6

open AlgebraicCurve IsLocalRing ModularCurve Polynomial
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open RamifiedWidth.P1N

section G
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem HasValue.add (v : Place K F) {g g' : F} {a a' : K} (h : v.HasValue g a)
    (h' : v.HasValue g' a') : v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

private theorem HasValue.neg (v : Place K F) {g : F} {a : K} (h : v.HasValue g a) :
    v.HasValue (-g) (-a) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have hx : (⟨-g, neg_mem hg⟩ : v.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [hx, map_neg, hr, map_neg]

private theorem HasValue.sub (v : Place K F) {g g' : F} {a a' : K} (h : v.HasValue g a)
    (h' : v.HasValue g' a') : v.HasValue (g - g') (a - a') := by
  simpa only [sub_eq_add_neg] using HasValue.add v h (HasValue.neg v h')

namespace HasValue
private theorem _root_.RamifiedWidth.S6.HasValue.pow (v : Place K F) {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) :
    v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using v.hasValue_one
  | succ n ih => simpa only [pow_succ] using ih.mul h

end HasValue
p2m_export "RamifiedWidth.S6" "HasValue.pow"

private theorem hasValue_evalAt (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasValue f (v.evalAt f) :=
  ⟨hf, (v.algebraMap_evalAt hv hf).symm⟩

end G

section AL

private theorem qExpand_congr (S : Type*) [CommRing S] {n m : ℕ} [NeZero n] [NeZero m] (h : n = m)
    (x : LaurentSeries S) :
    qExpand S n x = qExpand S m x := by
  subst h
  rfl

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]

private theorem isAtkinLehnerAutFull_of_not_dvd (hqN : ¬ q ∣ N) :
    IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
  isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
    (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)

private theorem jFun_eq_mk :
    jFun N q = ⟨coeffEmb (AlgebraicClosure ℚ)
        ((⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right (one_dvd N) q)⟩ :
          ↥(modularFunctionFieldFull (N * q))) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right (one_dvd N) q)⟩ :
          ↥(modularFunctionFieldFull (N * q))).2⟩ := by
  apply Subtype.ext
  show coeffEmb (AlgebraicClosure ℚ) jq = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq)
  rw [qExpand_one_apply]

private theorem jQFun_eq_mk :
    jQFun N q = ⟨coeffEmb (AlgebraicClosure ℚ)
        ((⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩ :
          ↥(modularFunctionFieldFull (N * q))) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩ :
          ↥(modularFunctionFieldFull (N * q))).2⟩ := by
  apply Subtype.ext
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
  rw [qExpand_congr ℚ (one_mul q)]

private theorem atkinLehnerBar_jFun (hqN : ¬ q ∣ N) : atkinLehnerBar N q (jFun N q) = jQFun N q := by
  obtain ⟨h1, -⟩ := isAtkinLehnerAutFull_of_not_dvd (q := q) (N := N) hqN 1 inferInstance (one_dvd N)
  have e := geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)
    ⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right (one_dvd N) q)⟩
  rw [h1] at e
  rw [show atkinLehnerBar N q (jFun N q)
      = geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q) (jFun N q)
      from rfl,
    jFun_eq_mk, e, jQFun_eq_mk]

private theorem atkinLehnerBar_jQFun (hqN : ¬ q ∣ N) : atkinLehnerBar N q (jQFun N q) = jFun N q := by
  obtain ⟨-, h2⟩ := isAtkinLehnerAutFull_of_not_dvd (q := q) (N := N) hqN 1 inferInstance (one_dvd N)
  have e := geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)
    ⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩
  rw [h2] at e
  rw [show atkinLehnerBar N q (jQFun N q)
      = geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q) (jQFun N q)
      from rfl,
    jQFun_eq_mk, e, jFun_eq_mk]

end AL

section RS
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

private theorem residue₁_of_coeffMap (y : LaurentSeries A) (f : ↥(modularFunctionFieldBar (N * q)))
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y) :
    ∃ h : f ∈ R.R₁.integers,
      ((R.residue₁ ⟨f, h⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k) = coeffMap red y := by
  obtain ⟨f, hfF⟩ := f
  simp only at hf
  subst hf
  obtain ⟨hmem, hres⟩ := R.residue₁_coeffMap y hfF
  refine ⟨hmem, ?_⟩
  rw [ProlongationTuple.residue₁_apply, R.ι_coe, hres, coeffMap_coeffMap,
    show R.redBar.comp (IsLocalRing.residue A) = red from RingHom.ext R.redBar_residue]

private theorem jFun_mem₁_and_residue₁ :
    ∃ h : jFun N q ∈ R.R₁.integers, R.residue₁ ⟨jFun N q, h⟩ = jGeomGen k N := by
  obtain ⟨h, hres⟩ := residue₁_of_coeffMap R (jqModC A) (jFun N q)
    (by rw [coe_jFun]; exact (coeffSemilinearAut.coeffMap_jqModC _).symm)
  exact ⟨h, Subtype.ext (by rw [hres]; exact coeffSemilinearAut.coeffMap_jqModC _)⟩

private theorem jQFun_mem₁_and_residue₁ :
    ∃ h : jQFun N q ∈ R.R₁.integers, R.residue₁ ⟨jQFun N q, h⟩ = jGeomGen k N ^ q := by
  obtain ⟨h, hres⟩ := residue₁_of_coeffMap R (qExpand A q (jqModC A)) (jQFun N q)
    (by
      show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = _
      rw [coeffEmb_qExpand, coeffEmb_jq, coeffSemilinearAut.coeffMap_qExpand, coeffSemilinearAut.coeffMap_jqModC])
  refine ⟨h, Subtype.ext ?_⟩
  rw [hres, coeffSemilinearAut.coeffMap_qExpand, coeffSemilinearAut.coeffMap_jqModC]
  show qExpand k q (jqModC k) = ((jGeomGen k N : ↥(modularFunctionFieldC k N)) : LaurentSeries k) ^ q
  have hpow := qExpand_jqNModC_eq_pow_unconditional k 1 (ℓ := q)
  rw [jqNModC_one] at hpow
  exact hpow

private theorem residue₁_jFun (h : jFun N q ∈ R.R₁.integers) : R.residue₁ ⟨jFun N q, h⟩ = jGeomGen k N := by
  obtain ⟨h', e⟩ := jFun_mem₁_and_residue₁ (q := q) (N := N) R
  exact e

private theorem residue₁_jQFun (h : jQFun N q ∈ R.R₁.integers) : R.residue₁ ⟨jQFun N q, h⟩ = jGeomGen k N ^ q := by
  obtain ⟨h', e⟩ := jQFun_mem₁_and_residue₁ (q := q) (N := N) R
  exact e

private theorem jFun_mem₂ (hqN : ¬ q ∣ N) : jFun N q ∈ R.R₂.integers :=
  (R.mem_integers₂_iff _).mpr (by rw [atkinLehnerBar_jFun hqN]; exact (jQFun_mem₁_and_residue₁ R).1)

private theorem jQFun_mem₂ (hqN : ¬ q ∣ N) : jQFun N q ∈ R.R₂.integers :=
  (R.mem_integers₂_iff _).mpr (by rw [atkinLehnerBar_jQFun hqN]; exact (jFun_mem₁_and_residue₁ R).1)

private theorem residue₂_jFun (hqN : ¬ q ∣ N) (h₂ : jFun N q ∈ R.R₂.integers) :
    R.residue₂ ⟨jFun N q, h₂⟩ = jGeomGen k N ^ q := by
  rw [ProlongationTuple.residue₂_apply, R.residue₂_eq]
  have key : ∀ (g : ↥(modularFunctionFieldBar (N * q))) (hg : g ∈ R.R₁.integers), g = jQFun N q →
      R.ι (R.R₁.residue ⟨g, hg⟩) = jGeomGen k N ^ q := by
    rintro g hg rfl
    exact residue₁_jQFun R hg
  exact key _ _ (atkinLehnerBar_jFun hqN)

private theorem residue₂_jQFun (hqN : ¬ q ∣ N) (h₂ : jQFun N q ∈ R.R₂.integers) :
    R.residue₂ ⟨jQFun N q, h₂⟩ = jGeomGen k N := by
  rw [ProlongationTuple.residue₂_apply, R.residue₂_eq]
  have key : ∀ (g : ↥(modularFunctionFieldBar (N * q))) (hg : g ∈ R.R₁.integers), g = jFun N q →
      R.ι (R.R₁.residue ⟨g, hg⟩) = jGeomGen k N := by
    rintro g hg rfl
    exact residue₁_jFun R hg
  exact key _ _ (atkinLehnerBar_jQFun hqN)

private theorem residue₁_G (h : jQFun N q - jFun N q ^ q ∈ R.R₁.integers) :
    R.residue₁ ⟨jQFun N q - jFun N q ^ q, h⟩ = 0 := by
  obtain ⟨hJ, eJ⟩ := jFun_mem₁_and_residue₁ (q := q) (N := N) R
  obtain ⟨hJq, eJq⟩ := jQFun_mem₁_and_residue₁ (q := q) (N := N) R
  rw [show (⟨jQFun N q - jFun N q ^ q, h⟩ : ↥R.R₁.integers) = ⟨jQFun N q, hJq⟩ - ⟨jFun N q, hJ⟩ ^ q from rfl,
    map_sub, map_pow, eJ, eJq, sub_self]

private theorem residue₁_H (h : jFun N q - jQFun N q ^ q ∈ R.R₁.integers) :
    R.residue₁ ⟨jFun N q - jQFun N q ^ q, h⟩ = jGeomGen k N - (jGeomGen k N ^ q) ^ q := by
  obtain ⟨hJ, eJ⟩ := jFun_mem₁_and_residue₁ (q := q) (N := N) R
  obtain ⟨hJq, eJq⟩ := jQFun_mem₁_and_residue₁ (q := q) (N := N) R
  rw [show (⟨jFun N q - jQFun N q ^ q, h⟩ : ↥R.R₁.integers) = ⟨jFun N q, hJ⟩ - ⟨jQFun N q, hJq⟩ ^ q from rfl,
    map_sub, map_pow, eJ, eJq]

private theorem residue₂_G (hqN : ¬ q ∣ N) (h : jQFun N q - jFun N q ^ q ∈ R.R₂.integers) :
    R.residue₂ ⟨jQFun N q - jFun N q ^ q, h⟩ = jGeomGen k N - (jGeomGen k N ^ q) ^ q := by
  rw [show (⟨jQFun N q - jFun N q ^ q, h⟩ : ↥R.R₂.integers)
        = ⟨jQFun N q, jQFun_mem₂ R hqN⟩ - ⟨jFun N q, jFun_mem₂ R hqN⟩ ^ q from rfl,
    map_sub, map_pow, residue₂_jFun R hqN, residue₂_jQFun R hqN]

private theorem residue₂_H (hqN : ¬ q ∣ N) (h : jFun N q - jQFun N q ^ q ∈ R.R₂.integers) :
    R.residue₂ ⟨jFun N q - jQFun N q ^ q, h⟩ = 0 := by
  rw [show (⟨jFun N q - jQFun N q ^ q, h⟩ : ↥R.R₂.integers)
        = ⟨jFun N q, jFun_mem₂ R hqN⟩ - ⟨jQFun N q, jQFun_mem₂ R hqN⟩ ^ q from rfl,
    map_sub, map_pow, residue₂_jFun R hqN, residue₂_jQFun R hqN, sub_self]

end RS

section Ord
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q]

private theorem jGeomGen_sub_pow_sq_eq (c : k) (hc : c ^ (q ^ 2) = c) :
    jGeomGen k N - (jGeomGen k N ^ q) ^ q
      = (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c)
          * (1 - (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c) ^ (q ^ 2 - 1)) := by
  haveI : CharP ↥(modularFunctionFieldC k N) q :=
    charP_of_injective_algebraMap (algebraMap k ↥(modularFunctionFieldC k N)).injective q
  have hfrob : (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c) ^ (q ^ 2)
      = jGeomGen k N ^ (q ^ 2) - algebraMap k ↥(modularFunctionFieldC k N) c := by
    rw [sub_pow_char_pow, ← map_pow, hc]
  calc jGeomGen k N - (jGeomGen k N ^ q) ^ q
      = (jGeomGen k N - algebraMap k _ c) - (jGeomGen k N ^ (q ^ 2) - algebraMap k _ c) := by
        rw [← pow_mul, ← sq]; ring
    _ = (jGeomGen k N - algebraMap k _ c) - (jGeomGen k N - algebraMap k _ c) ^ (q ^ 2) := by rw [hfrob]
    _ = _ := by
      have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (Fact.out : q.Prime).pos
      conv_lhs => rw [show q ^ 2 = (q ^ 2 - 1) + 1 from (Nat.sub_add_cancel hq2).symm, pow_succ]
      ring

variable [IsAlgClosed k] [DecidableEq k]

omit [DecidableEq k] in

private theorem arithFrobC_smul_jGeomGen_sub_pow_sq :
    arithFrobC q k N • (jGeomGen k N - (jGeomGen k N ^ q) ^ q) = jGeomGen k N - (jGeomGen k N ^ q) ^ q := by
  have hj : arithFrobC q k N • jGeomGen k N = jGeomGen k N := arithFrobC_smul_jq q k N
  show SemilinearAut.toRingAut (arithFrobC q k N) (jGeomGen k N - (jGeomGen k N ^ q) ^ q) = _
  rw [map_sub, map_pow, map_pow, show SemilinearAut.toRingAut (arithFrobC q k N) (jGeomGen k N) = jGeomGen k N from hj]

end Ord

end RamifiedWidth.S6

namespace RamifiedWidth
namespace ExpN

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem ext_LQ (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (g g' : ↥(R.nodeIntegersOver K w))
    (h : (((g : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) : LQ)
      = (((g' : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) : LQ)) : g = g' :=
  Subtype.ext (Subtype.ext h)

section Transport

variable (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
  (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
  (a : k) (ha : w.evalAt (jGeomGen k N) = a)

omit [Fact (Nat.Prime q)] [CharP k q] [IsAlgClosed k] in
include hw in
private theorem hW_single : ∀ v ∈ ({w} : Finset (Place k (modularFunctionFieldC k N))), v ∈ ssPlaces q N k :=
  fun v hv => by rw [Finset.mem_singleton] at hv; rw [hv]; exact hw

private noncomputable def tauFun
    (f : ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
        (NodeLocalized.redRestrict red K) a (a ^ q))) : ↥(R.nodeIntegersOver K w) :=
  ⟨(R.exists_mem_nodeIntegersOver_of_mem_modularLocalizedAtPoint {w} (hW_single w hw) K w
      (Finset.mem_singleton_self w) a ha (f : LQ) f.2).choose,
    (R.exists_mem_nodeIntegersOver_of_mem_modularLocalizedAtPoint {w} (hW_single w hw) K w
      (Finset.mem_singleton_self w) a ha (f : LQ) f.2).choose_spec.1⟩

private theorem coe_tauFun
    (f : ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
        (NodeLocalized.redRestrict red K) a (a ^ q))) :
    (((tauFun R K w hw a ha f : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) : LQ) = (f : LQ) :=
  (R.exists_mem_nodeIntegersOver_of_mem_modularLocalizedAtPoint {w} (hW_single w hw) K w
      (Finset.mem_singleton_self w) a ha (f : LQ) f.2).choose_spec.2

private noncomputable def tau :
    ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
        (NodeLocalized.redRestrict red K) a (a ^ q)) →+* ↥(R.nodeIntegersOver K w) where
  toFun := tauFun R K w hw a ha
  map_one' := by
    apply ext_LQ
    rw [coe_tauFun]
    simp
  map_mul' f g := by
    apply ext_LQ
    rw [coe_tauFun]
    push_cast
    rw [coe_tauFun, coe_tauFun]
  map_zero' := by
    apply ext_LQ
    rw [coe_tauFun]
    simp
  map_add' f g := by
    apply ext_LQ
    rw [coe_tauFun]
    push_cast
    rw [coe_tauFun, coe_tauFun]

private theorem coe_tau (f : ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
        (NodeLocalized.redRestrict red K) a (a ^ q))) :
    (((tau R K w hw a ha f : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) : LQ) = (f : LQ) :=
  coe_tauFun R K w hw a ha f

private theorem tau_const (ϖ : ↥(NodeLocalized.coeffSubring A K)) :
    tau R K w hw a ha ⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ),
      NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
        (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ = R.nodeConst K w ϖ := by
  apply ext_LQ
  rw [coe_tau, coe_nodeConst]
  simp [NodeLocalized.modularEval, CharPReduction.constSeries]

private theorem coe_tau_G :
    ((tau R K w hw a ha ⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K)
        (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
      NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
        (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ : ↥(R.nodeIntegersOver K w)) :
      ↥(modularFunctionFieldBar (N * q))) = jQFun N q - jFun N q ^ q := by
  apply Subtype.val_injective
  show (((tau R K w hw a ha _ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) : LQ) = _
  rw [coe_tau]
  push_cast
  rw [RamifiedWidth.P1N.coe_jQFun, RamifiedWidth.P1N.coe_jFun, map_sub, map_pow, RamifiedWidth.P1N.modularEval_X1,
    RamifiedWidth.P1N.modularEval_X0]

private theorem coe_tau_H :
    ((tau R K w hw a ha ⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K)
        (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
      NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
        (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ : ↥(R.nodeIntegersOver K w)) :
      ↥(modularFunctionFieldBar (N * q))) = jFun N q - jQFun N q ^ q := by
  apply Subtype.val_injective
  show (((tau R K w hw a ha _ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) : LQ) = _
  rw [coe_tau]
  push_cast
  rw [RamifiedWidth.P1N.coe_jQFun, RamifiedWidth.P1N.coe_jFun, map_sub, map_pow, RamifiedWidth.P1N.modularEval_X1,
    RamifiedWidth.P1N.modularEval_X0]

end Transport

private theorem jGeomGen_sub_pow_sq_ne_zero [IsAlgClosed k] [DecidableEq k]
    {v : Place k ↥(modularFunctionFieldC k N)} (hv : v ∈ ssPlaces q N k) :
    (jGeomGen k N - (jGeomGen k N ^ q) ^ q : ↥(modularFunctionFieldC k N)) ≠ 0 ∧
      v.HasValue (jGeomGen k N - (jGeomGen k N ^ q) ^ q) 0 := by
  have hss : IsSupersingularPlace q N k v := hv
  obtain ⟨b, hb⟩ : ∃ b : k, v.evalAt (jGeomGen k N) = b := ⟨_, rfl⟩
  have hb2 : b ^ (q ^ 2) = b := by
    have h := pow_q_sq_eq_self_of_mem_ssJSet q ((isSupersingularPlace_iff q N k v).mp hss).2.2
    rwa [hb] at h
  have hJ : v.HasValue (jGeomGen k N) b := hb ▸ RamifiedWidth.S6.hasValue_evalAt v hss.1 hss.2.1.1
  have hval : v.HasValue (jGeomGen k N - (jGeomGen k N ^ q) ^ q) (b - (b ^ q) ^ q) :=
    RamifiedWidth.S6.HasValue.sub _ hJ (RamifiedWidth.S6.HasValue.pow _ (RamifiedWidth.S6.HasValue.pow _ hJ q) q)
  have hbq : (b ^ q) ^ q = b := by rw [← pow_mul, ← sq, hb2]
  rw [hbq, sub_self] at hval
  refine ⟨?_, hval⟩

  have hne : jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) b ≠ 0 := jGeomGen_sub_algebraMap_ne_zero k N _
  obtain ⟨m, hm⟩ : ∃ m, q ^ 2 - 1 = m + 1 :=
    ⟨q ^ 2 - 2, by have := Nat.one_lt_pow (two_ne_zero) (Fact.out : q.Prime).one_lt; omega⟩
  have hunit : v.HasValue (1 - (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) b) ^ (q ^ 2 - 1)) 1 := by
    have h := RamifiedWidth.S6.HasValue.sub _ hJ (v.hasValue_algebraMap b)
    have h2 := RamifiedWidth.S6.HasValue.sub _ (v.hasValue_one) (RamifiedWidth.S6.HasValue.pow _ h (m + 1))
    rw [hm]
    simpa only [sub_self, zero_pow (Nat.succ_ne_zero m), sub_zero] using h2
  rw [RamifiedWidth.S6.jGeomGen_sub_pow_sq_eq b hb2]
  exact mul_ne_zero hne (hunit.ne_zero one_ne_zero)

section Witness

variable (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]

set_option maxHeartbeats 6400000 in

private theorem exists_witness_lift (hqN : ¬ q ∣ N) (hq : 5 ≤ q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (xa : ↥(NodeLocalized.coeffSubring A K)) (hxa : NodeLocalized.redRestrict red K xa = a)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    ∃ (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)), 1 ≤ eK ∧ IsUnit ε ∧
      ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε ∧
    ∃ (G H Wu Go Ho : ↥(R.nodeIntegersOver K w)), IsUnit Wu ∧ G * H = R.nodeConst K w ϖ ^ (jWidth a * eK) * Wu ∧
      (∃ r s : ↥(R.nodeIntegersOver K w), G = r * R.nodeConst K w ϖ + s * Go) ∧
      (∃ r s : ↥(R.nodeIntegersOver K w), Go = r * R.nodeConst K w ϖ + s * G) ∧
      (∃ r s : ↥(R.nodeIntegersOver K w), H = r * R.nodeConst K w ϖ + s * Ho) ∧
      (∃ r s : ↥(R.nodeIntegersOver K w), Ho = r * R.nodeConst K w ϖ + s * H) ∧
      R.nodeResidue₁ w ⟨Go, Go.2.1⟩ = 0 ∧ R.nodeResidue₂ w ⟨Go, Go.2.1⟩ = jGeomGen k N - (jGeomGen k N ^ q) ^ q ∧
      R.nodeResidue₂ w ⟨Ho, Ho.2.1⟩ = 0 ∧ R.nodeResidue₁ w ⟨Ho, Ho.2.1⟩ = jGeomGen k N - (jGeomGen k N ^ q) ^ q := by
  classical
  have hssw : IsSupersingularPlace q N k w := hw
  have ha_ss : a ∈ ssJSet q k := ha ▸ ((isSupersingularPlace_iff q N k w).mp hssw).2.2
  have ha2 : a ^ (q ^ 2) = a := pow_q_sq_eq_self_of_mem_ssJSet q ha_ss
  obtain ⟨eK, ε, heK, hε, hqe, G', H', w', hw', hGH', -, -, -, -, -, hspanG', hspanH'⟩ :=
    ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring red a ha_ss ha2 hq K xa hxa ϖ hϖ
  have hτp := tau_const R K w hw a ha ϖ
  obtain ⟨G, hGdef⟩ : ∃ G : ↥(R.nodeIntegersOver K w), tau R K w hw a ha G' = G := ⟨_, rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ H : ↥(R.nodeIntegersOver K w), tau R K w hw a ha H' = H := ⟨_, rfl⟩
  obtain ⟨Wu, hWudef⟩ : ∃ Wu : ↥(R.nodeIntegersOver K w), tau R K w hw a ha w' = Wu := ⟨_, rfl⟩
  have hWu : IsUnit Wu := hWudef ▸ hw'.map (tau R K w hw a ha)
  have hGH : G * H = R.nodeConst K w ϖ ^ (jWidth a * eK) * Wu := by
    have h1 := congrArg (tau R K w hw a ha) hGH'
    rw [map_mul, map_mul, map_pow, hτp, hGdef, hHdef, hWudef] at h1
    exact h1
  obtain ⟨Go, hGodef⟩ : ∃ Go : ↥(R.nodeIntegersOver K w), tau R K w hw a ha
      ⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
          (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ = Go := ⟨_, rfl⟩
  obtain ⟨Ho, hHodef⟩ : ∃ Ho : ↥(R.nodeIntegersOver K w), tau R K w hw a ha
      ⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
          (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ = Ho := ⟨_, rfl⟩
  have cGo : (Go : ↥(modularFunctionFieldBar (N * q))) = jQFun N q - jFun N q ^ q := by
    rw [← hGodef]; exact coe_tau_G R K w hw a ha
  have cHo : (Ho : ↥(modularFunctionFieldBar (N * q))) = jFun N q - jQFun N q ^ q := by
    rw [← hHodef]; exact coe_tau_H R K w hw a ha
  have hG₁ : jQFun N q - jFun N q ^ q ∈ R.R₁.integers := by rw [← cGo]; exact Go.2.1.1
  have hG₂ : jQFun N q - jFun N q ^ q ∈ R.R₂.integers := by rw [← cGo]; exact Go.2.1.2.1
  have hH₁ : jFun N q - jQFun N q ^ q ∈ R.R₁.integers := by rw [← cHo]; exact Ho.2.1.1
  have hH₂ : jFun N q - jQFun N q ^ q ∈ R.R₂.integers := by rw [← cHo]; exact Ho.2.1.2.1
  have rGo₁ : R.nodeResidue₁ w ⟨Go, Go.2.1⟩ = 0 := by
    rw [nodeResidue₁_apply]
    have e : (⟨((⟨(Go : ↥(modularFunctionFieldBar (N * q))), Go.2.1⟩ : ↥(R.nodeIntegers w)) :
        ↥(modularFunctionFieldBar (N * q))), Go.2.1.1⟩ : ↥R.R₁.integers) = ⟨jQFun N q - jFun N q ^ q, hG₁⟩ :=
      Subtype.ext cGo
    rw [e]
    exact RamifiedWidth.S6.residue₁_G R hG₁
  have rGo₂ : R.nodeResidue₂ w ⟨Go, Go.2.1⟩ = jGeomGen k N - (jGeomGen k N ^ q) ^ q := by
    rw [nodeResidue₂_apply]
    have e : (⟨((⟨(Go : ↥(modularFunctionFieldBar (N * q))), Go.2.1⟩ : ↥(R.nodeIntegers w)) :
        ↥(modularFunctionFieldBar (N * q))), Go.2.1.2.1⟩ : ↥R.R₂.integers) = ⟨jQFun N q - jFun N q ^ q, hG₂⟩ :=
      Subtype.ext cGo
    rw [e]
    exact RamifiedWidth.S6.residue₂_G R hqN hG₂
  have rHo₂ : R.nodeResidue₂ w ⟨Ho, Ho.2.1⟩ = 0 := by
    rw [nodeResidue₂_apply]
    have e : (⟨((⟨(Ho : ↥(modularFunctionFieldBar (N * q))), Ho.2.1⟩ : ↥(R.nodeIntegers w)) :
        ↥(modularFunctionFieldBar (N * q))), Ho.2.1.2.1⟩ : ↥R.R₂.integers) = ⟨jFun N q - jQFun N q ^ q, hH₂⟩ :=
      Subtype.ext cHo
    rw [e]
    exact RamifiedWidth.S6.residue₂_H R hqN hH₂
  have rHo₁ : R.nodeResidue₁ w ⟨Ho, Ho.2.1⟩ = jGeomGen k N - (jGeomGen k N ^ q) ^ q := by
    rw [nodeResidue₁_apply]
    have e : (⟨((⟨(Ho : ↥(modularFunctionFieldBar (N * q))), Ho.2.1⟩ : ↥(R.nodeIntegers w)) :
        ↥(modularFunctionFieldBar (N * q))), Ho.2.1.1⟩ : ↥R.R₁.integers) = ⟨jFun N q - jQFun N q ^ q, hH₁⟩ :=
      Subtype.ext cHo
    rw [e]
    exact RamifiedWidth.S6.residue₁_H R hH₁
  have relG : ∃ r s : ↥(R.nodeIntegersOver K w), G = r * R.nodeConst K w ϖ + s * Go := by
    have hmem := hspanG'.le (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton G')))
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.mp hmem
    have h1 := congrArg (tau R K w hw a ha) hrs
    rw [map_add, map_mul, map_mul, hτp, hGodef, hGdef] at h1
    exact ⟨_, _, h1.symm⟩
  have relGo : ∃ r s : ↥(R.nodeIntegersOver K w), Go = r * R.nodeConst K w ϖ + s * G := by
    have hmem := hspanG'.ge (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.mp hmem
    have h1 := congrArg (tau R K w hw a ha) hrs
    rw [map_add, map_mul, map_mul, hτp, hGodef, hGdef] at h1
    exact ⟨_, _, h1.symm⟩
  have relH : ∃ r s : ↥(R.nodeIntegersOver K w), H = r * R.nodeConst K w ϖ + s * Ho := by
    have hmem := hspanH'.le (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton H')))
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.mp hmem
    have h1 := congrArg (tau R K w hw a ha) hrs
    rw [map_add, map_mul, map_mul, hτp, hHodef, hHdef] at h1
    exact ⟨_, _, h1.symm⟩
  have relHo : ∃ r s : ↥(R.nodeIntegersOver K w), Ho = r * R.nodeConst K w ϖ + s * H := by
    have hmem := hspanH'.ge (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.mp hmem
    have h1 := congrArg (tau R K w hw a ha) hrs
    rw [map_add, map_mul, map_mul, hτp, hHodef, hHdef] at h1
    exact ⟨_, _, h1.symm⟩
  exact ⟨eK, ε, heK, hε, hqe, G, H, Wu, Go, Ho, hWu, hGH, relG, relGo, relH, relHo, rGo₁, rGo₂, rHo₂, rHo₁⟩

end Witness

private theorem hker_of_tuple' (R : ProlongationTuple P) :
    ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A := by
  intro c
  rw [← R.redBar_residue c, map_eq_zero_iff R.redBar R.redBar.injective]
  exact IsLocalRing.residue_eq_zero_iff c

private theorem nodeResidue_nodeConst_eq_zero' (R : ProlongationTuple P)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N))
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : NodeLocalized.redRestrict red K ϖ = 0) :
    R.nodeResidue₁ w ⟨R.nodeConst K w ϖ, (R.nodeConst K w ϖ).2.1⟩ = 0 ∧
      R.nodeResidue₂ w ⟨R.nodeConst K w ϖ, (R.nodeConst K w ϖ).2.1⟩ = 0 := by
  set a : A := Subring.inclusion inf_le_left ϖ with ha_def
  have ha : red a = 0 := hϖ0
  have hres : IsLocalRing.residue A a = 0 :=
    (IsLocalRing.residue_eq_zero_iff a).mpr ((hker_of_tuple' R a).mp ha)
  constructor
  · show R.ι (R.R₁.residue
        ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ),
        (R.R₁.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩) = 0
    rw [R.R₁.residue_algebraMap a, hres, map_zero, map_zero]
  · show R.ι (R.R₂.residue
        ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ),
        (R.R₂.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩) = 0
    rw [R.R₂.residue_algebraMap a, hres, map_zero, map_zero]

private theorem exists_reduceFst_eq' (P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (w : Place k ↥(modularFunctionFieldC k N)) :
    ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P'.reduceFst V = w := by
  obtain ⟨v, hv⟩ := P'.d4 w
  haveI : CharZero ↥(modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).injective
  obtain ⟨V, hV⟩ := Place.restrictAlong_surjective (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
    (finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N q)
    (separableAlong_of_charZero (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) v
  refine ⟨V, ?_⟩
  show P'.sp (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) = w
  dsimp only at hV
  rw [hV, hv]

private theorem ord_jGeomGen_sub_pow_sq_eq_placeRamificationJ [IsAlgClosed k] [DecidableEq k]
    {w : Place k ↥(modularFunctionFieldC k N)} (hw : w ∈ ssPlaces q N k) :
    w.ord (jGeomGen k N - (jGeomGen k N ^ q) ^ q) = (placeRamificationJ N w : ℤ) ∧
    (arithFrobC q k N • w).ord (jGeomGen k N - (jGeomGen k N ^ q) ^ q) = (placeRamificationJ N w : ℤ) := by
  have hss : IsSupersingularPlace q N k w := hw
  obtain ⟨a, ha⟩ : ∃ a : k, w.evalAt (jGeomGen k N) = a := ⟨_, rfl⟩
  have ha2 : a ^ (q ^ 2) = a := by
    have h := pow_q_sq_eq_self_of_mem_ssJSet q ((isSupersingularPlace_iff q N k w).mp hss).2.2
    rwa [ha] at h
  have hJ : w.HasValue (jGeomGen k N) a := ha ▸ RamifiedWidth.S6.hasValue_evalAt w hss.1 hss.2.1.1
  have hpos : 0 < w.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) a) := by
    have h := ModularCurve.ord_sub_evalAt_pos_of_isRational hss.1 hss.2.1.1 (jGeomGen_sub_algebraMap_ne_zero k N _)
    rwa [ha] at h
  have hram : (placeRamificationJ N w : ℤ) = w.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) a) := by
    have hdef : placeRamificationJ N w
        = (w.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (w.evalAt (jGeomGen k N)))).toNat := rfl
    rw [hdef, ha]
    exact Int.toNat_of_nonneg hpos.le
  have hne : jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) a ≠ 0 := jGeomGen_sub_algebraMap_ne_zero k N _
  obtain ⟨m, hm⟩ : ∃ m, q ^ 2 - 1 = m + 1 :=
    ⟨q ^ 2 - 2, by have := Nat.one_lt_pow (two_ne_zero) (Fact.out : q.Prime).one_lt; omega⟩
  have hunit : w.HasValue (1 - (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) a) ^ (q ^ 2 - 1)) 1 := by
    have h := RamifiedWidth.S6.HasValue.sub _ hJ (w.hasValue_algebraMap a)
    have h2 := RamifiedWidth.S6.HasValue.sub _ (w.hasValue_one) (RamifiedWidth.S6.HasValue.pow _ h (m + 1))
    rw [hm]
    simpa only [sub_self, zero_pow (Nat.succ_ne_zero m), sub_zero] using h2
  have hw1 : w.ord (jGeomGen k N - (jGeomGen k N ^ q) ^ q) = (placeRamificationJ N w : ℤ) := by
    rw [RamifiedWidth.S6.jGeomGen_sub_pow_sq_eq a ha2, Place.ord_mul _ hne (hunit.ne_zero one_ne_zero),
      hunit.ord_eq_zero one_ne_zero, add_zero, hram]
  refine ⟨hw1, ?_⟩
  conv_lhs => rw [← RamifiedWidth.S6.arithFrobC_smul_jGeomGen_sub_pow_sq (q := q) (k := k) (N := N)]
  rw [SemilinearAut.ord_smul]
  exact hw1

set_option maxHeartbeats 6400000 in

private theorem main_rr (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hq : 5 ≤ q)
    (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W) (hord : R.OrderLawFixed)
    (hker : ∀ c : ↥A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hr : 1 < placeRamificationJ N w)
    (xw : ↥(NodeLocalized.coeffSubring A K)) (hxw : NodeLocalized.redRestrict red K xw = w.evalAt (jGeomGen k N))
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqe : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u) :
    E = placeWidth N w * eK := by
  classical
  have hwss : w ∈ ssPlaces q N k := hW w hw
  obtain ⟨a, ha⟩ : ∃ a : k, w.evalAt (jGeomGen k N) = a := ⟨_, rfl⟩
  have hxa : NodeLocalized.redRestrict red K xw = a := hxw.trans ha
  have hrj : placeRamificationJ N w = jWidth a := ha ▸ WidthExt.NatTail.placeRamificationJ_eq_jWidth hqN hq w hwss hr
  have hpw : placeWidth N w = 1 := WidthExt.NatTail.placeWidth_eq_one hqN hq w hwss hr
  have hr0 : 0 < placeRamificationJ N w := lt_trans zero_lt_one hr

  let ι : ↥(R.nodeIntegersOver K w) →+* ↥(R.nodeIntegers w) := Subring.inclusion (R.nodeIntegersOver_le K w)
  let N₁ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) := (R.nodeResidue₁ w).comp ι
  let N₂ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) := (R.nodeResidue₂ w).comp ι
  have hN₁ : ∀ g : ↥(R.nodeIntegersOver K w), N₁ g = R.nodeResidue₁ w ⟨g, g.2.1⟩ := fun g => rfl
  have hN₂ : ∀ g : ↥(R.nodeIntegersOver K w), N₂ g = R.nodeResidue₂ w ⟨g, g.2.1⟩ := fun g => rfl

  have hϖ0 : NodeLocalized.redRestrict red K ϖ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
  obtain ⟨hc₁, hc₂⟩ := nodeResidue_nodeConst_eq_zero' R K w ϖ hϖ0
  have hN₁p : N₁ (R.nodeConst K w ϖ) = 0 := hc₁
  have hN₂p : N₂ (R.nodeConst K w ϖ) = 0 := hc₂

  have hvalA : R.ValueIntegralityLaw w := valueIntegralityLaw_of_orderLawFixed R hqN hord w hwss
  obtain ⟨V, hV⟩ := exists_reduceFst_eq' P w
  have hreg₁ : ∀ g : ↥(R.nodeIntegersOver K w), 0 ≤ w.ord (N₁ g) := fun g =>
    Place.ord_nonneg_of_mem _
      (hasValue_nodeResidueFst_red_evalAt_of_orderLawFixed R hqN hmodel hord W hW hreg hval K w hw hvalA g V hV).mem
  have hreg₂ : ∀ g : ↥(R.nodeIntegersOver K w), 0 ≤ (arithFrobC q k N • w).ord (N₂ g) := fun g =>
    Place.ord_nonneg_of_mem _
      (hasValue_nodeResidueSnd_red_evalAt_of_orderLawFixed R hqN hmodel hord W hW hreg hval K w hw hvalA g V hV).mem

  obtain ⟨eK', ε', -, hε', hqe', G, H, Wu, Go, Ho, hWu, hGH, relG, relGo, relH, relHo, rGo₁, rGo₂, rHo₂, rHo₁⟩ :=
    exists_witness_lift R hqN hq K w hwss a ha xw hxa ϖ hϖ
  obtain ⟨hDne, -⟩ := jGeomGen_sub_pow_sq_ne_zero (q := q) hwss
  obtain ⟨hordD₁, hordD₂⟩ := ord_jGeomGen_sub_pow_sq_eq_placeRamificationJ (q := q) hwss
  have rGo₁' : N₁ Go = 0 := rGo₁
  have rGo₂' : N₂ Go = jGeomGen k N - (jGeomGen k N ^ q) ^ q := rGo₂
  have rHo₂' : N₂ Ho = 0 := rHo₂
  have rHo₁' : N₁ Ho = jGeomGen k N - (jGeomGen k N ^ q) ^ q := rHo₁

  have x_fst : N₁ G = 0 := by
    obtain ⟨r, s, hrs⟩ := relG
    rw [hrs, map_add, map_mul, map_mul, hN₁p, rGo₁', mul_zero, mul_zero, add_zero]
  have y_snd : N₂ H = 0 := by
    obtain ⟨r, s, hrs⟩ := relH
    rw [hrs, map_add, map_mul, map_mul, hN₂p, rHo₂', mul_zero, mul_zero, add_zero]
  have x_snd : (arithFrobC q k N • w).ord (N₂ G) = (placeRamificationJ N w : ℤ) := by
    obtain ⟨r, s, hrs⟩ := relG
    obtain ⟨r', s', hrs'⟩ := relGo
    have e1 : N₂ G = N₂ s * (jGeomGen k N - (jGeomGen k N ^ q) ^ q) := by
      rw [hrs, map_add, map_mul, map_mul, hN₂p, rGo₂', mul_zero, zero_add]
    have e2 : jGeomGen k N - (jGeomGen k N ^ q) ^ q = N₂ s' * N₂ G := by
      rw [← rGo₂']
      conv_lhs => rw [hrs']
      rw [map_add, map_mul, map_mul, hN₂p, mul_zero, zero_add]
    have hG0 : N₂ G ≠ 0 := fun h => hDne (by rw [e2, h, mul_zero])
    have hs0 : N₂ s ≠ 0 := fun h => hG0 (by rw [e1, h, zero_mul])
    have hs'0 : N₂ s' ≠ 0 := fun h => hDne (by rw [e2, h, zero_mul])
    have o1 : (arithFrobC q k N • w).ord (N₂ G) = (arithFrobC q k N • w).ord (N₂ s) + placeRamificationJ N w := by
      rw [e1, Place.ord_mul _ hs0 hDne, hordD₂]
    have o2 : (placeRamificationJ N w : ℤ)
        = (arithFrobC q k N • w).ord (N₂ s') + (arithFrobC q k N • w).ord (N₂ G) := by
      conv_lhs => rw [← hordD₂, e2]
      rw [Place.ord_mul _ hs'0 hG0]
    have n1 := hreg₂ s
    have n2 := hreg₂ s'
    omega
  have y_fst : w.ord (N₁ H) = (placeRamificationJ N w : ℤ) := by
    obtain ⟨r, s, hrs⟩ := relH
    obtain ⟨r', s', hrs'⟩ := relHo
    have e1 : N₁ H = N₁ s * (jGeomGen k N - (jGeomGen k N ^ q) ^ q) := by
      rw [hrs, map_add, map_mul, map_mul, hN₁p, rHo₁', mul_zero, zero_add]
    have e2 : jGeomGen k N - (jGeomGen k N ^ q) ^ q = N₁ s' * N₁ H := by
      rw [← rHo₁']
      conv_lhs => rw [hrs']
      rw [map_add, map_mul, map_mul, hN₁p, mul_zero, zero_add]
    have hH0 : N₁ H ≠ 0 := fun h => hDne (by rw [e2, h, mul_zero])
    have hs0 : N₁ s ≠ 0 := fun h => hH0 (by rw [e1, h, zero_mul])
    have hs'0 : N₁ s' ≠ 0 := fun h => hDne (by rw [e2, h, zero_mul])
    have o1 : w.ord (N₁ H) = w.ord (N₁ s) + placeRamificationJ N w := by
      rw [e1, Place.ord_mul _ hs0 hDne, hordD₁]
    have o2 : (placeRamificationJ N w : ℤ) = w.ord (N₁ s') + w.ord (N₁ H) := by
      conv_lhs => rw [← hordD₁, e2]
      rw [Place.ord_mul _ hs'0 hH0]
    have n1 := hreg₁ s
    have n2 := hreg₁ s'
    omega

  have hG2 : N₂ G ≠ 0 := fun h => by
    rw [h, Place.ord_zero] at x_snd
    exact (Int.natCast_pos.mpr hr0).ne x_snd
  have hH1 : N₁ H ≠ 0 := fun h => by
    rw [h, Place.ord_zero] at y_fst
    exact (Int.natCast_pos.mpr hr0).ne y_fst

  obtain ⟨εi, hεi⟩ := hε'.exists_right_inv
  have hεiU : IsUnit εi := ⟨⟨εi, ε', by rw [mul_comm]; exact hεi, hεi⟩, rfl⟩
  have hϖpow : ϖ ^ eK' = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) * εi := by
    rw [hqe', mul_assoc, hεi, mul_one]
  have hu₀ : IsUnit (R.nodeConst K w εi ^ jWidth a * Wu) := ((hεiU.map (R.nodeConst K w)).pow _).mul hWu
  have hGH₁ : G * H =
      R.nodeConst K w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) ^ (jWidth a)
        * (R.nodeConst K w εi ^ jWidth a * Wu) := by
    rw [hGH, pow_mul', ← map_pow, hϖpow, map_mul, mul_pow, mul_assoc]

  have hkey0 := WidthRatio.valuation_pow_mul_eq_of_pair W hreg hw ϖ c E u hu hxy (placeRamificationJ N w) G H _ hu₀
    (by rw [← hN₂]; exact hG2) (by rw [← hN₂]; exact x_snd) (by rw [← hN₁]; exact hH1)
    ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) (jWidth a) hGH₁

  have hvε : A.valuation (ε : AlgebraicClosure ℚ) = 1 := by
    obtain ⟨εj, hεj⟩ := hε.exists_right_inv
    have hprod : A.valuation (ε : AlgebraicClosure ℚ) * A.valuation (εj : AlgebraicClosure ℚ) = 1 := by
      rw [← map_mul]
      have h := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K) => A.valuation (z : AlgebraicClosure ℚ)) hεj
      simpa using h
    have hle1 : A.valuation (ε : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr ε.2.1
    have hle2 : A.valuation (εj : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr εj.2.1
    refine le_antisymm hle1 ?_
    calc (1 : _) = A.valuation (ε : AlgebraicClosure ℚ) * A.valuation (εj : AlgebraicClosure ℚ) := hprod.symm
      _ ≤ A.valuation (ε : AlgebraicClosure ℚ) * 1 := mul_le_mul_right hle2 _
      _ = A.valuation (ε : AlgebraicClosure ℚ) := mul_one _
  have hqcoe : (((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ)
      = (ϖ : AlgebraicClosure ℚ) ^ eK * (ε : AlgebraicClosure ℚ) := by
    have h := congrArg Subtype.val hqe
    push_cast at h
    exact h
  have hkey : A.valuation (ϖ : AlgebraicClosure ℚ) ^ (placeRamificationJ N w * E)
      = A.valuation (ϖ : AlgebraicClosure ℚ) ^ (eK * jWidth a) := by
    rw [hkey0, hqcoe, map_mul, map_pow, hvε, mul_one, ← pow_mul]
  have hv1 : A.valuation (ϖ : AlgebraicClosure ℚ) < 1 := by
    have hmem : (⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := (hker _).mp hϖ0
    exact (A.valuation_lt_one_iff _).mp hmem
  have hϖne : (ϖ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    rcases Nat.eq_zero_or_pos eK with hz | hpos
    · have hu1 : IsUnit (NodeLocalized.redRestrict red K ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K))) := by
        rw [hqe, hz, pow_zero, one_mul]; exact hε.map _
      rw [map_natCast, CharP.cast_eq_zero k q] at hu1
      exact not_isUnit_zero hu1
    · have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
      have h1 := hqcoe
      rw [h0, zero_pow hpos.ne', zero_mul] at h1
      exact hq0 h1
  have hv0 : 0 < A.valuation (ϖ : AlgebraicClosure ℚ) :=
    lt_of_le_of_ne zero_le' (fun h => hϖne ((map_eq_zero _).mp h.symm))
  have hE : placeRamificationJ N w * E = eK * jWidth a := pow_right_injective₀ hv0 hv1.ne hkey
  rw [hpw, one_mul]
  rw [hrj, mul_comm eK] at hE
  exact Nat.eq_of_mul_eq_mul_left (hrj ▸ hr0) hE

end RamifiedWidth.ExpN

open AlgebraicCurve IsLocalRing ModularCurve in
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hq : 5 ≤ q)
    (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W) (hord : R.OrderLawFixed)
    (hker : ∀ c : ↥A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hr : 1 < placeRamificationJ N w)
    (xw : ↥(NodeLocalized.coeffSubring A K)) (hxw : NodeLocalized.redRestrict red K xw = w.evalAt (jGeomGen k N))
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqe : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u) :
    E = placeWidth N w * eK := by
  exact RamifiedWidth.ExpN.main_rr R hqN hq hmodel W hW hreg hval hord hker K w hw hr xw hxw ϖ hϖ eK ε hε hqe c E u hu
    hxy

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidth_mul_of_orderLawFixed_of_one_lt_placeRamificationJ
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidth_mul_of_orderLawFixed_of_one_lt_placeRamificationJ (solution)
