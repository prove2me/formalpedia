-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_nodeCoordinates_presentation_levelOne_of_orderLawFixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/86ce6a62-5963-5bda-8de3-3a4e10b76816

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_nodeEquation_jWidth_of_eq_zero_or_eq_1728_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_and_isNoetherianRing_nodeIntegersOver_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_levelOne_of_five_le
import Theorems.Thm_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
import Theorems.Thm_ModularCurve_NodeLocalized_exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul
import Theorems.Thm_ValuationSubring_exists_dvr_subring_of_forall_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_nodeCoordinates_presentation_levelOne_of_orderLawFixed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open scoped Pointwise

namespace S12EL
namespace Pres

section Kernel
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]

theorem pow_injective_of_lt_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {γ : Γ} (h0 : γ ≠ 0) (h1 : γ < 1)
    {m n : ℕ} (h : γ ^ m = γ ^ n) : m = n := by
  set u : Γˣ := Units.mk0 γ h0 with hu
  have hu1 : u < 1 := by rw [← Units.val_lt_val, hu, Units.val_mk0, Units.val_one]; exact h1
  have hum : ∀ j : ℕ, ((u ^ j : Γˣ) : Γ) = γ ^ j := fun j => by rw [Units.val_pow_eq_pow_val, hu, Units.val_mk0]
  have h' : u ^ m = u ^ n := Units.ext (by rw [hum, hum]; exact h)
  have hinv : 1 < u⁻¹ := one_lt_inv'.mpr hu1
  have hsm : StrictMono fun j : ℤ => (u⁻¹) ^ j := zpow_right_strictMono hinv
  have : (u⁻¹) ^ (-(m : ℤ)) = (u⁻¹) ^ (-(n : ℤ)) := by
    rw [inv_zpow', inv_zpow', neg_neg, neg_neg, zpow_natCast, zpow_natCast, h']
  have := hsm.injective this
  omega

theorem valuation_eq_one_of_mem_of_inv_mem {s : AlgebraicClosure ℚ} (h0 : s ≠ 0)
    (hs : s ∈ A) (hs' : s⁻¹ ∈ A) : A.valuation s = 1 := by
  apply le_antisymm ((A.valuation_le_one_iff _).mpr hs)
  have h1 : A.valuation s⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr hs'
  by_contra hlt
  push_neg at hlt
  have hmul : A.valuation s * A.valuation s⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ h0, map_one]
  exact absurd hmul (mul_lt_one_of_lt_of_le hlt h1).ne

theorem valuation_eq_one_of_isUnit (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) {ε : ↥(NodeLocalized.coeffSubring A K₀)} (hε : IsUnit ε) :
    A.valuation ((ε : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) = 1 := by
  obtain ⟨eu, heu⟩ := hε
  have hinv : ((eu⁻¹ : (↥(NodeLocalized.coeffSubring A K₀))ˣ) : ↥(NodeLocalized.coeffSubring A K₀)) * ε = 1 := by rw [← heu, Units.inv_mul]
  have hε0 : ((ε : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    have : (ε : ↥(NodeLocalized.coeffSubring A K₀)) = 0 := Subtype.ext h0
    rw [this, mul_zero] at hinv
    exact zero_ne_one hinv
  refine valuation_eq_one_of_mem_of_inv_mem hε0 ε.2.1 ?_
  have hcoe : (((eu⁻¹ : (↥(NodeLocalized.coeffSubring A K₀))ˣ) : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) = ((ε : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← Subring.coe_mul, hinv, Subring.coe_one])
  rw [← hcoe]
  exact ((eu⁻¹ : (↥(NodeLocalized.coeffSubring A K₀))ˣ) : ↥(NodeLocalized.coeffSubring A K₀)).2.1

theorem redRestrict_eq_zero_iff_of_inertiaFixed (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K₀]
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K₀, σ z = z) :
    ∀ d : ↥(NodeLocalized.coeffSubring A K₀), NodeLocalized.redRestrict red K₀ d = 0 ↔ ∃ d', d = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) * d' := by
  classical
  obtain ⟨ϖ₀, hϖ₀, e, ε, he, hε, hqe⟩ :=
    NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul red hker K₀
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero

  have hεv : A.valuation ((ε : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) = 1 := valuation_eq_one_of_isUnit K₀ hε
  have hqe' : ((q : ℕ) : AlgebraicClosure ℚ) = ((ϖ₀ : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) ^ e * ((ε : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) := by
    have := congrArg (fun t : ↥(NodeLocalized.coeffSubring A K₀) => (t : AlgebraicClosure ℚ)) hqe
    simpa using this
  have hϖ0 : ((ϖ₀ : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega), zero_mul] at hqe'; exact hq0 hqe'

  have hϖred : NodeLocalized.redRestrict red K₀ ϖ₀ = 0 := (hϖ₀ ϖ₀).mpr ⟨1, by rw [mul_one]⟩
  have hϖmax : (⟨((ϖ₀ : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ), ϖ₀.2.1⟩ : A) ∈ IsLocalRing.maximalIdeal A := (hker _).mp hϖred
  have hϖv : A.valuation ((ϖ₀ : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) < 1 := (A.valuation_lt_one_iff _).mp hϖmax

  have hqA : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := by
    rw [hqe', map_mul, map_pow, hεv, mul_one]
    exact pow_lt_one₀ zero_le' hϖv (by omega)
  have hqnon : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := (ValuationSubring.mem_nonunits_iff A).mpr hqA

  obtain ⟨O, hSO, hOA, -, hDVR, hirr, hnu⟩ :=
    ValuationSubring.exists_dvr_subring_of_forall_mem_inertiaSubgroupIn q A hqnon {((ϖ₀ : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ)}
      (fun x hx => by
        rw [Finset.mem_singleton] at hx
        subst hx
        exact ⟨ϖ₀.2.1, fun σ hσ => hfix σ hσ _ ϖ₀.2.2⟩)
  haveI : IsDiscreteValuationRing O := hDVR
  have hϖO : ((ϖ₀ : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) ∈ O := hSO (by simp)
  have hz0 : (⟨_, hϖO⟩ : O) ≠ 0 := fun h => hϖ0 (congrArg Subtype.val h)
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.associated_pow_irreducible hz0 hirr

  have hvw : A.valuation (((w : O) : O) : AlgebraicClosure ℚ) = 1 := by
    have h1 : (((w : O) : AlgebraicClosure ℚ)) * (((w⁻¹ : Oˣ) : O) : AlgebraicClosure ℚ) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    have hw0 : ((w : O) : AlgebraicClosure ℚ) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    exact valuation_eq_one_of_mem_of_inv_mem hw0 (hOA (w : O).2)
      (by rw [← eq_inv_of_mul_eq_one_right h1]; exact hOA ((w⁻¹ : Oˣ) : O).2)
  have hvϖn : A.valuation ((ϖ₀ : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ n := by
    have h := congrArg (fun t : O => A.valuation (t : AlgebraicClosure ℚ)) hw
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hvw, mul_one] at h
    convert h using 2
    rfl

  have hvq : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ 1 = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ (n * e) := by
    rw [pow_one, pow_mul, ← hvϖn]
    conv_lhs => rw [hqe', map_mul, map_pow, hεv, mul_one]
  have hγ0 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
  have hne : 1 = n * e := pow_injective_of_lt_one hγ0 hqA hvq
  have he1 : e = 1 := by
    rcases Nat.eq_one_of_mul_eq_one_left hne.symm with h
    exact h

  rw [he1, pow_one] at hqe
  obtain ⟨εu, hεu⟩ := hε
  intro d
  rw [hϖ₀ d]
  constructor
  · rintro ⟨d', rfl⟩
    refine ⟨((εu⁻¹ : (↥(NodeLocalized.coeffSubring A K₀))ˣ) : ↥(NodeLocalized.coeffSubring A K₀)) * d', ?_⟩
    rw [hqe, ← hεu, mul_assoc, ← mul_assoc (εu : ↥(NodeLocalized.coeffSubring A K₀)), Units.mul_inv, one_mul]
  · rintro ⟨d', rfl⟩
    exact ⟨ε * d', by rw [hqe, mul_assoc]⟩

end Kernel

section Ideals
variable {Rg : Type*} [CommRing Rg]

theorem span_pair_sup_span_pair (p x y : Rg) : Ideal.span {p, x} ⊔ Ideal.span {p, y} = Ideal.span {p, x, y} := by
  rw [← Ideal.span_union]
  congr 1
  ext z
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem not_mem_of_span_eq {p x y x₀ y₀ : Rg} (hX : Ideal.span {p, x} = Ideal.span {p, x₀})
    (hY : Ideal.span {p, y} = Ideal.span {p, y₀}) (hny : y ∉ Ideal.span {p, x}) : y₀ ∉ Ideal.span {p, x₀} := by
  intro h
  apply hny
  have hle : Ideal.span {p, y₀} ≤ Ideal.span {p, x₀} := by
    rw [Ideal.span_le]
    rintro z hz
    rcases hz with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · exact h
  have hy : y ∈ Ideal.span {p, y} := Ideal.subset_span (by simp)
  rw [hY] at hy
  rw [hX]
  exact hle hy

end Ideals

end S12EL.Pres

open S12EL.Pres in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : ProlongationTuple P)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) :
    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K₀),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K₀, σ z = z) ∧
      (∀ d : ↥(NodeLocalized.coeffSubring A K₀),
        NodeLocalized.redRestrict red K₀ d = 0 ↔ ∃ d', d = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) * d') ∧
      ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
        ∃ (c : R.NodeCoordinates K₀ w) (u : ↥(R.nodeIntegersOver K₀ w)),
          (IsUnit (u) ∧
        c.x * c.y = R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ (jWidth (w.evalAt (jGeomGen k 1)) * 1) * u) ∧
          ((Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K₀ w), M.IsMaximal →
          M = Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.x, c.y}) ∧
          ((Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.x}).IsPrime ∧
        (Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.x} ∧
        c.x ∉ Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.y}) ∧
          IsNoetherianRing ↥(R.nodeIntegersOver K₀ w) ∧
          (∀ g : ↥(R.nodeIntegersOver K₀ w),
        ∃ o : ↥(NodeLocalized.coeffSubring A K₀), ¬ IsUnit (g - R.nodeConst K₀ w o)) := by
  classical
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  have hq1 : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp h)

  have hss : ∀ w ∈ W, w.evalAt (jGeomGen k 1) ∈ ssJSet q k := fun w hw =>
    ((isSupersingularPlace_iff q 1 k w).mp ((mem_ssPlaces_iff q 1 k).mp (hW w hw))).2.2
  set S : Finset k := W.image (fun w => w.evalAt (jGeomGen k 1)) with hSdef
  have hS : ∀ a ∈ S, a ^ (q ^ 2) = a := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ha
    exact pow_q_sq_eq_self_of_mem_ssJSet q (hss w hw)
  obtain ⟨K₀, fd, hfix, hrange⟩ :=
    NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict q A k red S hS
  haveI := fd
  have hϖq : ∀ d : ↥(NodeLocalized.coeffSubring A K₀), NodeLocalized.redRestrict red K₀ d = 0 ↔ ∃ d', d = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) * d' :=
    redRestrict_eq_zero_iff_of_inertiaFixed red hker K₀ hfix
  have hqe : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ 1 * 1 := by rw [pow_one, mul_one]
  refine ⟨K₀, fd, hfix, hϖq, fun w hw => ?_⟩

  have hwss : w ∈ ssPlaces q 1 k := hW w hw
  have hfixφ : arithFrobC q k 1 • (arithFrobC q k 1 • w) = w := by
    rw [arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr w,
      arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr,
      frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k 1 hq1 data hKr w hwss]
  obtain ⟨xw, hxw⟩ : w.evalAt (jGeomGen k 1) ∈ Set.range (NodeLocalized.redRestrict red K₀) :=
    hrange _ (Finset.mem_image_of_mem _ hw)

  have seed : ∃ (c₀ : R.NodeCoordinates K₀ w) (u₀ : ↥(R.nodeIntegersOver K₀ w)), IsUnit u₀ ∧
      c₀.x * c₀.y = R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ (jWidth (w.evalAt (jGeomGen k 1)) * 1) * u₀ := by
    by_cases hgen : w.evalAt (jGeomGen k 1) ≠ 0 ∧ w.evalAt (jGeomGen k 1) ≠ 1728
    · obtain ⟨c₀, -, -, u₀, hu₀, hxy₀⟩ :=
        exists_nodeCoordinates_levelOneNodeCoord R hker hq1 hq5 w hwss hfixφ _ rfl hgen.1 hgen.2 K₀
          ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) hϖq 1 1 isUnit_one hqe
      refine ⟨c₀, u₀, hu₀, ?_⟩
      rw [jWidth_of_ne hgen.1 hgen.2, mul_one]
      exact hxy₀
    · have hwide : w.evalAt (jGeomGen k 1) = 0 ∨ w.evalAt (jGeomGen k 1) = 1728 := by
        by_cases h0 : w.evalAt (jGeomGen k 1) = 0
        · exact Or.inl h0
        · push_neg at hgen
          exact Or.inr (hgen h0)
      exact exists_nodeCoordinates_nodeEquation_jWidth_of_eq_zero_or_eq_1728_levelOne R hker hq5 hR W hW hRL hNV w hw
        hfixφ _ rfl hwide K₀ ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) hϖq 1 1 isUnit_one hqe
  obtain ⟨c₀, u₀, hu₀, hxy₀⟩ := seed

  obtain ⟨c, hX, hY, eK', ε', -, -, -, E, u', -, -, -, hmax, huniq, hpx, hpy, hny, hnx⟩ :=
    exists_crossingPresentation_nodeIntegersOver_levelOne R hq5 hR W hW hRL hNV K₀ w hw _ rfl xw hxw c₀
      ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) hϖq
  have hM : Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c₀.x, c₀.y}
      = Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.x, c.y} := by
    rw [← span_pair_sup_span_pair, ← span_pair_sup_span_pair, hX, hY]

  obtain ⟨V, hV⟩ := PlaceSpecialization.reduceFst_surjective P w
  refine ⟨c₀, u₀, ⟨hu₀, hxy₀⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, fun g => ?_⟩
  · rw [hM]
    exact ⟨hmax, huniq⟩
  · rw [← hX]; exact hpx
  · rw [← hY]; exact hpy
  · exact not_mem_of_span_eq hX hY hny
  · exact not_mem_of_span_eq hY hX hnx
  · exact (isLocalRing_and_isNoetherianRing_nodeIntegersOver_levelOne R hR W hW hRL K₀ w hw _ rfl xw hxw).2
  · exact exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_levelOne_of_five_le R hq5 hO W hW hRL K₀ w hw
      V hV ⟨xw, hxw⟩ g

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_nodeCoordinates_presentation_levelOne_of_orderLawFixed
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_nodeCoordinates_presentation_levelOne_of_orderLawFixed (solution)
