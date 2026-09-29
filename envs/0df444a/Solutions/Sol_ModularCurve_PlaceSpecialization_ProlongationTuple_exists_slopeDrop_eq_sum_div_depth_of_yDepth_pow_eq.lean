-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4f1e0316-bb37-56b8-8aba-3602d1e4c55c

import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ModularCurve_UVCrossingModel_gaussOrder_mul
import Theorems.Thm_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_circleIndexDrop
import Theorems.Thm_ModularCurve_UVCrossingModel_sInf_dominantIndices_eq_of_sub_mul_U_pow_mem
import Theorems.Thm_ModularCurve_UVCrossingModel_existsUnique_normalForm
import Theorems.Thm_ModularCurve_UVCrossingModel_sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_two_le_ringKrullDim_adicCompletion_nodeIntegersOver
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_surjective_mvPowerSeries_adicCompletion_nodeIntegersOver
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_ord_smul_of_ne_zero
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel_of_isMaximal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_gaussOrder_fst_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_gaussOrder_snd_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_integers_nodeResidueFst_ne_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_eq_finsum_rank_mul_length_of_total_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_eq_finsum_rank_mul_length_total_of_nodeResidue_ne_zero
import Theorems.Thm_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_sInf_sub_sSup
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Theorems.Thm_ModularCurve_UVCrossingModel_sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul
import Theorems.Thm_ModularCurve_UVCrossingModel_gaussOrder_scaled_eq_repGaussOrder_normalForm
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed
import Theorems.Thm_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring
import Theorems.Thm_PowerSeries_isAdicComplete_quotient_span_X_sub_C_of_irreducible
import Theorems.Thm_ModularCurve_UVCrossingModel_gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq_scaled
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_zero ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve ModularCurve.PlaceSpecialization"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve ModularCurve.PlaceSpecialization"
open Finset BigOperators

section LocBranchCore
open ModularCurve.PlaceSpecialization.ProlongationTuple

private noncomputable scoped instance (priority := high) AnnulusLocBranch.instAlgebraResidueFieldFullC
    {L : Type*} [Field L] (A : ValuationSubring L) (N : ℕ) :
    Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N) :=
  SubalgebraClass.toAlgebra (modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)

namespace AnnulusLocBranch

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private noncomputable def res₁ (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) :
    ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
  (R.nodeResidue₁ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))

private theorem res₁_apply (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (b : ↥(R.nodeIntegersOver K w)) :
    res₁ R K w b = R.nodeResidue₁ w ⟨b, b.2.1⟩ := rfl

private def toR₁ (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) : ↥(R.nodeIntegersOver K w) →+* ↥R.R₁.integers where
  toFun v := ⟨v, v.2.1.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem res₁_eq (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (v : ↥(R.nodeIntegersOver K w)) :
    res₁ R K w v = R.ι (R.R₁.residue (toR₁ R K w v)) := rfl

private theorem coe_toR₁ (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (v : ↥(R.nodeIntegersOver K w)) :
    ((toR₁ R K w v : ↥R.R₁.integers) : ↥(modularFunctionFieldBar (N * q))) = v := rfl

private theorem not_isUnit_toR₁_nodeConst (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    ¬ IsUnit (toR₁ R K w (R.nodeConst K w ϖ)) := by
  set a : A := ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ with ha
  have hred : red a = 0 := hϖ
  have hanu : ¬ IsUnit a := fun hu => by
    have := hu.map red
    rw [hred] at this
    exact not_isUnit_zero this
  have hfval : ((toR₁ R K w (R.nodeConst K w ϖ) : ↥R.R₁.integers) : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := rfl
  intro hu
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have hg' : ((toR₁ R K w (R.nodeConst K w ϖ) : ↥R.R₁.integers) : ↥(modularFunctionFieldBar (N * q))) *
      (g : ↥(modularFunctionFieldBar (N * q))) = 1 := by
    rw [← MulMemClass.coe_mul, hg]; rfl
  have ha0 : (a : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    rw [hfval, h0, map_zero, zero_mul] at hg'
    exact zero_ne_one hg'
  have hginv : (g : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ ((a : AlgebraicClosure ℚ)⁻¹) := by
    rw [map_inv₀, ← hfval]
    exact (eq_inv_of_mul_eq_one_right hg')
  have hmemA : (a : AlgebraicClosure ℚ)⁻¹ ∈ A := by
    have := g.2
    rw [hginv] at this
    exact (R.R₁.algebraMap_mem_iff _).mp this
  exact hanu (isUnit_iff_exists_inv.mpr ⟨⟨(a : AlgebraicClosure ℚ)⁻¹, hmemA⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩)

private theorem res₁_nodeConst_eq_zero (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    res₁ R K w (R.nodeConst K w ϖ) = 0 := by
  rw [res₁_apply, nodeResidue₁_apply, residue₁_apply]
  set a : A := ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ with ha
  have hred : red a = 0 := hϖ
  have hanu : ¬ IsUnit a := fun hu => by
    have := hu.map red
    rw [hred] at this
    exact not_isUnit_zero this
  set f : ↥R.R₁.integers := ⟨((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))),
      (R.nodeConst K w ϖ).2.1.1⟩ with hf
  have hfval : (f : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := rfl
  have hfnu : ¬ IsUnit f := by
    intro hu
    obtain ⟨g, hg⟩ := hu.exists_right_inv
    have hg' : (f : ↥(modularFunctionFieldBar (N * q))) * (g : ↥(modularFunctionFieldBar (N * q))) = 1 := by
      rw [← MulMemClass.coe_mul, hg]; rfl
    have ha0 : (a : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      rw [hfval, h0, map_zero, zero_mul] at hg'
      exact zero_ne_one hg'
    have hginv : (g : ↥(modularFunctionFieldBar (N * q))) =
        algebraMap (AlgebraicClosure ℚ) _ ((a : AlgebraicClosure ℚ)⁻¹) := by
      rw [map_inv₀, ← hfval]
      exact (eq_inv_of_mul_eq_one_right hg')
    have hmemA : (a : AlgebraicClosure ℚ)⁻¹ ∈ A := by
      have := g.2
      rw [hginv] at this
      exact (R.R₁.algebraMap_mem_iff _).mp this
    apply hanu
    exact isUnit_iff_exists_inv.mpr ⟨⟨(a : AlgebraicClosure ℚ)⁻¹, hmemA⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
  have hmem : f ∈ maximalIdeal ↥R.R₁.integers := (mem_maximalIdeal _).mpr hfnu
  rw [← R.R₁.ker_residue, RingHom.mem_ker] at hmem
  show R.ι (R.R₁.residue f) = 0
  rw [hmem, map_zero]

private theorem valuation_nodeConst_lt_one (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    R.R₁.integers.valuation ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) < 1 := by
  have hmem : toR₁ R K w (R.nodeConst K w ϖ) ∈ maximalIdeal ↥R.R₁.integers :=
    (mem_maximalIdeal _).mpr (not_isUnit_toR₁_nodeConst R K w ϖ hϖ)
  exact (ValuationSubring.valuation_lt_one_iff _ _).mp hmem

private theorem valuation_eq_one_of_res₁_ne_zero (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (v : ↥(R.nodeIntegersOver K w)) (h : res₁ R K w v ≠ 0) :
    R.R₁.integers.valuation (v : ↥(modularFunctionFieldBar (N * q))) = 1 := by
  have h1 : IsUnit (toR₁ R K w v) := by
    apply R.R₁.isUnit_of_residue_ne_zero
    intro h0
    exact h (by rw [res₁_eq, h0, map_zero])
  exact (ValuationSubring.valuation_eq_one_iff _ _).mp h1

section BranchKer

variable (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
  (ϖ : ↥(NodeLocalized.coeffSubring A K))

private theorem span_le_ker (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    Ideal.span {R.nodeConst K w ϖ, c.x} ≤ RingHom.ker (res₁ R K w) := by
  rw [Ideal.span_le]
  rintro z (rfl | rfl)
  · exact res₁_nodeConst_eq_zero R K w ϖ hϖ
  · show res₁ R K w c.x = 0
    rw [res₁_apply]
    exact c.x_fst

private theorem ker_res₁_eq [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hpr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime) (hy : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x}) :
    RingHom.ker (res₁ R K w) = Ideal.span {R.nodeConst K w ϖ, c.x} := by
  classical
  set 𝔮 : Ideal ↥(R.nodeIntegersOver K w) := Ideal.span {R.nodeConst K w ϖ, c.x} with h𝔮
  haveI : 𝔮.IsPrime := hpr
  haveI hloc : IsLocalRing ↥(R.nodeIntegersOver K w) := IsLocalRing.of_unique_max_ideal ⟨_, hmax.1, hmax.2⟩
  have hmaxB : maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y} :=
    hmax.2 _ (maximalIdeal.isMaximal _)
  refine le_antisymm ?_ (span_le_ker R K w c ϖ hϖ)

  set Q := ↥(R.nodeIntegersOver K w) ⧸ 𝔮
  set mkq : ↥(R.nodeIntegersOver K w) →+* Q := Ideal.Quotient.mk 𝔮
  haveI : IsDomain Q := Ideal.Quotient.isDomain 𝔮
  haveI : Nontrivial Q := inferInstance
  haveI : IsLocalRing Q := IsLocalRing.of_surjective' mkq Ideal.Quotient.mk_surjective
  have hybar_ne : mkq c.y ≠ 0 := fun h => hy (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hmaxQ : maximalIdeal Q = Ideal.span {mkq c.y} := by

    have hcomap : (maximalIdeal Q).comap mkq = maximalIdeal ↥(R.nodeIntegersOver K w) := by
      have := Ideal.comap_isMaximal_of_surjective mkq Ideal.Quotient.mk_surjective (K := maximalIdeal Q)
      exact (hmax.2 _ this).trans hmaxB.symm
    have hmap : maximalIdeal Q = (maximalIdeal ↥(R.nodeIntegersOver K w)).map mkq := by
      rw [← hcomap, Ideal.map_comap_of_surjective mkq Ideal.Quotient.mk_surjective]
    rw [hmap, hmaxB, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨z, hz, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · have : mkq (R.nodeConst K w ϖ) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
        rw [this]; exact zero_mem _
      · have : mkq c.x = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        rw [this]; exact zero_mem _
      · exact Ideal.subset_span rfl
    · exact Ideal.span_mono (Set.singleton_subset_iff.mpr
        ⟨c.y, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)), rfl⟩)
  have hnotfield : ¬ IsField Q := by
    intro hF
    have := (IsLocalRing.isField_iff_maximalIdeal_eq (R := Q)).mp hF
    rw [hmaxQ, Ideal.span_singleton_eq_bot] at this
    exact hybar_ne this
  have hP : (maximalIdeal Q).IsPrincipal := ⟨⟨mkq c.y, hmaxQ⟩⟩
  haveI : IsDiscreteValuationRing Q := ((IsDiscreteValuationRing.TFAE Q hnotfield).out 0 4).mpr hP
  have hirr : Irreducible (mkq c.y) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (mkq c.y) hybar_ne hmaxQ

  intro s hs
  by_contra hsnot
  have hI : (RingHom.ker (res₁ R K w)).map mkq ≠ ⊥ := by
    intro hbot
    apply hsnot
    have : mkq s ∈ (RingHom.ker (res₁ R K w)).map mkq := Ideal.mem_map_of_mem _ hs
    rw [hbot, Ideal.mem_bot] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hirr
  have hyn : mkq c.y ^ n ∈ (RingHom.ker (res₁ R K w)).map mkq := by rw [hn]; exact Ideal.subset_span rfl
  rw [← map_pow, Ideal.mem_map_iff_of_surjective mkq Ideal.Quotient.mk_surjective] at hyn
  obtain ⟨t, ht, hty⟩ := hyn

  have hdiff : c.y ^ n - t ∈ 𝔮 := by
    rw [← Ideal.Quotient.eq, hty]
  have hyn' : c.y ^ n ∈ RingHom.ker (res₁ R K w) := by
    have := add_mem (span_le_ker R K w c ϖ hϖ hdiff) ht
    rwa [sub_add_cancel] at this
  rw [RingHom.mem_ker, map_pow] at hyn'
  have hy0 : res₁ R K w c.y = 0 := (pow_eq_zero_iff'.mp hyn').1
  rw [res₁_apply] at hy0
  exact c.nodeResidue₁_y_ne_zero hy0

end BranchKer

section Loc

variable (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
  (ϖ : ↥(NodeLocalized.coeffSubring A K))

private theorem nodeConst_ne_zero
    (hy : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x}) (hx : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u) :
    R.nodeConst K w ϖ ≠ 0 := by
  intro h0
  rw [h0, zero_pow (by omega), zero_mul] at hxy
  rcases mul_eq_zero.mp hxy with hx0 | hy0
  · exact hx (hx0 ▸ zero_mem _)
  · exact hy (hy0 ▸ zero_mem _)

private theorem loc_injective [hpr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime] :
    Function.Injective (algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x}))) :=
  IsLocalization.injective _ (le_nonZeroDivisors_of_noZeroDivisors (fun h => hpr.ne_top
    ((Ideal.eq_top_iff_one _).mpr (by
      have : (0 : ↥(R.nodeIntegersOver K w)) ∈ (Ideal.span {R.nodeConst K w ϖ, c.x}).primeCompl := h
      exact absurd (zero_mem _) this))))

private theorem loc_x_mem_span [(Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime]
    (hy : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u) :
    algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) c.x ∈
      Ideal.span {algebraMap ↥(R.nodeIntegersOver K w)
        (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) (R.nodeConst K w ϖ)} := by
  let alg := algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x}))
  have hyu : IsUnit (alg c.y) :=
    IsLocalization.map_units (M := (Ideal.span {R.nodeConst K w ϖ, c.x}).primeCompl) _ ⟨c.y, hy⟩
  obtain ⟨yi, hyi⟩ := hyu.exists_right_inv
  have hprod : alg c.x * alg c.y = alg (R.nodeConst K w ϖ ^ E * u) :=
    (map_mul alg c.x c.y).symm.trans (congrArg alg hxy)
  have e1 : R.nodeConst K w ϖ ^ E * u = R.nodeConst K w ϖ * (R.nodeConst K w ϖ ^ (E - 1) * u) := by
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hE]
  have hchain : alg c.x = (alg (R.nodeConst K w ϖ ^ (E - 1) * u) * yi) * alg (R.nodeConst K w ϖ) :=
    calc alg c.x = alg c.x * 1 := (mul_one _).symm
      _ = alg c.x * (alg c.y * yi) := congrArg (alg c.x * ·) hyi.symm
      _ = (alg c.x * alg c.y) * yi := (mul_assoc _ _ _).symm
      _ = alg (R.nodeConst K w ϖ ^ E * u) * yi := congrArg (· * yi) hprod
      _ = alg (R.nodeConst K w ϖ * (R.nodeConst K w ϖ ^ (E - 1) * u)) * yi := congrArg (fun t => alg t * yi) e1
      _ = (alg (R.nodeConst K w ϖ) * alg (R.nodeConst K w ϖ ^ (E - 1) * u)) * yi :=
          congrArg (· * yi) (map_mul alg _ _)
      _ = alg (R.nodeConst K w ϖ) * (alg (R.nodeConst K w ϖ ^ (E - 1) * u) * yi) := mul_assoc _ _ _
      _ = (alg (R.nodeConst K w ϖ ^ (E - 1) * u) * yi) * alg (R.nodeConst K w ϖ) := mul_comm _ _
  exact Ideal.mem_span_singleton'.mpr ⟨_, hchain.symm⟩

private theorem loc_maximalIdeal_eq [(Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime]
    (hy : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u) :
    maximalIdeal (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) =
      Ideal.span {algebraMap ↥(R.nodeIntegersOver K w)
        (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) (R.nodeConst K w ϖ)} := by
  have hxmem := loc_x_mem_span R K w c ϖ hy E hE u hxy
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with rfl | rfl
    · exact Ideal.subset_span rfl
    · exact hxmem
  · exact Ideal.span_mono (fun o ho => ⟨R.nodeConst K w ϖ, Set.mem_insert _ _, (Set.mem_singleton_iff.mp ho).symm⟩)

private theorem loc_isDiscreteValuationRing [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    [hpr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime]
    (hy : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x}) (hx : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u) :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) := by
  let O := Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})
  let alg := algebraMap ↥(R.nodeIntegersOver K w) O
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing (Ideal.span {R.nodeConst K w ϖ, c.x}).primeCompl O
    inferInstance
  haveI : IsDomain O := IsLocalization.isDomain_localization
    (le_nonZeroDivisors_of_noZeroDivisors (fun h => by
      have : (0 : ↥(R.nodeIntegersOver K w)) ∈ (Ideal.span {R.nodeConst K w ϖ, c.x}).primeCompl := h
      exact absurd (zero_mem _) this))
  have hmaxO := loc_maximalIdeal_eq R K w c ϖ hy E hE u hxy
  have hϖO0 : alg (R.nodeConst K w ϖ) ≠ 0 := fun h =>
    nodeConst_ne_zero R K w c ϖ hy hx E hE u hxy ((loc_injective R K w c ϖ) (h.trans (map_zero alg).symm))
  have hϖOmem : alg (R.nodeConst K w ϖ) ∈ maximalIdeal O := by rw [hmaxO]; exact Ideal.subset_span rfl
  have hnotfield : ¬ IsField O := by
    intro hF
    have := (IsLocalRing.isField_iff_maximalIdeal_eq (R := O)).mp hF
    rw [this] at hϖOmem
    exact hϖO0 ((Ideal.mem_bot).mp hϖOmem)
  have hP : (maximalIdeal O).IsPrincipal := ⟨⟨alg (R.nodeConst K w ϖ), hmaxO⟩⟩
  exact ((IsDiscreteValuationRing.TFAE O hnotfield).out 0 4).mpr hP

private theorem loc_irreducible [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    [hpr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime]
    (hy : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x}) (hx : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u) :
    Irreducible (algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) (R.nodeConst K w ϖ)) := by
  haveI := loc_isDiscreteValuationRing R K w c ϖ hy hx E hE u hxy
  have hϖO0 : algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) (R.nodeConst K w ϖ) ≠ 0 := fun h =>
    nodeConst_ne_zero R K w c ϖ hy hx E hE u hxy ((loc_injective R K w c ϖ) (h.trans (map_zero _).symm))
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hϖO0
    (loc_maximalIdeal_eq R K w c ϖ hy E hE u hxy)

private theorem exists_surj_of_unit [hpr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime]
    (wu : (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x}))ˣ) :
    ∃ p : ↥(R.nodeIntegersOver K w) × ↥(Ideal.span {R.nodeConst K w ϖ, c.x}).primeCompl,
      (wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) *
          algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) p.2 =
        algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) p.1 ∧
      p.1 ∉ Ideal.span {R.nodeConst K w ϖ, c.x} := by
  obtain ⟨p, hp⟩ := IsLocalization.surj (Ideal.span {R.nodeConst K w ϖ, c.x}).primeCompl
    (wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x}))
  refine ⟨p, hp, fun ht => ?_⟩
  have htunit : IsUnit (algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) p.1) := by
    rw [← hp]
    exact (Units.isUnit wu).mul (IsLocalization.map_units (M := (Ideal.span {R.nodeConst K w ϖ, c.x}).primeCompl) _ p.2)
  have hmem := (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) (Ideal.span {R.nodeConst K w ϖ, c.x}) p.1).mpr ht
  exact (mem_maximalIdeal _).mp hmem htunit

private theorem exists_mul_eq_of_eq_unit_mul_pow [hpr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime]
    (b : ↥(R.nodeIntegersOver K w)) (m : ℕ)
    (wu : (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x}))ˣ)
    (hbw : algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) b =
      (wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) *
        algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x}))
          (R.nodeConst K w ϖ) ^ m) :
    ∃ (s t : ↥(R.nodeIntegersOver K w)),
      s ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ t ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧
      b * s = R.nodeConst K w ϖ ^ m * t := by
  let alg := algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x}))
  obtain ⟨p, hp, htmem⟩ := exists_surj_of_unit R K w c ϖ wu
  refine ⟨p.2, p.1, p.2.2, htmem, loc_injective R K w c ϖ ?_⟩
  have e2 : alg (R.nodeConst K w ϖ ^ m * p.1) = alg (R.nodeConst K w ϖ) ^ m * alg p.1 :=
    (map_mul alg _ _).trans (congrArg (· * alg p.1) (map_pow alg _ m))
  calc alg (b * p.2) = alg b * alg p.2 := map_mul alg b p.2
    _ = ((wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) * alg (R.nodeConst K w ϖ) ^ m) * alg p.2 :=
        congrArg (· * alg p.2) hbw
    _ = ((wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) * alg p.2) * alg (R.nodeConst K w ϖ) ^ m :=
        mul_right_comm _ _ _
    _ = alg p.1 * alg (R.nodeConst K w ϖ) ^ m := congrArg (· * alg (R.nodeConst K w ϖ) ^ m) hp
    _ = alg (R.nodeConst K w ϖ) ^ m * alg p.1 := mul_comm _ _
    _ = alg (R.nodeConst K w ϖ ^ m * p.1) := e2.symm

private theorem _root_.AnnulusLocBranch.exists_mul_eq_pow_mul [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hpr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime) (hy : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x})
    (hx : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (b : ↥(R.nodeIntegersOver K w)) (hb : b ≠ 0) :
    ∃ (m : ℕ) (s t : ↥(R.nodeIntegersOver K w)),
      s ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ t ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧
      b * s = R.nodeConst K w ϖ ^ m * t := by
  haveI := hpr
  haveI := loc_isDiscreteValuationRing R K w c ϖ hy hx E hE u hxy
  have hirr := loc_irreducible R K w c ϖ hy hx E hE u hxy
  have hbO : algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.x})) b ≠ 0 := fun h =>
    hb ((loc_injective R K w c ϖ) (h.trans (map_zero _).symm))
  obtain ⟨m, wu, hbw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hbO hirr
  obtain ⟨s, t, hs, ht, hst⟩ := exists_mul_eq_of_eq_unit_mul_pow R K w c ϖ b m wu hbw
  exact ⟨m, s, t, hs, ht, hst⟩

p2m_export "AnnulusLocBranch" "exists_mul_eq_pow_mul"
private theorem cross_identity (a b sa ta sb tb ϖB : ↥(R.nodeIntegersOver K w)) (ma mb : ℕ) (z : ↥(modularFunctionFieldBar (N * q)))
    (hzab : z * (b : ↥(modularFunctionFieldBar (N * q))) = a)
    (hfa : a * sa = ϖB ^ ma * ta) (hfb : b * sb = ϖB ^ mb * tb) :
    z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) =
      (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q))) := by
  have h1 : (b : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q))) = (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (tb : ↥(modularFunctionFieldBar (N * q))) := by
    have := congrArg (fun v : ↥(R.nodeIntegersOver K w) => (v : ↥(modularFunctionFieldBar (N * q)))) hfb
    simpa using this
  have h2 : (a : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) = (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ta : ↥(modularFunctionFieldBar (N * q))) := by
    have := congrArg (fun v : ↥(R.nodeIntegersOver K w) => (v : ↥(modularFunctionFieldBar (N * q)))) hfa
    simpa using this
  calc z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * ↑tb * ↑sa = z * (↑b * ↑sb) * ↑sa := by rw [h1]; ring
    _ = (↑a * ↑sa) * ↑sb := by rw [← hzab]; ring
    _ = _ := by rw [h2]

private theorem good_case (ta sb tb sa ϖB : ↥(R.nodeIntegersOver K w)) (ma mb : ℕ) (hle : mb ≤ ma) (z : ↥(modularFunctionFieldBar (N * q)))
    (hϖ0 : (ϖB : ↥(modularFunctionFieldBar (N * q))) ≠ 0)
    (key : z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) =
      (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q)))) :
    z * ((tb * sa : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = ((ϖB ^ (ma - mb) * ta * sb : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) := by
  have hpow : (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma = (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (ma - mb) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  have hmul : (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (z * ((tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))))) =
      (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * ((ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (ma - mb) * (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q)))) := by
    linear_combination key + ((ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q)))) * hpow
  have hfin := mul_left_cancel₀ (pow_ne_zero _ hϖ0) hmul
  push_cast
  exact hfin

private theorem bad_case {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (val : Valuation ↥(modularFunctionFieldBar (N * q)) Γ)
    (ta sb tb sa ϖB : ↥(R.nodeIntegersOver K w)) (ma mb : ℕ) (hlt : ma < mb) (z : ↥(modularFunctionFieldBar (N * q)))
    (hϖ0 : (ϖB : ↥(modularFunctionFieldBar (N * q))) ≠ 0) (hϖlt : val (ϖB : ↥(modularFunctionFieldBar (N * q))) < 1) (hz : val z ≤ 1)
    (hta : val (ta : ↥(modularFunctionFieldBar (N * q))) = 1) (hsb : val (sb : ↥(modularFunctionFieldBar (N * q))) = 1)
    (htb : val (tb : ↥(modularFunctionFieldBar (N * q))) = 1) (hsa : val (sa : ↥(modularFunctionFieldBar (N * q))) = 1)
    (key : z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) =
      (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q)))) : False := by
  have hpow : (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb = (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) := by
    rw [← pow_add, Nat.add_sub_cancel' hlt.le]
  have key2 : z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) = (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q))) := by
    apply mul_left_cancel₀ (pow_ne_zero ma hϖ0)
    linear_combination key - (z * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q)))) * hpow
  have hv := congrArg val key2
  rw [map_mul, map_mul, map_mul, map_pow, map_mul, hta, hsb, htb, hsa, mul_one, mul_one, mul_one] at hv
  have hpk : val (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) < 1 := pow_lt_one₀ zero_le' hϖlt (by omega)
  have hle1 : val z * val (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) ≤
      val (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) := by
    have := mul_le_mul_left hz (val (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma))
    rwa [one_mul] at this
  rw [hv] at hle1
  exact absurd (lt_of_le_of_lt hle1 hpk) (lt_irrefl _)

private theorem exists_mul_eq_of_mem_integers [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (a b : ↥(R.nodeIntegersOver K w)) (hb : b ≠ 0)
    (z : ↥(modularFunctionFieldBar (N * q))) (hz : z ∈ R.R₁.integers)
    (hzab : z * (b : ↥(modularFunctionFieldBar (N * q))) = a) :
    ∃ a' b' : ↥(R.nodeIntegersOver K w), R.nodeResidue₁ w ⟨b', b'.2.1⟩ ≠ 0 ∧ z * (b' : ↥(modularFunctionFieldBar (N * q))) = a' := by
  classical
  have hker := ker_res₁_eq R K w c ϖ hϖ hmax hbr.1 hbr.2.2.1
  have hres_of_notmem : ∀ v : ↥(R.nodeIntegersOver K w), v ∉ Ideal.span {R.nodeConst K w ϖ, c.x} → res₁ R K w v ≠ 0 := by
    intro v hv h0
    exact hv (by rw [← hker]; exact h0)
  by_cases ha : a = 0
  · refine ⟨0, 1, ?_, ?_⟩
    · have : res₁ R K w 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
      exact this
    · have hb' : (b : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h => hb (Subtype.ext h)
      have hz0 : z = 0 := by
        have : z * (b : ↥(modularFunctionFieldBar (N * q))) = 0 := by rw [hzab, ha]; rfl
        exact (mul_eq_zero.mp this).resolve_right hb'
      rw [hz0, zero_mul]; rfl
  obtain ⟨ma, sa, ta, hsa, hta, hfa⟩ :=
    exists_mul_eq_pow_mul R K w c ϖ hbr.1 hbr.2.2.1 hbr.2.2.2 E hE u hu hxy a ha
  obtain ⟨mb, sb, tb, hsb, htb, hfb⟩ :=
    exists_mul_eq_pow_mul R K w c ϖ hbr.1 hbr.2.2.1 hbr.2.2.2 E hE u hu hxy b hb
  have hϖB0 := nodeConst_ne_zero R K w c ϖ hbr.2.2.1 hbr.2.2.2 E hE u hxy
  have hϖF0 : ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h0 => hϖB0 (Subtype.ext h0)
  have key := cross_identity R K w a b sa ta sb tb (R.nodeConst K w ϖ) ma mb z hzab hfa hfb
  rcases le_or_gt mb ma with hle | hlt
  · refine ⟨R.nodeConst K w ϖ ^ (ma - mb) * ta * sb, tb * sa, ?_,
      good_case R K w ta sb tb sa (R.nodeConst K w ϖ) ma mb hle z hϖF0 key⟩
    have : res₁ R K w (tb * sa) ≠ 0 := by
      rw [map_mul]
      exact mul_ne_zero (hres_of_notmem tb htb) (hres_of_notmem sa hsa)
    exact this
  · exact (bad_case R K w R.R₁.integers.valuation ta sb tb sa (R.nodeConst K w ϖ) ma mb hlt z hϖF0
      (valuation_nodeConst_lt_one R K w ϖ hϖ)
      ((ValuationSubring.valuation_le_one_iff R.R₁.integers z).mpr hz)
      (valuation_eq_one_of_res₁_ne_zero R K w ta (hres_of_notmem ta hta))
      (valuation_eq_one_of_res₁_ne_zero R K w sb (hres_of_notmem sb hsb))
      (valuation_eq_one_of_res₁_ne_zero R K w tb (hres_of_notmem tb htb))
      (valuation_eq_one_of_res₁_ne_zero R K w sa (hres_of_notmem sa hsa)) key).elim

end Loc

end AnnulusLocBranch

namespace AnnulusLocBranchSnd

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private noncomputable def res₂ (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) :
    ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
  (R.nodeResidue₂ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))

private theorem res₂_apply (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (b : ↥(R.nodeIntegersOver K w)) :
    res₂ R K w b = R.nodeResidue₂ w ⟨b, b.2.1⟩ := rfl

private def toR₂ (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) : ↥(R.nodeIntegersOver K w) →+* ↥R.R₂.integers where
  toFun v := ⟨v, v.2.1.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem res₂_eq (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (v : ↥(R.nodeIntegersOver K w)) :
    res₂ R K w v = R.ι (R.R₂.residue (toR₂ R K w v)) := rfl

private theorem coe_toR₂ (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (v : ↥(R.nodeIntegersOver K w)) :
    ((toR₂ R K w v : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) = v := rfl

private theorem not_isUnit_toR₂_nodeConst (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    ¬ IsUnit (toR₂ R K w (R.nodeConst K w ϖ)) := by
  set a : A := ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ with ha
  have hred : red a = 0 := hϖ
  have hanu : ¬ IsUnit a := fun hu => by
    have := hu.map red
    rw [hred] at this
    exact not_isUnit_zero this
  have hfval : ((toR₂ R K w (R.nodeConst K w ϖ) : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := rfl
  intro hu
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have hg' : ((toR₂ R K w (R.nodeConst K w ϖ) : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) *
      (g : ↥(modularFunctionFieldBar (N * q))) = 1 := by
    rw [← MulMemClass.coe_mul, hg]; rfl
  have ha0 : (a : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    rw [hfval, h0, map_zero, zero_mul] at hg'
    exact zero_ne_one hg'
  have hginv : (g : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ ((a : AlgebraicClosure ℚ)⁻¹) := by
    rw [map_inv₀, ← hfval]
    exact (eq_inv_of_mul_eq_one_right hg')
  have hmemA : (a : AlgebraicClosure ℚ)⁻¹ ∈ A := by
    have := g.2
    rw [hginv] at this
    exact (R.R₂.algebraMap_mem_iff _).mp this
  exact hanu (isUnit_iff_exists_inv.mpr ⟨⟨(a : AlgebraicClosure ℚ)⁻¹, hmemA⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩)

private theorem res₂_nodeConst_eq_zero (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    res₂ R K w (R.nodeConst K w ϖ) = 0 := by
  rw [res₂_apply, nodeResidue₂_apply, residue₂_apply]
  set a : A := ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ with ha
  have hred : red a = 0 := hϖ
  have hanu : ¬ IsUnit a := fun hu => by
    have := hu.map red
    rw [hred] at this
    exact not_isUnit_zero this
  set f : ↥R.R₂.integers := ⟨((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))),
      (R.nodeConst K w ϖ).2.1.2.1⟩ with hf
  have hfval : (f : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := rfl
  have hfnu : ¬ IsUnit f := by
    intro hu
    obtain ⟨g, hg⟩ := hu.exists_right_inv
    have hg' : (f : ↥(modularFunctionFieldBar (N * q))) * (g : ↥(modularFunctionFieldBar (N * q))) = 1 := by
      rw [← MulMemClass.coe_mul, hg]; rfl
    have ha0 : (a : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      rw [hfval, h0, map_zero, zero_mul] at hg'
      exact zero_ne_one hg'
    have hginv : (g : ↥(modularFunctionFieldBar (N * q))) =
        algebraMap (AlgebraicClosure ℚ) _ ((a : AlgebraicClosure ℚ)⁻¹) := by
      rw [map_inv₀, ← hfval]
      exact (eq_inv_of_mul_eq_one_right hg')
    have hmemA : (a : AlgebraicClosure ℚ)⁻¹ ∈ A := by
      have := g.2
      rw [hginv] at this
      exact (R.R₂.algebraMap_mem_iff _).mp this
    apply hanu
    exact isUnit_iff_exists_inv.mpr ⟨⟨(a : AlgebraicClosure ℚ)⁻¹, hmemA⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
  have hmem : f ∈ maximalIdeal ↥R.R₂.integers := (mem_maximalIdeal _).mpr hfnu
  rw [← R.R₂.ker_residue, RingHom.mem_ker] at hmem
  show R.ι (R.R₂.residue f) = 0
  rw [hmem, map_zero]

private theorem valuation_nodeConst_lt_one (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    R.R₂.integers.valuation ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) < 1 := by
  have hmem : toR₂ R K w (R.nodeConst K w ϖ) ∈ maximalIdeal ↥R.R₂.integers :=
    (mem_maximalIdeal _).mpr (not_isUnit_toR₂_nodeConst R K w ϖ hϖ)
  exact (ValuationSubring.valuation_lt_one_iff _ _).mp hmem

private theorem valuation_eq_one_of_res₂_ne_zero (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (v : ↥(R.nodeIntegersOver K w)) (h : res₂ R K w v ≠ 0) :
    R.R₂.integers.valuation (v : ↥(modularFunctionFieldBar (N * q))) = 1 := by
  have h1 : IsUnit (toR₂ R K w v) := by
    apply R.R₂.isUnit_of_residue_ne_zero
    intro h0
    exact h (by rw [res₂_eq, h0, map_zero])
  exact (ValuationSubring.valuation_eq_one_iff _ _).mp h1

section BranchKer

variable (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
  (ϖ : ↥(NodeLocalized.coeffSubring A K))

private theorem span_le_ker (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    Ideal.span {R.nodeConst K w ϖ, c.y} ≤ RingHom.ker (res₂ R K w) := by
  rw [Ideal.span_le]
  rintro z (rfl | rfl)
  · exact res₂_nodeConst_eq_zero R K w ϖ hϖ
  · show res₂ R K w c.y = 0
    rw [res₂_apply]
    exact c.y_snd

private theorem ker_res₂_eq [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.y, c.x}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.y, c.x})
    (hpr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime) (hy : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y}) :
    RingHom.ker (res₂ R K w) = Ideal.span {R.nodeConst K w ϖ, c.y} := by
  classical
  set 𝔮 : Ideal ↥(R.nodeIntegersOver K w) := Ideal.span {R.nodeConst K w ϖ, c.y} with h𝔮
  haveI : 𝔮.IsPrime := hpr
  haveI hloc : IsLocalRing ↥(R.nodeIntegersOver K w) := IsLocalRing.of_unique_max_ideal ⟨_, hmax.1, hmax.2⟩
  have hmaxB : maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.y, c.x} :=
    hmax.2 _ (maximalIdeal.isMaximal _)
  refine le_antisymm ?_ (span_le_ker R K w c ϖ hϖ)

  set Q := ↥(R.nodeIntegersOver K w) ⧸ 𝔮
  set mkq : ↥(R.nodeIntegersOver K w) →+* Q := Ideal.Quotient.mk 𝔮
  haveI : IsDomain Q := Ideal.Quotient.isDomain 𝔮
  haveI : Nontrivial Q := inferInstance
  haveI : IsLocalRing Q := IsLocalRing.of_surjective' mkq Ideal.Quotient.mk_surjective
  have hybar_ne : mkq c.x ≠ 0 := fun h => hy (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hmaxQ : maximalIdeal Q = Ideal.span {mkq c.x} := by

    have hcomap : (maximalIdeal Q).comap mkq = maximalIdeal ↥(R.nodeIntegersOver K w) := by
      have := Ideal.comap_isMaximal_of_surjective mkq Ideal.Quotient.mk_surjective (K := maximalIdeal Q)
      exact (hmax.2 _ this).trans hmaxB.symm
    have hmap : maximalIdeal Q = (maximalIdeal ↥(R.nodeIntegersOver K w)).map mkq := by
      rw [← hcomap, Ideal.map_comap_of_surjective mkq Ideal.Quotient.mk_surjective]
    rw [hmap, hmaxB, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨z, hz, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · have : mkq (R.nodeConst K w ϖ) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
        rw [this]; exact zero_mem _
      · have : mkq c.y = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        rw [this]; exact zero_mem _
      · exact Ideal.subset_span rfl
    · exact Ideal.span_mono (Set.singleton_subset_iff.mpr
        ⟨c.x, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)), rfl⟩)
  have hnotfield : ¬ IsField Q := by
    intro hF
    have := (IsLocalRing.isField_iff_maximalIdeal_eq (R := Q)).mp hF
    rw [hmaxQ, Ideal.span_singleton_eq_bot] at this
    exact hybar_ne this
  have hP : (maximalIdeal Q).IsPrincipal := ⟨⟨mkq c.x, hmaxQ⟩⟩
  haveI : IsDiscreteValuationRing Q := ((IsDiscreteValuationRing.TFAE Q hnotfield).out 0 4).mpr hP
  have hirr : Irreducible (mkq c.x) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (mkq c.x) hybar_ne hmaxQ

  intro s hs
  by_contra hsnot
  have hI : (RingHom.ker (res₂ R K w)).map mkq ≠ ⊥ := by
    intro hbot
    apply hsnot
    have : mkq s ∈ (RingHom.ker (res₂ R K w)).map mkq := Ideal.mem_map_of_mem _ hs
    rw [hbot, Ideal.mem_bot] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hirr
  have hyn : mkq c.x ^ n ∈ (RingHom.ker (res₂ R K w)).map mkq := by rw [hn]; exact Ideal.subset_span rfl
  rw [← map_pow, Ideal.mem_map_iff_of_surjective mkq Ideal.Quotient.mk_surjective] at hyn
  obtain ⟨t, ht, hty⟩ := hyn

  have hdiff : c.x ^ n - t ∈ 𝔮 := by
    rw [← Ideal.Quotient.eq, hty]
  have hyn' : c.x ^ n ∈ RingHom.ker (res₂ R K w) := by
    have := add_mem (span_le_ker R K w c ϖ hϖ hdiff) ht
    rwa [sub_add_cancel] at this
  rw [RingHom.mem_ker, map_pow] at hyn'
  have hy0 : res₂ R K w c.x = 0 := (pow_eq_zero_iff'.mp hyn').1
  rw [res₂_apply] at hy0
  exact c.nodeResidue₂_x_ne_zero hy0

end BranchKer

section Loc

variable (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
  (ϖ : ↥(NodeLocalized.coeffSubring A K))

private theorem nodeConst_ne_zero
    (hy : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y}) (hx : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.y * c.x = R.nodeConst K w ϖ ^ E * u) :
    R.nodeConst K w ϖ ≠ 0 := by
  intro h0
  rw [h0, zero_pow (by omega), zero_mul] at hxy
  rcases mul_eq_zero.mp hxy with hx0 | hy0
  · exact hx (hx0 ▸ zero_mem _)
  · exact hy (hy0 ▸ zero_mem _)

private theorem loc_injective [hpr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime] :
    Function.Injective (algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y}))) :=
  IsLocalization.injective _ (le_nonZeroDivisors_of_noZeroDivisors (fun h => hpr.ne_top
    ((Ideal.eq_top_iff_one _).mpr (by
      have : (0 : ↥(R.nodeIntegersOver K w)) ∈ (Ideal.span {R.nodeConst K w ϖ, c.y}).primeCompl := h
      exact absurd (zero_mem _) this))))

private theorem loc_x_mem_span [(Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime]
    (hy : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.y * c.x = R.nodeConst K w ϖ ^ E * u) :
    algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) c.y ∈
      Ideal.span {algebraMap ↥(R.nodeIntegersOver K w)
        (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) (R.nodeConst K w ϖ)} := by
  let alg := algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y}))
  have hyu : IsUnit (alg c.x) :=
    IsLocalization.map_units (M := (Ideal.span {R.nodeConst K w ϖ, c.y}).primeCompl) _ ⟨c.x, hy⟩
  obtain ⟨yi, hyi⟩ := hyu.exists_right_inv
  have hprod : alg c.y * alg c.x = alg (R.nodeConst K w ϖ ^ E * u) :=
    (map_mul alg c.y c.x).symm.trans (congrArg alg hxy)
  have e1 : R.nodeConst K w ϖ ^ E * u = R.nodeConst K w ϖ * (R.nodeConst K w ϖ ^ (E - 1) * u) := by
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hE]
  have hchain : alg c.y = (alg (R.nodeConst K w ϖ ^ (E - 1) * u) * yi) * alg (R.nodeConst K w ϖ) :=
    calc alg c.y = alg c.y * 1 := (mul_one _).symm
      _ = alg c.y * (alg c.x * yi) := congrArg (alg c.y * ·) hyi.symm
      _ = (alg c.y * alg c.x) * yi := (mul_assoc _ _ _).symm
      _ = alg (R.nodeConst K w ϖ ^ E * u) * yi := congrArg (· * yi) hprod
      _ = alg (R.nodeConst K w ϖ * (R.nodeConst K w ϖ ^ (E - 1) * u)) * yi := congrArg (fun t => alg t * yi) e1
      _ = (alg (R.nodeConst K w ϖ) * alg (R.nodeConst K w ϖ ^ (E - 1) * u)) * yi :=
          congrArg (· * yi) (map_mul alg _ _)
      _ = alg (R.nodeConst K w ϖ) * (alg (R.nodeConst K w ϖ ^ (E - 1) * u) * yi) := mul_assoc _ _ _
      _ = (alg (R.nodeConst K w ϖ ^ (E - 1) * u) * yi) * alg (R.nodeConst K w ϖ) := mul_comm _ _
  exact Ideal.mem_span_singleton'.mpr ⟨_, hchain.symm⟩

private theorem loc_maximalIdeal_eq [(Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime]
    (hy : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.y * c.x = R.nodeConst K w ϖ ^ E * u) :
    maximalIdeal (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) =
      Ideal.span {algebraMap ↥(R.nodeIntegersOver K w)
        (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) (R.nodeConst K w ϖ)} := by
  have hxmem := loc_x_mem_span R K w c ϖ hy E hE u hxy
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with rfl | rfl
    · exact Ideal.subset_span rfl
    · exact hxmem
  · exact Ideal.span_mono (fun o ho => ⟨R.nodeConst K w ϖ, Set.mem_insert _ _, (Set.mem_singleton_iff.mp ho).symm⟩)

private theorem loc_isDiscreteValuationRing [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    [hpr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime]
    (hy : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y}) (hx : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.y * c.x = R.nodeConst K w ϖ ^ E * u) :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) := by
  let O := Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})
  let alg := algebraMap ↥(R.nodeIntegersOver K w) O
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing (Ideal.span {R.nodeConst K w ϖ, c.y}).primeCompl O
    inferInstance
  haveI : IsDomain O := IsLocalization.isDomain_localization
    (le_nonZeroDivisors_of_noZeroDivisors (fun h => by
      have : (0 : ↥(R.nodeIntegersOver K w)) ∈ (Ideal.span {R.nodeConst K w ϖ, c.y}).primeCompl := h
      exact absurd (zero_mem _) this))
  have hmaxO := loc_maximalIdeal_eq R K w c ϖ hy E hE u hxy
  have hϖO0 : alg (R.nodeConst K w ϖ) ≠ 0 := fun h =>
    nodeConst_ne_zero R K w c ϖ hy hx E hE u hxy ((loc_injective R K w c ϖ) (h.trans (map_zero alg).symm))
  have hϖOmem : alg (R.nodeConst K w ϖ) ∈ maximalIdeal O := by rw [hmaxO]; exact Ideal.subset_span rfl
  have hnotfield : ¬ IsField O := by
    intro hF
    have := (IsLocalRing.isField_iff_maximalIdeal_eq (R := O)).mp hF
    rw [this] at hϖOmem
    exact hϖO0 ((Ideal.mem_bot).mp hϖOmem)
  have hP : (maximalIdeal O).IsPrincipal := ⟨⟨alg (R.nodeConst K w ϖ), hmaxO⟩⟩
  exact ((IsDiscreteValuationRing.TFAE O hnotfield).out 0 4).mpr hP

private theorem loc_irreducible [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    [hpr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime]
    (hy : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y}) (hx : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hxy : c.y * c.x = R.nodeConst K w ϖ ^ E * u) :
    Irreducible (algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) (R.nodeConst K w ϖ)) := by
  haveI := loc_isDiscreteValuationRing R K w c ϖ hy hx E hE u hxy
  have hϖO0 : algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) (R.nodeConst K w ϖ) ≠ 0 := fun h =>
    nodeConst_ne_zero R K w c ϖ hy hx E hE u hxy ((loc_injective R K w c ϖ) (h.trans (map_zero _).symm))
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hϖO0
    (loc_maximalIdeal_eq R K w c ϖ hy E hE u hxy)

private theorem exists_surj_of_unit [hpr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime]
    (wu : (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y}))ˣ) :
    ∃ p : ↥(R.nodeIntegersOver K w) × ↥(Ideal.span {R.nodeConst K w ϖ, c.y}).primeCompl,
      (wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) *
          algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) p.2 =
        algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) p.1 ∧
      p.1 ∉ Ideal.span {R.nodeConst K w ϖ, c.y} := by
  obtain ⟨p, hp⟩ := IsLocalization.surj (Ideal.span {R.nodeConst K w ϖ, c.y}).primeCompl
    (wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y}))
  refine ⟨p, hp, fun ht => ?_⟩
  have htunit : IsUnit (algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) p.1) := by
    rw [← hp]
    exact (Units.isUnit wu).mul (IsLocalization.map_units (M := (Ideal.span {R.nodeConst K w ϖ, c.y}).primeCompl) _ p.2)
  have hmem := (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) (Ideal.span {R.nodeConst K w ϖ, c.y}) p.1).mpr ht
  exact (mem_maximalIdeal _).mp hmem htunit

private theorem exists_mul_eq_of_eq_unit_mul_pow [hpr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime]
    (b : ↥(R.nodeIntegersOver K w)) (m : ℕ)
    (wu : (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y}))ˣ)
    (hbw : algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) b =
      (wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) *
        algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y}))
          (R.nodeConst K w ϖ) ^ m) :
    ∃ (s t : ↥(R.nodeIntegersOver K w)),
      s ∉ Ideal.span {R.nodeConst K w ϖ, c.y} ∧ t ∉ Ideal.span {R.nodeConst K w ϖ, c.y} ∧
      b * s = R.nodeConst K w ϖ ^ m * t := by
  let alg := algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y}))
  obtain ⟨p, hp, htmem⟩ := exists_surj_of_unit R K w c ϖ wu
  refine ⟨p.2, p.1, p.2.2, htmem, loc_injective R K w c ϖ ?_⟩
  have e2 : alg (R.nodeConst K w ϖ ^ m * p.1) = alg (R.nodeConst K w ϖ) ^ m * alg p.1 :=
    (map_mul alg _ _).trans (congrArg (· * alg p.1) (map_pow alg _ m))
  calc alg (b * p.2) = alg b * alg p.2 := map_mul alg b p.2
    _ = ((wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) * alg (R.nodeConst K w ϖ) ^ m) * alg p.2 :=
        congrArg (· * alg p.2) hbw
    _ = ((wu : Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) * alg p.2) * alg (R.nodeConst K w ϖ) ^ m :=
        mul_right_comm _ _ _
    _ = alg p.1 * alg (R.nodeConst K w ϖ) ^ m := congrArg (· * alg (R.nodeConst K w ϖ) ^ m) hp
    _ = alg (R.nodeConst K w ϖ) ^ m * alg p.1 := mul_comm _ _
    _ = alg (R.nodeConst K w ϖ ^ m * p.1) := e2.symm

private theorem _root_.AnnulusLocBranchSnd.exists_mul_eq_pow_mul [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hpr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime) (hy : c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hx : c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.y * c.x = R.nodeConst K w ϖ ^ E * u)
    (b : ↥(R.nodeIntegersOver K w)) (hb : b ≠ 0) :
    ∃ (m : ℕ) (s t : ↥(R.nodeIntegersOver K w)),
      s ∉ Ideal.span {R.nodeConst K w ϖ, c.y} ∧ t ∉ Ideal.span {R.nodeConst K w ϖ, c.y} ∧
      b * s = R.nodeConst K w ϖ ^ m * t := by
  haveI := hpr
  haveI := loc_isDiscreteValuationRing R K w c ϖ hy hx E hE u hxy
  have hirr := loc_irreducible R K w c ϖ hy hx E hE u hxy
  have hbO : algebraMap ↥(R.nodeIntegersOver K w)
      (Localization.AtPrime (Ideal.span {R.nodeConst K w ϖ, c.y})) b ≠ 0 := fun h =>
    hb ((loc_injective R K w c ϖ) (h.trans (map_zero _).symm))
  obtain ⟨m, wu, hbw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hbO hirr
  obtain ⟨s, t, hs, ht, hst⟩ := exists_mul_eq_of_eq_unit_mul_pow R K w c ϖ b m wu hbw
  exact ⟨m, s, t, hs, ht, hst⟩

p2m_export "AnnulusLocBranchSnd" "exists_mul_eq_pow_mul"
private theorem cross_identity (a b sa ta sb tb ϖB : ↥(R.nodeIntegersOver K w)) (ma mb : ℕ) (z : ↥(modularFunctionFieldBar (N * q)))
    (hzab : z * (b : ↥(modularFunctionFieldBar (N * q))) = a)
    (hfa : a * sa = ϖB ^ ma * ta) (hfb : b * sb = ϖB ^ mb * tb) :
    z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) =
      (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q))) := by
  have h1 : (b : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q))) = (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (tb : ↥(modularFunctionFieldBar (N * q))) := by
    have := congrArg (fun v : ↥(R.nodeIntegersOver K w) => (v : ↥(modularFunctionFieldBar (N * q)))) hfb
    simpa using this
  have h2 : (a : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) = (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ta : ↥(modularFunctionFieldBar (N * q))) := by
    have := congrArg (fun v : ↥(R.nodeIntegersOver K w) => (v : ↥(modularFunctionFieldBar (N * q)))) hfa
    simpa using this
  calc z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * ↑tb * ↑sa = z * (↑b * ↑sb) * ↑sa := by rw [h1]; ring
    _ = (↑a * ↑sa) * ↑sb := by rw [← hzab]; ring
    _ = _ := by rw [h2]

private theorem good_case (ta sb tb sa ϖB : ↥(R.nodeIntegersOver K w)) (ma mb : ℕ) (hle : mb ≤ ma) (z : ↥(modularFunctionFieldBar (N * q)))
    (hϖ0 : (ϖB : ↥(modularFunctionFieldBar (N * q))) ≠ 0)
    (key : z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) =
      (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q)))) :
    z * ((tb * sa : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = ((ϖB ^ (ma - mb) * ta * sb : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) := by
  have hpow : (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma = (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (ma - mb) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  have hmul : (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (z * ((tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))))) =
      (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * ((ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (ma - mb) * (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q)))) := by
    linear_combination key + ((ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q)))) * hpow
  have hfin := mul_left_cancel₀ (pow_ne_zero _ hϖ0) hmul
  push_cast
  exact hfin

private theorem bad_case {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (val : Valuation ↥(modularFunctionFieldBar (N * q)) Γ)
    (ta sb tb sa ϖB : ↥(R.nodeIntegersOver K w)) (ma mb : ℕ) (hlt : ma < mb) (z : ↥(modularFunctionFieldBar (N * q)))
    (hϖ0 : (ϖB : ↥(modularFunctionFieldBar (N * q))) ≠ 0) (hϖlt : val (ϖB : ↥(modularFunctionFieldBar (N * q))) < 1) (hz : val z ≤ 1)
    (hta : val (ta : ↥(modularFunctionFieldBar (N * q))) = 1) (hsb : val (sb : ↥(modularFunctionFieldBar (N * q))) = 1)
    (htb : val (tb : ↥(modularFunctionFieldBar (N * q))) = 1) (hsa : val (sa : ↥(modularFunctionFieldBar (N * q))) = 1)
    (key : z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) =
      (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q)))) : False := by
  have hpow : (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ mb = (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ ma * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) := by
    rw [← pow_add, Nat.add_sub_cancel' hlt.le]
  have key2 : z * (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q))) = (ta : ↥(modularFunctionFieldBar (N * q))) * (sb : ↥(modularFunctionFieldBar (N * q))) := by
    apply mul_left_cancel₀ (pow_ne_zero ma hϖ0)
    linear_combination key - (z * (tb : ↥(modularFunctionFieldBar (N * q))) * (sa : ↥(modularFunctionFieldBar (N * q)))) * hpow
  have hv := congrArg val key2
  rw [map_mul, map_mul, map_mul, map_pow, map_mul, hta, hsb, htb, hsa, mul_one, mul_one, mul_one] at hv
  have hpk : val (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) < 1 := pow_lt_one₀ zero_le' hϖlt (by omega)
  have hle1 : val z * val (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) ≤
      val (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma) := by
    have := mul_le_mul_left hz (val (ϖB : ↥(modularFunctionFieldBar (N * q))) ^ (mb - ma))
    rwa [one_mul] at this
  rw [hv] at hle1
  exact absurd (lt_of_le_of_lt hle1 hpk) (lt_irrefl _)

private theorem exists_mul_eq_of_mem_integers [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.y, c.x}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.y, c.x})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧
      c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y} ∧ c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.y * c.x = R.nodeConst K w ϖ ^ E * u)
    (a b : ↥(R.nodeIntegersOver K w)) (hb : b ≠ 0)
    (z : ↥(modularFunctionFieldBar (N * q))) (hz : z ∈ R.R₂.integers)
    (hzab : z * (b : ↥(modularFunctionFieldBar (N * q))) = a) :
    ∃ a' b' : ↥(R.nodeIntegersOver K w), R.nodeResidue₂ w ⟨b', b'.2.1⟩ ≠ 0 ∧ z * (b' : ↥(modularFunctionFieldBar (N * q))) = a' := by
  classical
  have hker := ker_res₂_eq R K w c ϖ hϖ hmax hbr.1 hbr.2.2.1
  have hres_of_notmem : ∀ v : ↥(R.nodeIntegersOver K w), v ∉ Ideal.span {R.nodeConst K w ϖ, c.y} → res₂ R K w v ≠ 0 := by
    intro v hv h0
    exact hv (by rw [← hker]; exact h0)
  by_cases ha : a = 0
  · refine ⟨0, 1, ?_, ?_⟩
    · have : res₂ R K w 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
      exact this
    · have hb' : (b : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h => hb (Subtype.ext h)
      have hz0 : z = 0 := by
        have : z * (b : ↥(modularFunctionFieldBar (N * q))) = 0 := by rw [hzab, ha]; rfl
        exact (mul_eq_zero.mp this).resolve_right hb'
      rw [hz0, zero_mul]; rfl
  obtain ⟨ma, sa, ta, hsa, hta, hfa⟩ :=
    exists_mul_eq_pow_mul R K w c ϖ hbr.1 hbr.2.2.1 hbr.2.2.2 E hE u hu hxy a ha
  obtain ⟨mb, sb, tb, hsb, htb, hfb⟩ :=
    exists_mul_eq_pow_mul R K w c ϖ hbr.1 hbr.2.2.1 hbr.2.2.2 E hE u hu hxy b hb
  have hϖB0 := nodeConst_ne_zero R K w c ϖ hbr.2.2.1 hbr.2.2.2 E hE u hxy
  have hϖF0 : ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h0 => hϖB0 (Subtype.ext h0)
  have key := cross_identity R K w a b sa ta sb tb (R.nodeConst K w ϖ) ma mb z hzab hfa hfb
  rcases le_or_gt mb ma with hle | hlt
  · refine ⟨R.nodeConst K w ϖ ^ (ma - mb) * ta * sb, tb * sa, ?_,
      good_case R K w ta sb tb sa (R.nodeConst K w ϖ) ma mb hle z hϖF0 key⟩
    have : res₂ R K w (tb * sa) ≠ 0 := by
      rw [map_mul]
      exact mul_ne_zero (hres_of_notmem tb htb) (hres_of_notmem sa hsa)
    exact this
  · exact (bad_case R K w R.R₂.integers.valuation ta sb tb sa (R.nodeConst K w ϖ) ma mb hlt z hϖF0
      (valuation_nodeConst_lt_one R K w ϖ hϖ)
      ((ValuationSubring.valuation_le_one_iff R.R₂.integers z).mpr hz)
      (valuation_eq_one_of_res₂_ne_zero R K w ta (hres_of_notmem ta hta))
      (valuation_eq_one_of_res₂_ne_zero R K w sb (hres_of_notmem sb hsb))
      (valuation_eq_one_of_res₂_ne_zero R K w tb (hres_of_notmem tb htb))
      (valuation_eq_one_of_res₂_ne_zero R K w sa (hres_of_notmem sa hsa)) key).elim

end Loc

end AnnulusLocBranchSnd

end LocBranchCore

universe u

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence ssPlaces arithFrobC modularFunctionFieldFullC NodeLocalized.coeffSubring NodeLocalized.redRestrict NodeLocalized.fieldOver uvCrossingIdeal UVCrossingModel UVCrossingModel.mk UVCrossingModel.U UVCrossingModel.V UVCrossingModel.const UVCrossingModel.constHom UVCrossingModel.constHom_apply UVCrossingModel.annulusWeight UVCrossingModel.repGaussOrder UVCrossingModel.repGaussOrder_le UVCrossingModel.gaussOrder_le_iff UVCrossingModel.finsum_rank_mul_length_eq_circleIndexDrop UVCrossingModel.sInf_dominantIndices_eq_of_sub_mul_U_pow_mem UVCrossingModel.existsUnique_normalForm UVCrossingModel.sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed isCurveOver_laurentBaseChange_modularFunctionFieldFull arithFrobC_smul_eq_frobOnPlacesGeomLevel PlaceSpecialization.ProlongationTuple.gaussOrder_fst_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul PlaceSpecialization.ProlongationTuple.gaussOrder_snd_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul PlaceSpecialization.ProlongationTuple.sum_ord_eq_finsum_rank_mul_length_of_total_eq PlaceSpecialization.ProlongationTuple.sum_ord_eq_finsum_rank_mul_length_total_of_nodeResidue_ne_zero UVCrossingModel.finsum_rank_mul_length_eq_sInf_sub_sSup UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm UVCrossingModel.const_mem_nonZeroDivisors PlaceSpecialization.ProlongationTuple.nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed NodeLocalized.isDiscreteValuationRing_coeffSubring UVCrossingModel.gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq_scaled"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "gaussOrder_mul mk U V const constHom constHom_apply mk_surjective D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff gaussOrder_le_iff finsum_rank_mul_length_eq_circleIndexDrop nfCoeff nfExponent termOrder dominantIndices circleIndexDrop sInf_dominantIndices_eq_of_sub_mul_U_pow_mem existsUnique_normalForm sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem finsum_rank_mul_length_eq_sInf_sub_sSup sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul gaussOrder_scaled_eq_repGaussOrder_normalForm const_mem_nonZeroDivisors gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq_scaled"
p2m_open "ModularCurve.UVCrossingModel ModularCurve"

variable {W : Type u} [CommRing W]

private theorem annulusWeight_mul (s e t : ℕ) (d : Fin 2 →₀ ℕ) :
    annulusWeight (s * e) (s * t) d = s * annulusWeight e t d := by
  unfold annulusWeight
  rw [← Nat.mul_sub]
  ring

private theorem repGaussOrder_mul_scale (v : W → ℕ∞) (s e t : ℕ) (hs : s ≠ 0)
    (F : MvPowerSeries (Fin 2) W) :
    repGaussOrder (fun w => ((s : ℕ) : ℕ∞) * v w) (s * e) (s * t) F =
      ((s : ℕ) : ℕ∞) * repGaussOrder v e t F := by
  have hs' : ((s : ℕ) : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr hs
  simp only [repGaussOrder, annulusWeight_mul, ENat.coe_mul, ENat.mul_iInf_of_ne hs', mul_add]

private theorem gaussOrder_mul_scale' (v : W → ℕ∞) (π : W) (s e t : ℕ) (hs : s ≠ 0)
    (x : UVCrossingModel W π) :
    gaussOrder (fun w => ((s : ℕ) : ℕ∞) * v w) π (s * e) (s * t) x =
      ((s : ℕ) : ℕ∞) * gaussOrder v π e t x := by
  simp only [gaussOrder, ENat.mul_iSup, repGaussOrder_mul_scale v s e t hs]

private theorem termOrder_mul_scale (v : W → ℕ∞) (s E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (n : ℤ) :
    termOrder (fun w => ((s : ℕ) : ℕ∞) * v w) (s * E) (s * t) ab n =
      ((s : ℕ) : ℕ∞) * termOrder v E t ab n := by
  simp only [termOrder, annulusWeight_mul, ENat.coe_mul, mul_add]

private theorem dominantIndices_mul_scale (v : W → ℕ∞) (s E t : ℕ) (hs : s ≠ 0)
    (ab : PowerSeries W × PowerSeries W) :
    dominantIndices (fun w => ((s : ℕ) : ℕ∞) * v w) (s * E) (s * t) ab =
      dominantIndices v E t ab := by
  have hs' : ((s : ℕ) : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr hs
  have hcancel : ∀ x y : ℕ∞, ((s : ℕ) : ℕ∞) * x = ((s : ℕ) : ℕ∞) * y ↔ x = y := fun x y =>
    (ENat.mul_right_strictMono hs' (ENat.coe_ne_top s)).injective.eq_iff
  ext n
  simp only [dominantIndices, Set.mem_setOf_eq, termOrder_mul_scale v s E t,
    repGaussOrder_mul_scale v s E t hs]
  exact hcancel _ _

private theorem circleIndexDrop_mul_scale (v : W → ℕ∞) (s E t : ℕ) (hs : s ≠ 0)
    (ab : PowerSeries W × PowerSeries W) :
    circleIndexDrop (fun w => ((s : ℕ) : ℕ∞) * v w) (s * E) (s * t) ab =
      circleIndexDrop v E t ab := by
  simp only [circleIndexDrop, dominantIndices_mul_scale v s E t hs ab]

end ModularCurve.UVCrossingModel

section
p2m_open "ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve ModularCurve.UVCrossingModel P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve.UVCrossingModel IsLocalRing"

namespace AnnulusEnds

variable {W : Type u} [CommRing W]

private theorem inU_C_add_inV_zero (c : W) : inU (PowerSeries.C c) + inV (0 : PowerSeries W) = MvPowerSeries.C c := by
  classical
  ext d
  rw [map_add, coeff_inU, coeff_inV, MvPowerSeries.coeff_C, (PowerSeries.coeff (d 1)).map_zero, PowerSeries.coeff_C]
  simp only [ite_self, add_zero]
  by_cases hd : d = 0
  · subst hd; simp
  · rw [if_neg hd]
    have hne : ¬ (d 1 = 0 ∧ d 0 = 0) := by
      rintro ⟨h1, h0⟩; apply hd; ext i; fin_cases i <;> simp [h0, h1]
    by_cases h1 : d 1 = 0
    · rw [if_pos h1, if_neg (fun h0 => hne ⟨h1, h0⟩)]
    · rw [if_neg h1]

private theorem repGaussOrder_C (v : W → ℕ∞) (hv0 : v 0 = ⊤) (e t : ℕ) (c : W) :
    repGaussOrder v e t (MvPowerSeries.C c : MvPowerSeries (Fin 2) W) = v c := by
  classical
  apply le_antisymm
  · refine le_trans (repGaussOrder_le _ _ _ _ 0) ?_
    simp [annulusWeight, MvPowerSeries.coeff_C]
  · rw [le_repGaussOrder_iff]
    intro d
    by_cases hd : d = 0
    · subst hd; simp [annulusWeight, MvPowerSeries.coeff_C]
    · rw [MvPowerSeries.coeff_C, if_neg hd, hv0, top_add]
      exact le_top

private theorem dominantIndices_C_zero (v : W → ℕ∞) (hv0 : v 0 = ⊤) (e t : ℕ) (c : W) (hc : v c ≠ ⊤) :
    dominantIndices v e t (PowerSeries.C c, 0) = {0} := by
  classical
  ext n
  rw [dominantIndices, Set.mem_setOf_eq, Set.mem_singleton_iff, inU_C_add_inV_zero, repGaussOrder_C v hv0]
  constructor
  · intro h
    rcases n with (_ | i) | j
    · rfl
    · exfalso
      rw [termOrder, nfCoeff] at h
      simp only [PowerSeries.coeff_C, Nat.succ_ne_zero, ite_false, hv0, top_add] at h
      exact hc h.symm
    · exfalso
      rw [termOrder, nfCoeff] at h
      simp only [map_zero, hv0, top_add] at h
      exact hc h.symm
  · rintro rfl
    show termOrder v e t (PowerSeries.C c, 0) (Int.ofNat 0) = v c
    rw [termOrder, nfCoeff, nfExponent]
    simp [annulusWeight, PowerSeries.coeff_C]

variable [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

private theorem const_dom
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (c : W) (hc : c ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habc : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = const (ϖ ^ e) c) :
    sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) = 0 ∧
      sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab) = 0 := by
  classical
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := by rw [← hϖ.maximalIdeal_eq]; infer_instance

  obtain ⟨ab₀, -, huniq⟩ := existsUnique_normalForm ϖ e he (const (ϖ ^ e) c)
  have h1 : ab = ab₀ := huniq ab ⟨hb, habc⟩
  have h2 : (PowerSeries.C c, (0 : PowerSeries W)) = ab₀ :=
    huniq (PowerSeries.C c, 0) ⟨by simp, by show mk (ϖ ^ e) (inU (PowerSeries.C c) + inV 0) = _; rw [inU_C_add_inV_zero]; rfl⟩
  have hab : ab = (PowerSeries.C c, 0) := h1.trans h2.symm
  subst hab
  have hvc : IsDiscreteValuationRing.addVal W c ≠ ⊤ := (IsDiscreteValuationRing.addVal_eq_top_iff.not).mpr hc
  rw [dominantIndices_C_zero _ IsDiscreteValuationRing.addVal_zero e 0 c hvc,
    dominantIndices_C_zero _ IsDiscreteValuationRing.addVal_zero e e c hvc]
  exact ⟨csInf_singleton 0, csSup_singleton 0⟩

end AnnulusEnds
end

section
p2m_open "ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve ModularCurve.UVCrossingModel P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve.UVCrossingModel IsLocalRing"

namespace AnnulusEnds

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

private theorem scale_one : (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) = ⇑(IsDiscreteValuationRing.addVal W) := by
  funext w; simp

private theorem extremes_sub_eq_of_mul_eq_const_mul (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (X Y X₁ Y₁ : UVCrossingModel W (ϖ ^ e)) (hX : X ≠ 0) (hY : Y ≠ 0) (hX₁ : X₁ ≠ 0) (hY₁ : Y₁ ≠ 0)
    (c : W) (hc : c ≠ 0) (hrel : X * Y₁ = const (ϖ ^ e) c * (X₁ * Y)) (hXY₁ : X * Y₁ ≠ 0) (hX₁Y : X₁ * Y ≠ 0)
    (abX abY abX₁ abY₁ : PowerSeries W × PowerSeries W)
    (hbX : PowerSeries.constantCoeff abX.2 = 0) (habX : mk (ϖ ^ e) (inU abX.1 + inV abX.2) = X)
    (hbY : PowerSeries.constantCoeff abY.2 = 0) (habY : mk (ϖ ^ e) (inU abY.1 + inV abY.2) = Y)
    (hbX₁ : PowerSeries.constantCoeff abX₁.2 = 0) (habX₁ : mk (ϖ ^ e) (inU abX₁.1 + inV abX₁.2) = X₁)
    (hbY₁ : PowerSeries.constantCoeff abY₁.2 = 0) (habY₁ : mk (ϖ ^ e) (inU abY₁.1 + inV abY₁.2) = Y₁) :
    sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * e) (1 * e) abX) - sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * e) (1 * e) abY) =
      sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * e) (1 * e) abX₁) - sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * e) (1 * e) abY₁) ∧
    sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * e) 0 abX) - sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * e) 0 abY) =
      sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * e) 0 abX₁) - sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * e) 0 abY₁) := by
  rw [scale_one, one_mul]
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]; infer_instance
  have hc0 : const (ϖ ^ e) c ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hrel
    exact hXY₁ hrel

  obtain ⟨abP, ⟨hbP, habP⟩, -⟩ := existsUnique_normalForm ϖ e he (X * Y₁)
  obtain ⟨abQ, ⟨hbQ, habQ⟩, -⟩ := existsUnique_normalForm ϖ e he (X₁ * Y)
  obtain ⟨abC, ⟨hbC, habC⟩, -⟩ := existsUnique_normalForm ϖ e he (const (ϖ ^ e) c)

  have habP' : mk (ϖ ^ e) (inU abP.1 + inV abP.2) = const (ϖ ^ e) c * (X₁ * Y) := habP.trans hrel
  obtain ⟨h1i, h1s⟩ := sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul ϖ hϖ e he X hX abX hbX habX Y₁ hY₁ abY₁ hbY₁ habY₁ abP hbP habP
  obtain ⟨h2i, h2s⟩ := sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul ϖ hϖ e he X₁ hX₁ abX₁ hbX₁ habX₁ Y hY abY hbY habY abQ hbQ habQ
  obtain ⟨h3i, h3s⟩ := sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul ϖ hϖ e he (const (ϖ ^ e) c) hc0 abC hbC habC (X₁ * Y) hX₁Y abQ hbQ habQ abP hbP habP'
  obtain ⟨hCi, hCs⟩ := const_dom ϖ hϖ e he c hc abC hbC habC
  constructor
  · linear_combination -h1s + h3s + h2s + hCs
  · linear_combination -h1i + h3i + h2i + hCi

end AnnulusEnds
end

section
p2m_open "ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve ModularCurve.UVCrossingModel P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve.UVCrossingModel IsLocalRing"

namespace AnnulusPair

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

private theorem gaussOrder_const [IsAdicComplete (maximalIdeal W) W] (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (c : W) (t : ℕ) (ht : t ≤ e) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t (const (ϖ ^ e) c) =
      IsDiscreteValuationRing.addVal W c := by
  classical
  have hnf : inU (PowerSeries.C c) + inV (0 : PowerSeries W) = MvPowerSeries.C c := by
    ext d
    rw [map_add, coeff_inU, coeff_inV, MvPowerSeries.coeff_C, (PowerSeries.coeff (d 1)).map_zero,
      PowerSeries.coeff_C]
    simp only [ite_self, add_zero]
    by_cases hd : d = 0
    · subst hd; simp
    · rw [if_neg hd]
      have hne : ¬ (d 1 = 0 ∧ d 0 = 0) := by
        rintro ⟨h1, h0⟩; apply hd; ext i; fin_cases i <;> simp [h0, h1]
      by_cases h1 : d 1 = 0
      · rw [if_pos h1, if_neg (fun h0 => hne ⟨h1, h0⟩)]
      · rw [if_neg h1]
  have hA := gaussOrder_scaled_eq_repGaussOrder_normalForm ϖ hϖ e he 1 le_rfl (const (ϖ ^ e) c)
    (PowerSeries.C c, 0) (by simp) (by rw [hnf]; rfl) t (by simpa using ht)
  simp only [Nat.cast_one, one_mul, Nat.one_mul] at hA
  rw [hA, hnf]

  apply le_antisymm
  · refine le_trans (repGaussOrder_le _ _ _ _ 0) ?_
    simp [annulusWeight, MvPowerSeries.coeff_C]
  · rw [le_repGaussOrder_iff]
    intro d
    by_cases hd : d = 0
    · subst hd; simp [annulusWeight, MvPowerSeries.coeff_C]
    · rw [MvPowerSeries.coeff_C, if_neg hd, IsDiscreteValuationRing.addVal_zero, top_add]
      exact le_top

private theorem gaussOrder_add_eq_addVal_add_of_mul_eq_const_mul [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (X₁ Y₁ X₂ Y₂ : UVCrossingModel W (ϖ ^ e)) (c : W) (hrel : X₁ * Y₂ = const (ϖ ^ e) c * (X₂ * Y₁))
    (t : ℕ) (ht : t ≤ e) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t X₁ +
        gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t Y₂ =
      IsDiscreteValuationRing.addVal W c +
        (gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t X₂ +
          gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t Y₁) := by
  have h := congrArg (gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t) hrel
  rw [gaussOrder_mul ϖ hϖ e t he ht, gaussOrder_mul ϖ hϖ e t he ht, gaussOrder_mul ϖ hϖ e t he ht,
    gaussOrder_const ϖ hϖ e he c t ht] at h
  exact h

private theorem sub_sub_eq_of_mul_eq_const_mul [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (X₁ Y₁ X₂ Y₂ : UVCrossingModel W (ϖ ^ e)) (c : W) (hc : c ≠ 0) (hrel : X₁ * Y₂ = const (ϖ ^ e) c * (X₂ * Y₁))
    (hfin : ∀ t, t ≤ e → gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t X₁ ≠ ⊤ ∧
      gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t Y₁ ≠ ⊤ ∧
      gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t X₂ ≠ ⊤ ∧
      gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t Y₂ ≠ ⊤)
    (t t' : ℕ) (ht : t ≤ e) (ht' : t' ≤ e) :
    (((gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t X₁).toNat : ℤ)
        - (gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t Y₁).toNat)
      - (((gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t' X₁).toNat : ℤ)
        - (gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t' Y₁).toNat) =
    (((gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t X₂).toNat : ℤ)
        - (gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t Y₂).toNat)
      - (((gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t' X₂).toNat : ℤ)
        - (gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t' Y₂).toNat) := by
  have hvc : IsDiscreteValuationRing.addVal W c ≠ ⊤ := by
    rw [ne_eq, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hc

  have key : ∀ s, s ≤ e →
      ((gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e s X₁).toNat : ℤ)
        + (gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e s Y₂).toNat =
      ((IsDiscreteValuationRing.addVal W c).toNat : ℤ)
        + ((gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e s X₂).toNat
          + (gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e s Y₁).toNat) := by
    intro s hs
    obtain ⟨h1, h2, h3, h4⟩ := hfin s hs
    have h := gaussOrder_add_eq_addVal_add_of_mul_eq_const_mul ϖ hϖ e he X₁ Y₁ X₂ Y₂ c hrel s hs
    have h' := congrArg ENat.toNat h
    have h32 : gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e s X₂ +
        gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e s Y₁ ≠ ⊤ := WithTop.add_ne_top.mpr ⟨h3, h2⟩
    rw [ENat.toNat_add h1 h4, ENat.toNat_add hvc h32, ENat.toNat_add h3 h2] at h'
    exact_mod_cast h'
  have k1 := key t ht
  have k2 := key t' ht'
  linear_combination k1 - k2

end AnnulusPair
end

section
p2m_open "ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve ModularCurve.UVCrossingModel P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve.UVCrossingModel IsLocalRing"

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence ssPlaces arithFrobC modularFunctionFieldFullC NodeLocalized.coeffSubring NodeLocalized.redRestrict NodeLocalized.fieldOver uvCrossingIdeal UVCrossingModel UVCrossingModel.mk UVCrossingModel.U UVCrossingModel.V UVCrossingModel.const UVCrossingModel.constHom UVCrossingModel.constHom_apply UVCrossingModel.annulusWeight UVCrossingModel.repGaussOrder UVCrossingModel.repGaussOrder_le UVCrossingModel.gaussOrder_le_iff UVCrossingModel.finsum_rank_mul_length_eq_circleIndexDrop UVCrossingModel.sInf_dominantIndices_eq_of_sub_mul_U_pow_mem UVCrossingModel.existsUnique_normalForm UVCrossingModel.sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed isCurveOver_laurentBaseChange_modularFunctionFieldFull arithFrobC_smul_eq_frobOnPlacesGeomLevel PlaceSpecialization.ProlongationTuple.gaussOrder_fst_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul PlaceSpecialization.ProlongationTuple.gaussOrder_snd_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul PlaceSpecialization.ProlongationTuple.sum_ord_eq_finsum_rank_mul_length_of_total_eq PlaceSpecialization.ProlongationTuple.sum_ord_eq_finsum_rank_mul_length_total_of_nodeResidue_ne_zero UVCrossingModel.finsum_rank_mul_length_eq_sInf_sub_sSup UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm UVCrossingModel.const_mem_nonZeroDivisors PlaceSpecialization.ProlongationTuple.nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed NodeLocalized.isDiscreteValuationRing_coeffSubring UVCrossingModel.gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq_scaled" namespace UVCrossingModel p2m_export "ModularCurve.UVCrossingModel" "gaussOrder_mul mk U V const constHom constHom_apply mk_surjective D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff gaussOrder_le_iff finsum_rank_mul_length_eq_circleIndexDrop nfCoeff nfExponent termOrder dominantIndices circleIndexDrop sInf_dominantIndices_eq_of_sub_mul_U_pow_mem existsUnique_normalForm sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem finsum_rank_mul_length_eq_sInf_sub_sSup sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul gaussOrder_scaled_eq_repGaussOrder_normalForm const_mem_nonZeroDivisors gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq_scaled" end ModularCurve.UVCrossingModel
p2m_open_scoped "ModularCurve ModularCurve.UVCrossingModel" in
private theorem ModularCurve.UVCrossingModel.gaussOrder_ne_top_of_ne_zero
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (t : ℕ) (ht : t ≤ e) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t x ≠ ⊤ := by
  classical

  haveI : IsAdicComplete (Ideal.span {ϖ}) W := by rw [← hϖ.maximalIdeal_eq]; infer_instance
  obtain ⟨ab, ⟨hb, habx⟩, -⟩ := ModularCurve.UVCrossingModel.existsUnique_normalForm ϖ e he x

  have key := ModularCurve.UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm ϖ hϖ e he 1 le_rfl x ab hb habx t
    (by rwa [one_mul])
  have hv : (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) = IsDiscreteValuationRing.addVal W := by
    funext w; rw [Nat.cast_one, one_mul]
  rw [hv, one_mul] at key
  rw [key]

  have hF : inU ab.1 + inV ab.2 ≠ 0 := by
    intro h0
    apply hx
    rw [← habx, h0, map_zero]
  obtain ⟨d, hd⟩ : ∃ d, MvPowerSeries.coeff d (inU ab.1 + inV ab.2) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hF (MvPowerSeries.ext fun d => by rw [hall d, map_zero])
  refine ne_top_of_le_ne_top ?_ (repGaussOrder_le _ e t _ d)
  exact WithTop.add_ne_top.mpr ⟨(IsDiscreteValuationRing.addVal_eq_top_iff.not).mpr hd, WithTop.natCast_ne_top _⟩
end

section
open IsLocalRing

private theorem ConstantUnits.algebraMap_adicCompletion_ne_zero {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (z : B) (hz : z ≠ 0) :
    algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) z ≠ 0 := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  intro h
  apply hz
  have hinj : Function.Injective (AdicCompletion.of (maximalIdeal B) B) := AdicCompletion.of_injective (maximalIdeal B) B
  exact hinj (by rw [h, map_zero])
end

section
p2m_open "ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve ModularCurve.UVCrossingModel P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve.UVCrossingModel IsLocalRing"

private theorem ConstantUnits.mem_span_of_const_eq_zero {W : Type*} [CommRing W] (π c : W) (h : const π c = 0) : c ∈ Ideal.span {π} := by
  classical
  have hker : ∀ f ∈ uvCrossingIdeal W π, ((Ideal.Quotient.mk (Ideal.span {π})).comp MvPowerSeries.constantCoeff) f = 0 := by
    intro f hf
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    have hP : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C π :
        MvPowerSeries (Fin 2) W) = -π := by
      rw [map_sub, map_mul, MvPowerSeries.constantCoeff_X, zero_mul, MvPowerSeries.constantCoeff_C, zero_sub]
    rw [RingHom.comp_apply, map_mul, hP, map_mul, map_neg, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π),
      neg_zero, mul_zero]
  have hρ : Ideal.Quotient.lift _ _ hker (const π c) = Ideal.Quotient.mk (Ideal.span {π}) c := by
    show Ideal.Quotient.lift _ _ hker (UVCrossingModel.mk π (MvPowerSeries.C c)) = _
    rw [UVCrossingModel.mk, Ideal.Quotient.lift_mk, RingHom.comp_apply, MvPowerSeries.constantCoeff_C]
  have := congrArg (Ideal.Quotient.lift _ _ hker) h
  rw [hρ, map_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

private theorem ConstantUnits.const_ne_zero {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (c : W) (hc : c ≠ 0) : const (ϖ ^ e) c ≠ 0 := by
  classical
  have hπ0 : ϖ ^ e ∈ nonZeroDivisors W := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hϖ.ne_zero)
  have hnzd := ModularCurve.UVCrossingModel.const_mem_nonZeroDivisors (W := W) hπ0

  suffices key : ∀ (n : ℕ) (c : W), c ≠ 0 → IsDiscreteValuationRing.addVal W c ≤ n → const (ϖ ^ e) c ≠ 0 by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ((IsDiscreteValuationRing.addVal_eq_top_iff.not).mpr hc)
    exact key n c hc (by rw [← hn])
  intro n
  induction n with
  | zero =>
    intro c hc hv h0
    have hcm : c ∈ Ideal.span {ϖ} :=
      Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self ϖ (by omega)) (ConstantUnits.mem_span_of_const_eq_zero _ _ h0)
    rw [Ideal.mem_span_singleton] at hcm
    have h1 : (1 : ℕ∞) ≤ IsDiscreteValuationRing.addVal W c := by
      rw [← IsDiscreteValuationRing.addVal_uniformizer hϖ]
      exact IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hcm
    have := h1.trans hv
    simp at this
  | succ n ih =>
    intro c hc hv h0
    obtain ⟨c₁, rfl⟩ := Ideal.mem_span_singleton'.mp (ConstantUnits.mem_span_of_const_eq_zero _ _ h0)
    have hc₁ : c₁ ≠ 0 := fun h => hc (by rw [h, zero_mul])
    have h0' : const (ϖ ^ e) c₁ = 0 := by
      have : const (ϖ ^ e) c₁ * const (ϖ ^ e) (ϖ ^ e) = 0 := by
        rw [← UVCrossingModel.constHom_apply, ← UVCrossingModel.constHom_apply, ← map_mul]; exact h0
      exact (mul_right_mem_nonZeroDivisors_eq_zero_iff hnzd).mp this
    have hv₁ : IsDiscreteValuationRing.addVal W c₁ ≤ n := by
      have hadd : IsDiscreteValuationRing.addVal W (c₁ * ϖ ^ e) =
          IsDiscreteValuationRing.addVal W c₁ + (e : ℕ∞) := by
        rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]
        simp
      rw [hadd] at hv
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp ((IsDiscreteValuationRing.addVal_eq_top_iff.not).mpr hc₁)
      rw [← hm] at hv ⊢
      have : (m : ℕ∞) + (e : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) := hv
      norm_cast at this ⊢
      omega
    exact ih c₁ hc₁ hv₁ h0'
end

namespace SlopeLaw

section Wiring
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem red_eq_zero_iff (R : ProlongationTuple P) (c : A) : red c = 0 ↔ c ∈ maximalIdeal A := by
  rw [← R.redBar_residue, map_eq_zero_iff _ R.redBar.injective, IsLocalRing.residue_eq_zero_iff]

omit [Fact q.Prime] in

private theorem fieldOver_mono (M : ℕ) [NeZero M] {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K') :
    NodeLocalized.fieldOver M K ≤ NodeLocalized.fieldOver M K' := by
  unfold NodeLocalized.fieldOver
  apply Subfield.closure_mono
  apply Set.union_subset_union_left
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x.1, hKK' x.2⟩, rfl⟩

end Wiring

section Enlarge
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem nodeIntegersOver_mono (R : ProlongationTuple P) {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K')
    (w : Place k (modularFunctionFieldC k N)) : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w :=
  fun _ hf => ⟨hf.1, fieldOver_mono (N * q) hKK' hf.2⟩

private def enlargeCoordinates (R : ProlongationTuple P) [PerfectField k] {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K')
    {w : Place k (modularFunctionFieldC k N)} (c : R.NodeCoordinates K w) : R.NodeCoordinates K' w where
  x := ⟨c.x.1, nodeIntegersOver_mono R hKK' w c.x.2⟩
  y := ⟨c.y.1, nodeIntegersOver_mono R hKK' w c.y.2⟩
  x_fst := c.x_fst
  x_snd := c.x_snd
  y_snd := c.y_snd
  y_fst := c.y_fst

set_option maxHeartbeats 0 in

private def inclCoords (R : ProlongationTuple P) [PerfectField k] {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {w : Place k (modularFunctionFieldC k N)} (hBB' : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w)
    (c : R.NodeCoordinates K w) : R.NodeCoordinates K' w where
  x := ⟨c.x.1, hBB' c.x.2⟩
  y := ⟨c.y.1, hBB' c.y.2⟩
  x_fst := c.x_fst
  x_snd := c.x_snd
  y_snd := c.y_snd
  y_fst := c.y_fst

set_option maxHeartbeats 0 in

private theorem inclusion_x (R : ProlongationTuple P) [PerfectField k] {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {w : Place k (modularFunctionFieldC k N)} (hBB' : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w)
    (c : R.NodeCoordinates K w) : Subring.inclusion hBB' c.x = (inclCoords R hBB' c).x := rfl

set_option maxHeartbeats 0 in

private theorem inclusion_y (R : ProlongationTuple P) [PerfectField k] {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {w : Place k (modularFunctionFieldC k N)} (hBB' : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w)
    (c : R.NodeCoordinates K w) : Subring.inclusion hBB' c.y = (inclCoords R hBB' c).y := rfl

end Enlarge

section Iface
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem packet_isUnit_of_red_ne_zero (A : ValuationSubring (AlgebraicClosure ℚ)) (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ maximalIdeal A) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (z : ↥(NodeLocalized.coeffSubring A K)) (hz : NodeLocalized.redRestrict red K z ≠ 0) : IsUnit z := by
  have hzA : (⟨(z : AlgebraicClosure ℚ), z.2.1⟩ : ↥A) ∉ maximalIdeal ↥A := fun h => hz ((hker _).mpr h)
  have hv1 : A.valuation (z : AlgebraicClosure ℚ) = 1 := by
    have hle := (A.valuation_le_one_iff _).mpr z.2.1
    have hnlt : ¬ A.valuation (z : AlgebraicClosure ℚ) < 1 := fun h => hzA ((A.valuation_lt_one_iff ⟨_, z.2.1⟩).mpr h)
    exact le_antisymm hle (not_lt.mp hnlt)
  have hz0 : (z : AlgebraicClosure ℚ) ≠ 0 := fun h => by rw [h, map_zero] at hv1; exact zero_ne_one hv1
  have hinvA : (z : AlgebraicClosure ℚ)⁻¹ ∈ A := (A.valuation_le_one_iff _).mp (by rw [map_inv₀, hv1, inv_one])
  have hinvK : (z : AlgebraicClosure ℚ)⁻¹ ∈ K := inv_mem (show (z : AlgebraicClosure ℚ) ∈ K from z.2.2)
  exact isUnit_iff_exists_inv.mpr ⟨⟨(z : AlgebraicClosure ℚ)⁻¹, hinvA, hinvK⟩, Subtype.ext (mul_inv_cancel₀ hz0)⟩

include q in

private theorem coeffRing_packet (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K']
    (hker : ∀ a : A, red a = 0 ↔ a ∈ maximalIdeal A)
    (ϖ : ↥(NodeLocalized.coeffSubring A K'))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ * d') :
    ∃ (_ : IsDomain (PowerSeries ↥(NodeLocalized.coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ})) (_ : IsDiscreteValuationRing (PowerSeries ↥(NodeLocalized.coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}))
      (_ : IsAdicComplete (maximalIdeal (PowerSeries ↥(NodeLocalized.coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ})) (PowerSeries ↥(NodeLocalized.coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ})),
      Irreducible (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) := by
  haveI : IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K') :=
    ModularCurve.NodeLocalized.isDiscreteValuationRing_coeffSubring (q := q) red hker K'

  have hmax : maximalIdeal ↥(NodeLocalized.coeffSubring A K') = Ideal.span {ϖ} := by
    ext d
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_span_singleton']
    constructor
    · intro hd
      have h0 : NodeLocalized.redRestrict red K' d = 0 := by
        by_contra h; exact hd (packet_isUnit_of_red_ne_zero A red hker K' d h)
      obtain ⟨d', hd'⟩ := (hϖ d).mp h0
      exact ⟨d', by rw [hd', mul_comm]⟩
    · rintro ⟨d', rfl⟩ hu
      have hred : NodeLocalized.redRestrict red K' (d' * ϖ) = 0 := (hϖ _).mpr ⟨d', mul_comm _ _⟩
      exact (hu.map (NodeLocalized.redRestrict red K')).ne_zero hred
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hmax
  exact PowerSeries.isAdicComplete_quotient_span_X_sub_C_of_irreducible ϖ hirr

set_option maxHeartbeats 6400000 in

private theorem model (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) (hW₀ : ∀ v ∈ W₀, v ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W₀) (hval : R.NodeValueLaw W₀)
    (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K']
    (hker : ∀ a : A, red a = 0 ↔ a ∈ maximalIdeal A)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W₀) (c' : R.NodeCoordinates K' w)
    [IsLocalRing ↥(R.nodeIntegersOver K' w)] [IsNoetherianRing ↥(R.nodeIntegersOver K' w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K'))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ * d')
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K' w)) (hu : IsUnit u) (hxy : c'.x * c'.y = R.nodeConst K' w ϖ ^ E * u)
    (hmax : (Ideal.span {R.nodeConst K' w ϖ, c'.x, c'.y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K' w), M.IsMaximal → M = Ideal.span {R.nodeConst K' w ϖ, c'.x, c'.y})
    (hpr : (Ideal.span {R.nodeConst K' w ϖ, c'.x}).IsPrime) (hy : c'.y ∉ Ideal.span {R.nodeConst K' w ϖ, c'.x})
    (hres : ∀ g : ↥(R.nodeIntegersOver K' w), ∃ o : ↥(NodeLocalized.coeffSubring A K'), ¬ IsUnit (g - R.nodeConst K' w o)) :
    ∃ (_ : IsDomain (PowerSeries ↥(NodeLocalized.coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ})) (_ : IsDiscreteValuationRing (PowerSeries ↥(NodeLocalized.coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}))
      (_ : IsAdicComplete (maximalIdeal (PowerSeries ↥(NodeLocalized.coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ})) (PowerSeries ↥(NodeLocalized.coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}))
      (θ : MvPowerSeries (Fin 2) (PowerSeries ↥(NodeLocalized.coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) →+* AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K' w)) ↥(R.nodeIntegersOver K' w))
      (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K' w)) ↥(R.nodeIntegersOver K' w) ≃+* UVCrossingModel (PowerSeries ↥(NodeLocalized.coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ E))
      (α β : UVCrossingModel (PowerSeries ↥(NodeLocalized.coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ E)),
      Irreducible (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ∧ IsUnit α ∧ IsUnit β ∧
      (∀ o : ↥(NodeLocalized.coeffSubring A K'),
        ι (algebraMap _ _ (R.nodeConst K' w o)) = UVCrossingModel.const ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ E) (Ideal.Quotient.mk _ (PowerSeries.C o))) ∧
      ι (algebraMap _ _ c'.x) = UVCrossingModel.U ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ E) * α ∧
      ι (algebraMap _ _ c'.y) = UVCrossingModel.V ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ E) * β ∧
      (∀ (f : ↥(R.nodeIntegersOver K' w)) (n : ℕ), R.nodeResidue₁ w ⟨f, f.2.1⟩ ≠ 0 →
        w.ord (R.nodeResidue₁ w ⟨f, f.2.1⟩) = (n : ℤ) →
        ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * UVCrossingModel.V ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ E) ^ n ∈
          Ideal.span {UVCrossingModel.const ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ E) (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)), UVCrossingModel.U ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ E)}) ∧
      (∀ (f : ↥(R.nodeIntegersOver K' w)) (n : ℕ), R.nodeResidue₂ w ⟨f, f.2.1⟩ ≠ 0 →
        (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨f, f.2.1⟩) = (n : ℤ) →
        ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * UVCrossingModel.U ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ E) ^ n ∈
          Ideal.span {UVCrossingModel.const ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ E) (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)), UVCrossingModel.V ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ E)}) := by
  obtain ⟨instD, instV, instC, hirr⟩ := coeffRing_packet (A := A) (red := red) K' hker ϖ hϖ
  have hmaxB : maximalIdeal ↥(R.nodeIntegersOver K' w) = Ideal.span {R.nodeConst K' w ϖ, c'.x, c'.y} := hmax.2 _ (maximalIdeal.isMaximal _)
  obtain ⟨θW, θ, hθWo, hθWX, hθ, hθC, hθ0, hθ1⟩ :=
    R.exists_surjective_mvPowerSeries_adicCompletion_nodeIntegersOver K' w c' ϖ hϖ hmaxB hres
  have hdim := R.two_le_ringKrullDim_adicCompletion_nodeIntegersOver K' w c' ϖ hpr hy
  have hθπ : θ (MvPowerSeries.C (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ))) = algebraMap _ _ (R.nodeConst K' w ϖ) := by
    have := congrArg (fun g => g (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ))) hθC
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    rw [this, hθWo]
  obtain ⟨ι, α, β, hα, hβ, hWc, hιx, hιy, hord1, hord2⟩ :=
    R.exists_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel_of_isMaximal hqN hmodel W₀ hW₀ hreg hval K' w hw c'
      ϖ hϖ E hE u hu hxy hmax (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) hirr θ hθ hθπ hθ0 hθ1 hdim
  refine ⟨instD, instV, instC, θ, ι, α, β, hirr, hα, hβ, ?_, hιx, hιy, hord1, hord2⟩
  intro o
  have := congrArg (fun g => g (Ideal.Quotient.mk _ (PowerSeries.C o))) hθC
  simp only [RingHom.coe_comp, Function.comp_apply] at this
  rw [← hθWo o, ← this]
  exact hWc _

end Iface

section Rep
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

set_option maxHeartbeats 3200000 in

private theorem rep_fst (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w) [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ≠ 0) (a b : ↥(R.nodeIntegersOver K w)) (hb : b ≠ 0) (hfab : f * (b : ↥(modularFunctionFieldBar (N * q))) = a) :
    ∃ (m m' : ℕ) (x x' : ↥(R.nodeIntegersOver K w)), R.nodeResidue₁ w ⟨x, x.2.1⟩ ≠ 0 ∧ R.nodeResidue₁ w ⟨x', x'.2.1⟩ ≠ 0 ∧
      ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ^ m' * (f * (x' : ↥(modularFunctionFieldBar (N * q)))) =
        ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ^ m * (x : ↥(modularFunctionFieldBar (N * q))) := by
  classical
  have hϖ0 : NodeLocalized.redRestrict red K ϖ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩
  have hker := AnnulusLocBranch.ker_res₁_eq R K w c ϖ hϖ0 hmax hbr.1 hbr.2.2.1
  have hres_of_notmem : ∀ v : ↥(R.nodeIntegersOver K w), v ∉ Ideal.span {R.nodeConst K w ϖ, c.x} →
      R.nodeResidue₁ w ⟨v, v.2.1⟩ ≠ 0 := by
    intro v hv h0
    exact hv (by rw [← hker]; exact h0)
  have ha : a ≠ 0 := by
    intro ha0
    have hb' : (b : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h => hb (Subtype.ext h)
    have : f * (b : ↥(modularFunctionFieldBar (N * q))) = 0 := by rw [hfab, ha0]; rfl
    exact hf ((mul_eq_zero.mp this).resolve_right hb')
  obtain ⟨m, s, t, hs, ht, hfa⟩ :=
    AnnulusLocBranch.exists_mul_eq_pow_mul R K w c ϖ hbr.1 hbr.2.2.1 hbr.2.2.2 E hE u hu hxy a ha
  obtain ⟨m', s', t', hs', ht', hfb⟩ :=
    AnnulusLocBranch.exists_mul_eq_pow_mul R K w c ϖ hbr.1 hbr.2.2.1 hbr.2.2.2 E hE u hu hxy b hb
  refine ⟨m, m', t * s', s * t', ?_, ?_, ?_⟩
  · exact hres_of_notmem _ (fun h => ((hbr.1.mem_or_mem h).elim ht hs'))
  · exact hres_of_notmem _ (fun h => ((hbr.1.mem_or_mem h).elim hs ht'))
  · have h1 : (b : ↥(modularFunctionFieldBar (N * q))) * (s' : ↥(modularFunctionFieldBar (N * q))) =
        ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ^ m' * (t' : ↥(modularFunctionFieldBar (N * q))) := by
      have := congrArg (fun v : ↥(R.nodeIntegersOver K w) => (v : ↥(modularFunctionFieldBar (N * q)))) hfb
      simpa using this
    have h2 : (a : ↥(modularFunctionFieldBar (N * q))) * (s : ↥(modularFunctionFieldBar (N * q))) =
        ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ^ m * (t : ↥(modularFunctionFieldBar (N * q))) := by
      have := congrArg (fun v : ↥(R.nodeIntegersOver K w) => (v : ↥(modularFunctionFieldBar (N * q)))) hfa
      simpa using this
    push_cast
    linear_combination (-(f * (s : ↥(modularFunctionFieldBar (N * q))))) * h1 + ((s : ↥(modularFunctionFieldBar (N * q))) * (s' : ↥(modularFunctionFieldBar (N * q)))) * hfab + (s' : ↥(modularFunctionFieldBar (N * q))) * h2

end Rep

section RepSnd
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

set_option maxHeartbeats 3200000 in

private theorem rep_snd (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w) [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ≠ 0) (a b : ↥(R.nodeIntegersOver K w)) (hb : b ≠ 0) (hfab : f * (b : ↥(modularFunctionFieldBar (N * q))) = a) :
    ∃ (m m' : ℕ) (x x' : ↥(R.nodeIntegersOver K w)), R.nodeResidue₂ w ⟨x, x.2.1⟩ ≠ 0 ∧ R.nodeResidue₂ w ⟨x', x'.2.1⟩ ≠ 0 ∧
      ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ^ m' * (f * (x' : ↥(modularFunctionFieldBar (N * q)))) =
        ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ^ m * (x : ↥(modularFunctionFieldBar (N * q))) := by
  classical
  have hϖ0 : NodeLocalized.redRestrict red K ϖ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩
  have hS : (Ideal.span {R.nodeConst K w ϖ, c.y, c.x} : Ideal ↥(R.nodeIntegersOver K w)) =
      Ideal.span {R.nodeConst K w ϖ, c.x, c.y} := by
    show Ideal.span (insert _ {c.y, c.x}) = Ideal.span (insert _ {c.x, c.y})
    rw [Set.pair_comm]
  have hmax' : (Ideal.span {R.nodeConst K w ϖ, c.y, c.x}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.y, c.x} := by
    rw [hS]; exact hmax
  have hker := AnnulusLocBranchSnd.ker_res₂_eq R K w c ϖ hϖ0 hmax' hbr.2.1 hbr.2.2.2
  have hres_of_notmem : ∀ v : ↥(R.nodeIntegersOver K w), v ∉ Ideal.span {R.nodeConst K w ϖ, c.y} →
      R.nodeResidue₂ w ⟨v, v.2.1⟩ ≠ 0 := by
    intro v hv h0
    exact hv (by rw [← hker]; exact h0)
  have ha : a ≠ 0 := by
    intro ha0
    have hb' : (b : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h => hb (Subtype.ext h)
    have : f * (b : ↥(modularFunctionFieldBar (N * q))) = 0 := by rw [hfab, ha0]; rfl
    exact hf ((mul_eq_zero.mp this).resolve_right hb')
  obtain ⟨m, s, t, hs, ht, hfa⟩ :=
    AnnulusLocBranchSnd.exists_mul_eq_pow_mul R K w c ϖ hbr.2.1 hbr.2.2.2 hbr.2.2.1 E hE u hu ((mul_comm c.y c.x).trans hxy) a ha
  obtain ⟨m', s', t', hs', ht', hfb⟩ :=
    AnnulusLocBranchSnd.exists_mul_eq_pow_mul R K w c ϖ hbr.2.1 hbr.2.2.2 hbr.2.2.1 E hE u hu ((mul_comm c.y c.x).trans hxy) b hb
  refine ⟨m, m', t * s', s * t', ?_, ?_, ?_⟩
  · exact hres_of_notmem _ (fun h => ((hbr.2.1.mem_or_mem h).elim ht hs'))
  · exact hres_of_notmem _ (fun h => ((hbr.2.1.mem_or_mem h).elim hs ht'))
  · have h1 : (b : ↥(modularFunctionFieldBar (N * q))) * (s' : ↥(modularFunctionFieldBar (N * q))) =
        ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ^ m' * (t' : ↥(modularFunctionFieldBar (N * q))) := by
      have := congrArg (fun v : ↥(R.nodeIntegersOver K w) => (v : ↥(modularFunctionFieldBar (N * q)))) hfb
      simpa using this
    have h2 : (a : ↥(modularFunctionFieldBar (N * q))) * (s : ↥(modularFunctionFieldBar (N * q))) =
        ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ^ m * (t : ↥(modularFunctionFieldBar (N * q))) := by
      have := congrArg (fun v : ↥(R.nodeIntegersOver K w) => (v : ↥(modularFunctionFieldBar (N * q)))) hfa
      simpa using this
    push_cast
    linear_combination (-(f * (s : ↥(modularFunctionFieldBar (N * q))))) * h1 + ((s : ↥(modularFunctionFieldBar (N * q))) * (s' : ↥(modularFunctionFieldBar (N * q)))) * hfab + (s' : ↥(modularFunctionFieldBar (N * q))) * h2

end RepSnd

section RepSmul
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem smul_mem_fieldOver (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (f : ↥(modularFunctionFieldBar (N * q)))
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K) (c₁ : AlgebraicClosure ℚ) (hc₁ : c₁ ∈ K) :
    ((c₁ • f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K := by
  rw [IntermediateField.coe_smul, Algebra.smul_def]
  refine mul_mem ?_ hfK
  exact Subfield.subset_closure (Or.inl ⟨⟨c₁, hc₁⟩, rfl⟩)

set_option maxHeartbeats 3200000 in

private theorem rep_common (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w) [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (f : ↥(modularFunctionFieldBar (N * q)))
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K)
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    (cst : AlgebraicClosure ℚ) (hcst : cst ∈ K) (hz₁ : cst • f ∈ R.R₁.integers) (hz₂ : cst • f ∈ R.R₂.integers) :
    ∃ x x' : ↥(R.nodeIntegersOver K w), R.nodeResidue₁ w ⟨x', x'.2.1⟩ ≠ 0 ∧ R.nodeResidue₂ w ⟨x', x'.2.1⟩ ≠ 0 ∧
      (cst • f) * (x' : ↥(modularFunctionFieldBar (N * q))) = x := by
  obtain ⟨x, y, hx, hy, hy0, hxyL⟩ := hfrac _ (smul_mem_fieldOver K f hfK cst hcst)
  have hxyF : (cst • f) * y = x := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul]
    exact hxyL
  have hy0' : (⟨y, hy⟩ : ↥(R.nodeIntegersOver K w)) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  obtain ⟨a₁, b₁, hb₁, hab₁⟩ :=
    R.exists_mul_eq_of_mem_integers_nodeResidueFst_ne_zero K w c ϖ hϖ hmax hbr E hE u hu hxy ⟨x, hx⟩ ⟨y, hy⟩ hy0' (cst • f) hz₁ hxyF
  obtain ⟨a₂, b₂, hb₂, hab₂⟩ :=
    R.exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero K w c ϖ hϖ hmax hbr E hE u hu hxy ⟨x, hx⟩ ⟨y, hy⟩ hy0' (cst • f) hz₂ hxyF
  by_cases h12 : R.nodeResidue₂ w ⟨b₁, b₁.2.1⟩ = 0
  · by_cases h21 : R.nodeResidue₁ w ⟨b₂, b₂.2.1⟩ = 0
    ·
      have e : (⟨((b₁ + b₂ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))), (b₁ + b₂).2.1⟩ :
          ↥(R.nodeIntegers w)) = ⟨b₁, b₁.2.1⟩ + ⟨b₂, b₂.2.1⟩ := Subtype.ext rfl
      refine ⟨a₁ + a₂, b₁ + b₂, ?_, ?_, ?_⟩
      · rw [e, map_add, h21, add_zero]; exact hb₁
      · rw [e, map_add, h12, zero_add]; exact hb₂
      · rw [Subring.coe_add, Subring.coe_add, mul_add, hab₁, hab₂]
    · exact ⟨a₂, b₂, h21, hb₂, hab₂⟩
  · exact ⟨a₁, b₁, hb₁, h12, hab₁⟩

set_option maxHeartbeats 3200000 in

private theorem rep_smul_fst (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w) [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (f : ↥(modularFunctionFieldBar (N * q))) (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K)
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    (c₁ : AlgebraicClosure ℚ) (hc₁ : c₁ ∈ K) (h₁ : c₁ • f ∈ R.R₁.integers) (hu₁ : R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0) :
    ∃ a b : ↥(R.nodeIntegersOver K w), R.nodeResidue₁ w ⟨a, a.2.1⟩ ≠ 0 ∧ R.nodeResidue₁ w ⟨b, b.2.1⟩ ≠ 0 ∧
      (c₁ • f) * (b : ↥(modularFunctionFieldBar (N * q))) = a := by
  obtain ⟨x, y, hx, hy, hy0, hxyL⟩ := hfrac _ (smul_mem_fieldOver K f hfK c₁ hc₁)
  have hxyF : (c₁ • f) * y = x := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul]
    exact hxyL
  obtain ⟨a', b', hb', hab'⟩ :=
    R.exists_mul_eq_of_mem_integers_nodeResidueFst_ne_zero K w c ϖ hϖ hmax hbr E hE u hu hxy ⟨x, hx⟩ ⟨y, hy⟩
      (fun h => hy0 (congrArg Subtype.val h)) (c₁ • f) h₁ hxyF
  refine ⟨a', b', ?_, hb', hab'⟩

  have hmul : (⟨(a' : ↥(modularFunctionFieldBar (N * q))), a'.2.1.1⟩ : ↥R.R₁.integers) =
      ⟨c₁ • f, h₁⟩ * ⟨(b' : ↥(modularFunctionFieldBar (N * q))), b'.2.1.1⟩ := Subtype.ext hab'.symm
  intro h0
  have : R.residue₁ ⟨(a' : ↥(modularFunctionFieldBar (N * q))), a'.2.1.1⟩ = 0 := h0
  rw [hmul, map_mul, mul_eq_zero] at this
  rcases this with h | h
  · exact hu₁ (by
      have := h
      rwa [ProlongationTuple.residue₁_apply, map_eq_zero_iff _ R.ι.injective] at this)
  · exact hb' h

set_option maxHeartbeats 3200000 in

private theorem rep_smul_snd (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w) [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (f : ↥(modularFunctionFieldBar (N * q))) (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K)
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    (c₁ : AlgebraicClosure ℚ) (hc₁ : c₁ ∈ K) (h₁ : c₁ • f ∈ R.R₂.integers) (hu₁ : R.R₂.residue ⟨c₁ • f, h₁⟩ ≠ 0) :
    ∃ a b : ↥(R.nodeIntegersOver K w), R.nodeResidue₂ w ⟨a, a.2.1⟩ ≠ 0 ∧ R.nodeResidue₂ w ⟨b, b.2.1⟩ ≠ 0 ∧
      (c₁ • f) * (b : ↥(modularFunctionFieldBar (N * q))) = a := by
  obtain ⟨x, y, hx, hy, hy0, hxyL⟩ := hfrac _ (smul_mem_fieldOver K f hfK c₁ hc₁)
  have hxyF : (c₁ • f) * y = x := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul]
    exact hxyL
  obtain ⟨a', b', hb', hab'⟩ :=
    R.exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero K w c ϖ hϖ hmax hbr E hE u hu hxy ⟨x, hx⟩ ⟨y, hy⟩
      (fun h => hy0 (congrArg Subtype.val h)) (c₁ • f) h₁ hxyF
  refine ⟨a', b', ?_, hb', hab'⟩

  have hmul : (⟨(a' : ↥(modularFunctionFieldBar (N * q))), a'.2.1.2.1⟩ : ↥R.R₂.integers) =
      ⟨c₁ • f, h₁⟩ * ⟨(b' : ↥(modularFunctionFieldBar (N * q))), b'.2.1.2.1⟩ := Subtype.ext hab'.symm
  intro h0
  have : R.residue₂ ⟨(a' : ↥(modularFunctionFieldBar (N * q))), a'.2.1.2.1⟩ = 0 := h0
  rw [hmul, map_mul, mul_eq_zero] at this
  rcases this with h | h
  · exact hu₁ (by
      have := h
      rwa [ProlongationTuple.residue₂_apply, map_eq_zero_iff _ R.ι.injective] at this)
  · exact hb' h

end RepSmul

section ExpB
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

set_option maxHeartbeats 3200000 in

private theorem valuation_const_eq_of_smul_isUnit_fst (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N))
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : ϖ ≠ 0)
    (f : ↥(modularFunctionFieldBar (N * q))) (cst : AlgebraicClosure ℚ) (hcst0 : cst ≠ 0)
    (hz : cst • f ∈ R.R₁.integers) (hzu : R.R₁.residue ⟨cst • f, hz⟩ ≠ 0)
    (a b s t s' t' : ↥(R.nodeIntegersOver K w)) (hb : b ≠ 0)
    (hfab : f * (b : ↥(modularFunctionFieldBar (N * q))) = a)
    (ma mb : ℕ) (hfa : a * s = R.nodeConst K w ϖ ^ ma * t) (hfb : b * s' = R.nodeConst K w ϖ ^ mb * t')
    (hs : R.nodeResidue₁ w ⟨s, s.2.1⟩ ≠ 0) (ht : R.nodeResidue₁ w ⟨t, t.2.1⟩ ≠ 0)
    (hs' : R.nodeResidue₁ w ⟨s', s'.2.1⟩ ≠ 0) (ht' : R.nodeResidue₁ w ⟨t', t'.2.1⟩ ≠ 0) :
    A.valuation cst * A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ ma =
      A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ mb := by

  have hunit : ∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0 →
      R.R₁.integers.valuation (g : ↥(modularFunctionFieldBar (N * q))) = 1 := by
    intro g hg
    have hg' : R.R₁.residue ⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.1.1⟩ ≠ 0 := by
      intro h0
      apply hg
      rw [ProlongationTuple.nodeResidue₁_apply, ProlongationTuple.residue₁_apply]
      exact (congrArg R.ι h0).trans (map_zero _)
    exact (R.R₁.integers.valuation_eq_one_iff _).mp (R.R₁.isUnit_of_residue_ne_zero hg')

  have bridge : ∀ x y : AlgebraicClosure ℚ, y ≠ 0 →
      R.R₁.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) x) ≤ R.R₁.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) y) →
        A.valuation x ≤ A.valuation y := by
    intro x y hy hle
    have hy' : R.R₁.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) y) ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero _).mpr hy)
    have h1 : R.R₁.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) (x / y)) ≤ 1 := by
      rw [map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.mpr hy')]; exact hle
    have h2 : x / y ∈ A := (R.R₁.algebraMap_mem_iff _).mp ((R.R₁.integers.valuation_le_one_iff _).mp h1)
    have h3 : A.valuation (x / y) ≤ 1 := (A.valuation_le_one_iff _).mpr h2
    rwa [map_div₀, div_le_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hy))] at h3

  have hcf : (cst • f : ↥(modularFunctionFieldBar (N * q))) = algebraMap _ ↥(modularFunctionFieldBar (N * q)) cst * f := Algebra.smul_def cst f
  have hfa' := congrArg (fun z : ↥(R.nodeIntegersOver K w) => (z : ↥(modularFunctionFieldBar (N * q)))) hfa
  have hfb' := congrArg (fun z : ↥(R.nodeIntegersOver K w) => (z : ↥(modularFunctionFieldBar (N * q)))) hfb
  simp only [Subring.coe_mul, Subring.coe_pow, ProlongationTuple.coe_nodeConst] at hfa' hfb'
  have hv1 : R.R₁.integers.valuation (cst • f : ↥(modularFunctionFieldBar (N * q))) = 1 :=
    (R.R₁.integers.valuation_eq_one_iff ⟨cst • f, hz⟩).mp (R.R₁.isUnit_of_residue_ne_zero hzu)

  have hva : R.R₁.integers.valuation (a : ↥(modularFunctionFieldBar (N * q))) = R.R₁.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)) ^ ma := by
    have := congrArg R.R₁.integers.valuation hfa'
    rwa [map_mul, map_mul, map_pow, hunit s hs, hunit t ht, mul_one, mul_one] at this
  have hvb : R.R₁.integers.valuation (b : ↥(modularFunctionFieldBar (N * q))) = R.R₁.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)) ^ mb := by
    have := congrArg R.R₁.integers.valuation hfb'
    rwa [map_mul, map_mul, map_pow, hunit s' hs', hunit t' ht', mul_one, mul_one] at this
  have hkey : R.R₁.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) (cst * (ϖ : AlgebraicClosure ℚ) ^ ma)) =
      R.R₁.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) ((ϖ : AlgebraicClosure ℚ) ^ mb)) := by
    have h := congrArg R.R₁.integers.valuation (show algebraMap _ ↥(modularFunctionFieldBar (N * q)) cst * (a : ↥(modularFunctionFieldBar (N * q))) = (cst • f) * b by
      rw [hcf, mul_assoc, hfab])
    rw [map_mul, map_mul, hv1, one_mul, hva, hvb] at h
    rw [map_mul, map_pow, map_mul, map_pow, map_pow, map_pow]; exact h
  have hϖ0' : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := fun h => hϖ0 (Subtype.ext h)
  have hx0 : cst * (ϖ : AlgebraicClosure ℚ) ^ ma ≠ 0 := mul_ne_zero hcst0 (pow_ne_zero _ hϖ0')
  have hy0 : (ϖ : AlgebraicClosure ℚ) ^ mb ≠ 0 := pow_ne_zero _ hϖ0'
  have heq : A.valuation (cst * (ϖ : AlgebraicClosure ℚ) ^ ma) = A.valuation ((ϖ : AlgebraicClosure ℚ) ^ mb) :=
    le_antisymm (bridge _ _ hy0 hkey.le) (bridge _ _ hx0 hkey.ge)
  rwa [map_mul, map_pow, map_pow] at heq

set_option maxHeartbeats 3200000 in

private theorem valuation_const_eq_of_smul_isUnit_snd (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N))
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : ϖ ≠ 0)
    (f : ↥(modularFunctionFieldBar (N * q))) (cst : AlgebraicClosure ℚ) (hcst0 : cst ≠ 0)
    (hz : cst • f ∈ R.R₂.integers) (hzu : R.R₂.residue ⟨cst • f, hz⟩ ≠ 0)
    (a b s t s' t' : ↥(R.nodeIntegersOver K w)) (hb : b ≠ 0)
    (hfab : f * (b : ↥(modularFunctionFieldBar (N * q))) = a)
    (ma mb : ℕ) (hfa : a * s = R.nodeConst K w ϖ ^ ma * t) (hfb : b * s' = R.nodeConst K w ϖ ^ mb * t')
    (hs : R.nodeResidue₂ w ⟨s, s.2.1⟩ ≠ 0) (ht : R.nodeResidue₂ w ⟨t, t.2.1⟩ ≠ 0)
    (hs' : R.nodeResidue₂ w ⟨s', s'.2.1⟩ ≠ 0) (ht' : R.nodeResidue₂ w ⟨t', t'.2.1⟩ ≠ 0) :
    A.valuation cst * A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ ma =
      A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ mb := by

  have hunit : ∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₂ w ⟨g, g.2.1⟩ ≠ 0 →
      R.R₂.integers.valuation (g : ↥(modularFunctionFieldBar (N * q))) = 1 := by
    intro g hg
    have hg' : R.R₂.residue ⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.1.2.1⟩ ≠ 0 := by
      intro h0
      apply hg
      rw [ProlongationTuple.nodeResidue₂_apply, ProlongationTuple.residue₂_apply]
      exact (congrArg R.ι h0).trans (map_zero _)
    exact (R.R₂.integers.valuation_eq_one_iff _).mp (R.R₂.isUnit_of_residue_ne_zero hg')

  have bridge : ∀ x y : AlgebraicClosure ℚ, y ≠ 0 →
      R.R₂.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) x) ≤ R.R₂.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) y) →
        A.valuation x ≤ A.valuation y := by
    intro x y hy hle
    have hy' : R.R₂.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) y) ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero _).mpr hy)
    have h1 : R.R₂.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) (x / y)) ≤ 1 := by
      rw [map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.mpr hy')]; exact hle
    have h2 : x / y ∈ A := (R.R₂.algebraMap_mem_iff _).mp ((R.R₂.integers.valuation_le_one_iff _).mp h1)
    have h3 : A.valuation (x / y) ≤ 1 := (A.valuation_le_one_iff _).mpr h2
    rwa [map_div₀, div_le_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hy))] at h3

  have hcf : (cst • f : ↥(modularFunctionFieldBar (N * q))) = algebraMap _ ↥(modularFunctionFieldBar (N * q)) cst * f := Algebra.smul_def cst f
  have hfa' := congrArg (fun z : ↥(R.nodeIntegersOver K w) => (z : ↥(modularFunctionFieldBar (N * q)))) hfa
  have hfb' := congrArg (fun z : ↥(R.nodeIntegersOver K w) => (z : ↥(modularFunctionFieldBar (N * q)))) hfb
  simp only [Subring.coe_mul, Subring.coe_pow, ProlongationTuple.coe_nodeConst] at hfa' hfb'
  have hv1 : R.R₂.integers.valuation (cst • f : ↥(modularFunctionFieldBar (N * q))) = 1 :=
    (R.R₂.integers.valuation_eq_one_iff ⟨cst • f, hz⟩).mp (R.R₂.isUnit_of_residue_ne_zero hzu)

  have hva : R.R₂.integers.valuation (a : ↥(modularFunctionFieldBar (N * q))) = R.R₂.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)) ^ ma := by
    have := congrArg R.R₂.integers.valuation hfa'
    rwa [map_mul, map_mul, map_pow, hunit s hs, hunit t ht, mul_one, mul_one] at this
  have hvb : R.R₂.integers.valuation (b : ↥(modularFunctionFieldBar (N * q))) = R.R₂.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)) ^ mb := by
    have := congrArg R.R₂.integers.valuation hfb'
    rwa [map_mul, map_mul, map_pow, hunit s' hs', hunit t' ht', mul_one, mul_one] at this
  have hkey : R.R₂.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) (cst * (ϖ : AlgebraicClosure ℚ) ^ ma)) =
      R.R₂.integers.valuation (algebraMap _ ↥(modularFunctionFieldBar (N * q)) ((ϖ : AlgebraicClosure ℚ) ^ mb)) := by
    have h := congrArg R.R₂.integers.valuation (show algebraMap _ ↥(modularFunctionFieldBar (N * q)) cst * (a : ↥(modularFunctionFieldBar (N * q))) = (cst • f) * b by
      rw [hcf, mul_assoc, hfab])
    rw [map_mul, map_mul, hv1, one_mul, hva, hvb] at h
    rw [map_mul, map_pow, map_mul, map_pow, map_pow, map_pow]; exact h
  have hϖ0' : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := fun h => hϖ0 (Subtype.ext h)
  have hx0 : cst * (ϖ : AlgebraicClosure ℚ) ^ ma ≠ 0 := mul_ne_zero hcst0 (pow_ne_zero _ hϖ0')
  have hy0 : (ϖ : AlgebraicClosure ℚ) ^ mb ≠ 0 := pow_ne_zero _ hϖ0'
  have heq : A.valuation (cst * (ϖ : AlgebraicClosure ℚ) ^ ma) = A.valuation ((ϖ : AlgebraicClosure ℚ) ^ mb) :=
    le_antisymm (bridge _ _ hy0 hkey.le) (bridge _ _ hx0 hkey.ge)
  rwa [map_mul, map_pow, map_pow] at heq

end ExpB

section ExpA
p2m_open "ModularCurve.UVCrossingModel P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve.UVCrossingModel"
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem gaussOrder_one {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (π : W) (hπ : π ∈ maximalIdeal W) (e t : ℕ) :
    gaussOrder (IsDiscreteValuationRing.addVal W) π e t (1 : UVCrossingModel W π) = 0 := by
  refine le_antisymm ((UVCrossingModel.gaussOrder_le_iff _ _ _ _ _ _).mpr fun F hF => ?_) bot_le

  have hF1 : F - 1 ∈ uvCrossingIdeal W π := by
    rw [← Ideal.Quotient.eq]; exact hF.trans (map_one _).symm
  obtain ⟨G, hG⟩ := Ideal.mem_span_singleton'.mp hF1
  have hc : MvPowerSeries.constantCoeff F = 1 - π * MvPowerSeries.constantCoeff G := by
    have h := congrArg MvPowerSeries.constantCoeff hG
    simp only [map_mul, map_sub, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, map_one,
      mul_zero, zero_sub] at h

    linear_combination -h
  have hunit : IsUnit (MvPowerSeries.constantCoeff F) := by
    rw [hc]
    by_contra hnu
    have hmem : 1 - π * MvPowerSeries.constantCoeff G ∈ maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have : (1 : W) ∈ maximalIdeal W := by
      have h2 := Ideal.add_mem _ hmem (Ideal.mul_mem_right (MvPowerSeries.constantCoeff G) _ hπ)
      rwa [sub_add_cancel] at h2
    exact (Ideal.ne_top_iff_one _).mp (Ideal.IsMaximal.ne_top (IsLocalRing.maximalIdeal.isMaximal W)) this
  calc UVCrossingModel.repGaussOrder (IsDiscreteValuationRing.addVal W) e t F
      ≤ IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) F) + (UVCrossingModel.annulusWeight e t 0 : ℕ∞) :=
        UVCrossingModel.repGaussOrder_le _ _ _ _ _
    _ = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, show MvPowerSeries.constantCoeff F = (hunit.unit : W) from rfl,
          IsDiscreteValuationRing.addVal_eq_zero_of_unit hunit.unit]
        simp [UVCrossingModel.annulusWeight]

set_option maxHeartbeats 3200000 in

private theorem gaussOrder_fst_end_eq_of_mul_eq_nodeConst_pow_mul (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N))
    [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E : ℕ) (hE : 1 ≤ E)
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = UVCrossingModel.const (π ^ E) π)
    (hord : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨f, f.2.1⟩ ≠ 0 →
        w.ord (R.nodeResidue₁ w ⟨f, f.2.1⟩) = (n : ℤ) →
        ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * UVCrossingModel.V (π ^ E) ^ n ∈
          Ideal.span {UVCrossingModel.const (π ^ E) π, UVCrossingModel.U (π ^ E)})
    (a s t : ↥(R.nodeIntegersOver K w)) (ma : ℕ) (hfa : a * s = R.nodeConst K w ϖ ^ ma * t)
    (ns nt : ℕ) (hs : R.nodeResidue₁ w ⟨s, s.2.1⟩ ≠ 0) (hns : w.ord (R.nodeResidue₁ w ⟨s, s.2.1⟩) = (ns : ℤ))
    (ht : R.nodeResidue₁ w ⟨t, t.2.1⟩ ≠ 0) (hnt : w.ord (R.nodeResidue₁ w ⟨t, t.2.1⟩) = (nt : ℤ)) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (π ^ E) E E (ι (algebraMap _ _ a)) = ma := by
  have e1 := ModularCurve.PlaceSpecialization.ProlongationTuple.gaussOrder_fst_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul
    R K w ϖ E hE π hπ ι hιϖ hord (a * s) 1 t nt ht hnt ma (by rw [mul_one]; exact hfa)
  have e2 := ModularCurve.PlaceSpecialization.ProlongationTuple.gaussOrder_fst_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul
    R K w ϖ E hE π hπ ι hιϖ hord (a * s) a s ns hs hns 0 (by rw [pow_zero, one_mul]; exact mul_comm a s)
  have hπE : π ^ E ∈ maximalIdeal W :=
    Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit) _ (Nat.one_le_iff_ne_zero.mp hE |> Nat.pos_of_ne_zero)
  have h1 : gaussOrder (IsDiscreteValuationRing.addVal W) (π ^ E) E E (ι (algebraMap _ _ (1 : ↥(R.nodeIntegersOver K w)))) = 0 := by
    rw [map_one, map_one]; exact gaussOrder_one (π ^ E) hπE E E
  rw [h1, add_zero] at e1
  rw [e1, Nat.cast_zero, zero_add] at e2
  exact e2.symm

set_option maxHeartbeats 3200000 in

private theorem gaussOrder_snd_end_eq_of_mul_eq_nodeConst_pow_mul (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N))
    [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E : ℕ) (hE : 1 ≤ E)
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = UVCrossingModel.const (π ^ E) π)
    (hord : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨f, f.2.1⟩ ≠ 0 →
        (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨f, f.2.1⟩) = (n : ℤ) →
        ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * UVCrossingModel.U (π ^ E) ^ n ∈
          Ideal.span {UVCrossingModel.const (π ^ E) π, UVCrossingModel.V (π ^ E)})
    (a s t : ↥(R.nodeIntegersOver K w)) (ma : ℕ) (hfa : a * s = R.nodeConst K w ϖ ^ ma * t)
    (ns nt : ℕ) (hs : R.nodeResidue₂ w ⟨s, s.2.1⟩ ≠ 0) (hns : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨s, s.2.1⟩) = (ns : ℤ))
    (ht : R.nodeResidue₂ w ⟨t, t.2.1⟩ ≠ 0) (hnt : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨t, t.2.1⟩) = (nt : ℤ)) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (π ^ E) E 0 (ι (algebraMap _ _ a)) = ma := by
  have e1 := ModularCurve.PlaceSpecialization.ProlongationTuple.gaussOrder_snd_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul
    R K w ϖ E hE π hπ ι hιϖ hord (a * s) 1 t nt ht hnt ma (by rw [mul_one]; exact hfa)
  have e2 := ModularCurve.PlaceSpecialization.ProlongationTuple.gaussOrder_snd_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul
    R K w ϖ E hE π hπ ι hιϖ hord (a * s) a s ns hs hns 0 (by rw [pow_zero, one_mul]; exact mul_comm a s)
  have hπE : π ^ E ∈ maximalIdeal W :=
    Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit) _ (Nat.one_le_iff_ne_zero.mp hE |> Nat.pos_of_ne_zero)
  have h1 : gaussOrder (IsDiscreteValuationRing.addVal W) (π ^ E) E 0 (ι (algebraMap _ _ (1 : ↥(R.nodeIntegersOver K w)))) = 0 := by
    rw [map_one, map_one]; exact gaussOrder_one (π ^ E) hπE E 0
  rw [h1, add_zero] at e1
  rw [e1, Nat.cast_zero, zero_add] at e2
  exact e2.symm

end ExpA

section PlaceSplit
open Classical in
set_option maxHeartbeats 1600000 in

private theorem sum_support_filter_eq_sum_ord_sub_sum_ord
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (f x x' : F) (hx : x ≠ 0) (hx' : x' ≠ 0) (hfx : f * x' = x)
    (D : Divisor K F) (hDf : ∀ V, D V = V.ord f)
    (Pr : Place K F → Prop)
    (Tx Tx' : Finset (Place K F))
    (hTx : ∀ V, V ∈ Tx ↔ (V.ord x ≠ 0 ∧ Pr V)) (hTx' : ∀ V, V ∈ Tx' ↔ (V.ord x' ≠ 0 ∧ Pr V)) :
    (∑ V ∈ D.support with Pr V, D V) = (∑ V ∈ Tx, V.ord x) - ∑ V ∈ Tx', V.ord x' := by
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hfx
    exact hx hfx.symm
  have hordf : ∀ V : Place K F, V.ord f = V.ord x - V.ord x' := fun V => by
    have h := V.ord_mul hf0 hx'
    rw [hfx] at h
    linarith
  have h1 : (∑ V ∈ D.support with Pr V, D V) = ∑ V ∈ (D.support ∪ Tx ∪ Tx') with Pr V, D V := by
    apply Finset.sum_subset (Finset.filter_subset_filter _ (Finset.subset_union_left.trans Finset.subset_union_left))
    intro V hV hVn
    rw [Finset.mem_filter] at hV hVn
    by_contra h
    exact hVn ⟨Finsupp.mem_support_iff.mpr h, hV.2⟩
  have h2 : (∑ V ∈ Tx, V.ord x) = ∑ V ∈ (D.support ∪ Tx ∪ Tx') with Pr V, V.ord x := by
    apply Finset.sum_subset
    · intro V hV
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hV), ((hTx V).mp hV).2⟩
    · intro V hV hVn
      rw [Finset.mem_filter] at hV
      by_contra h
      exact hVn ((hTx V).mpr ⟨h, hV.2⟩)
  have h3 : (∑ V ∈ Tx', V.ord x') = ∑ V ∈ (D.support ∪ Tx ∪ Tx') with Pr V, V.ord x' := by
    apply Finset.sum_subset
    · intro V hV
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_union_right _ hV, ((hTx' V).mp hV).2⟩
    · intro V hV hVn
      rw [Finset.mem_filter] at hV
      by_contra h
      exact hVn ((hTx' V).mpr ⟨h, hV.2⟩)
  rw [h1, h2, h3, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun V _ => by rw [hDf V, hordf V]

end PlaceSplit

section Slope1
p2m_open "ModularCurve.UVCrossingModel P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve.UVCrossingModel"
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem ord_nonneg_of_reduceFst_eq (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (z : ↥(R.nodeIntegersOver K w))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) : 0 ≤ V.ord (z : ↥(modularFunctionFieldBar (N * q))) := by
  have hmem : (z : ↥(modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring := z.2.1.2.2 V hV
  by_contra hlt
  exact (V.not_adicValuation_le_one_iff.mpr (lt_of_not_ge hlt)) (V.mem_iff_adicValuation_le_one.mp hmem)

open Classical in
set_option maxHeartbeats 6400000 in

private theorem circleIndexDrop_sub_eq_sum_div_of_total_eq (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hwss : w ∈ ssPlaces q N k) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w)
    (hv0 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0)
    (hv1 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) < 1)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    (ew eK : ℕ) (hew : 1 ≤ ew) (heK : 1 ≤ eK) (hEeq : E = ew * eK) (e' : ℕ) (he' : 1 ≤ e')

    (fc : ↥(modularFunctionFieldBar (N * q))) (a b : ↥(R.nodeIntegersOver K w)) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hfab : fc * (b : ↥(modularFunctionFieldBar (N * q))) = a)
    (hιa : ι (algebraMap _ _ a) ≠ 0) (hιb : ι (algebraMap _ _ b) ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hab2 : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (π ^ E) (inU ab.1 + inV ab.2) = ι (algebraMap _ _ a))
    (ab' : PowerSeries W × PowerSeries W) (hab'2 : PowerSeries.constantCoeff ab'.2 = 0)
    (habx' : mk (π ^ E) (inU ab'.1 + inV ab'.2) = ι (algebraMap _ _ b))

    (Ta : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hTa : ∀ V, V ∈ Ta ↔ (V.ord ((a : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w))
    (htota : ((∑ V ∈ Ta, (V.ord ((a : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) =
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ a)})))
    (Tb : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hTb : ∀ V, V ∈ Tb ↔ (V.ord ((b : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w))
    (htotb : ((∑ V ∈ Tb, (V.ord ((b : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) =
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ b)})))

    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : ∀ V, D V = V.ord fc)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
    (hgrid : ∀ V ∈ D.support, P.reduceFst V = w →
      depth V ≤ e' * ew ∧ c.xDepth V ^ e' = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ (e' * E - depth V * eK)) :
    (∀ r s : ℕ, 1 ≤ r → 0 < s → s < r * (e' * E) → (¬ ∃ d, d ≤ e' * ew ∧ s = r * (e' * E - d * eK)) →
        circleIndexDrop (fun w => ((r * e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * e' * E) s ab =
          circleIndexDrop (fun w => ((r * e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * e' * E) s ab') ∧
    (∀ d ∈ Finset.Ico 1 (e' * ew), (circleIndexDrop (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * E) (e' * E - d * eK) ab : ℤ)
          - circleIndexDrop (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * E) (e' * E - d * eK) ab' =
        ∑ V ∈ D.support with (P.reduceFst V = w ∧ depth V = d), D V) := by
  classical

  haveI hCurveBar : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    isCurveOver_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) (N * q)
  have ha0' : (a : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h => ha0 (Subtype.ext h)
  have hb0' : (b : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h => hb0 (Subtype.ext h)
  obtain ⟨Da, hDa, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldBar (N * q))) ha0'
  obtain ⟨Db, hDb, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (b : ↥(modularFunctionFieldBar (N * q))) hb0'

  have hpow : ∀ m n : ℕ, A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ m =
      A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ n → m = n := by
    intro m n h
    have hinj := zpow_right_injective₀ (zero_lt_iff.mpr hv0) hv1.ne
    exact_mod_cast (hinj (by simp only [zpow_natCast]; exact h) : (m : ℤ) = n)

  have hchain : ∀ (qq s : ℕ), 1 ≤ qq → 1 ≤ s → s + 1 ≤ qq * E →
      ((circleIndexDrop (fun w => ((qq : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (qq * E) s ab : ℤ) =
          ∑ V ∈ Da.support with (P.reduceFst V = w ∧ c.xDepth V ^ qq =
              A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ s), V.ord (a : ↥(modularFunctionFieldBar (N * q)))) ∧
      ((circleIndexDrop (fun w => ((qq : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (qq * E) s ab' : ℤ) =
          ∑ V ∈ Db.support with (P.reduceFst V = w ∧ c.xDepth V ^ qq =
              A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ s), V.ord (b : ↥(modularFunctionFieldBar (N * q)))) := by
    intro qq s hqq hs1 hsE
    constructor
    · have hP2 := ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_eq_finsum_rank_mul_length_of_total_eq
        R K w c ϖ hmax hres hVI hwss π hπ E hE ι hιϖ αU hαU hιx a ha0 Ta hTa htota qq hqq s hs1 hsE
        (Da.support.filter fun V => P.reduceFst V = w ∧ c.xDepth V ^ qq =
          A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ s)
        (fun V => by rw [Finset.mem_filter, Finsupp.mem_support_iff, hDa V])
      have hP1 := ModularCurve.UVCrossingModel.finsum_rank_mul_length_eq_circleIndexDrop π hπ E hE qq hqq
        (ι (algebraMap _ _ a)) hιa ab hab2 habx s hs1 hsE
      have hnat := ENat.coe_inj.mp (hP2.trans hP1)
      rw [← hnat, Nat.cast_sum]
      refine Finset.sum_congr rfl fun V hV => Int.toNat_of_nonneg (ord_nonneg_of_reduceFst_eq R K w a V ?_)
      exact (Finset.mem_filter.mp hV).2.1
    · have hP2 := ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_eq_finsum_rank_mul_length_of_total_eq
        R K w c ϖ hmax hres hVI hwss π hπ E hE ι hιϖ αU hαU hιx b hb0 Tb hTb htotb qq hqq s hs1 hsE
        (Db.support.filter fun V => P.reduceFst V = w ∧ c.xDepth V ^ qq =
          A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ s)
        (fun V => by rw [Finset.mem_filter, Finsupp.mem_support_iff, hDb V])
      have hP1 := ModularCurve.UVCrossingModel.finsum_rank_mul_length_eq_circleIndexDrop π hπ E hE qq hqq
        (ι (algebraMap _ _ b)) hιb ab' hab'2 habx' s hs1 hsE
      have hnat := ENat.coe_inj.mp (hP2.trans hP1)
      rw [← hnat, Nat.cast_sum]
      refine Finset.sum_congr rfl fun V hV => Int.toNat_of_nonneg (ord_nonneg_of_reduceFst_eq R K w b V ?_)
      exact (Finset.mem_filter.mp hV).2.1

  have hsplit : ∀ (qq s : ℕ), 1 ≤ qq → 1 ≤ s → s + 1 ≤ qq * E →
      (circleIndexDrop (fun w => ((qq : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (qq * E) s ab : ℤ) - (circleIndexDrop (fun w => ((qq : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (qq * E) s ab' : ℤ) =
        ∑ V ∈ D.support with (P.reduceFst V = w ∧ c.xDepth V ^ qq =
            A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ s), D V := by
    intro qq s hqq hs1 hsE
    obtain ⟨h1, h2⟩ := hchain qq s hqq hs1 hsE
    rw [h1, h2]
    convert (sum_support_filter_eq_sum_ord_sub_sum_ord fc (a : ↥(modularFunctionFieldBar (N * q))) (b : ↥(modularFunctionFieldBar (N * q))) ha0' hb0' hfab D hD _
      (Da.support.filter fun V => P.reduceFst V = w ∧ c.xDepth V ^ qq =
          A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ s)
      (Db.support.filter fun V => P.reduceFst V = w ∧ c.xDepth V ^ qq =
          A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ s)
      (fun V => by rw [Finset.mem_filter, Finsupp.mem_support_iff, hDa V])
      (fun V => by rw [Finset.mem_filter, Finsupp.mem_support_iff, hDb V])).symm using 2
    congr 1 <;> exact Subsingleton.elim _ _
  have he'0 : e' ≠ 0 := by omega
  have hE' : e' * E = e' * ew * eK := by rw [hEeq, Nat.mul_assoc]
  have hgrid' : ∀ V ∈ D.support, P.reduceFst V = w → ∀ qq s : ℕ,
      c.xDepth V ^ qq = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ s → s * e' = qq * (e' * E - depth V * eK) := by
    intro V hV hVw qq s h
    obtain ⟨-, hx⟩ := hgrid V hV hVw
    have h2 : (c.xDepth V ^ qq) ^ e' = (c.xDepth V ^ e') ^ qq := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [h, hx, ← pow_mul, ← pow_mul] at h2
    exact (hpow _ _ h2).trans (Nat.mul_comm _ _)
  refine ⟨fun r s hr hs hsr hoff => ?_, fun d hd => ?_⟩
  · have hr1 : 1 ≤ r * e' := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) he'0)
    have hsE : s + 1 ≤ r * e' * E := by rw [Nat.mul_assoc]; exact hsr
    have h := hsplit (r * e') s hr1 hs hsE
    rw [Finset.sum_eq_zero (fun V hV => ?_), sub_eq_zero] at h
    · exact_mod_cast h
    · exfalso
      obtain ⟨hVD, hVw, hVx⟩ := Finset.mem_filter.mp hV
      refine hoff ⟨depth V, (hgrid V hVD hVw).1, ?_⟩
      have h1 := hgrid' V hVD hVw (r * e') s hVx
      have h2 : s * e' = (r * (e' * E - depth V * eK)) * e' := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_right (by omega) h2
  · obtain ⟨hd1, hdN⟩ := Finset.mem_Ico.mp hd
    have hdE : d * eK + eK ≤ e' * E := by
      have h := Nat.mul_le_mul_right eK (Nat.succ_le_of_lt hdN)
      rw [Nat.succ_mul] at h
      rw [hE']; exact h
    have hh : 1 ≤ d * eK := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hs1 : 1 ≤ e' * E - d * eK := by omega
    have hsE : e' * E - d * eK + 1 ≤ e' * E := by omega
    rw [hsplit e' (e' * E - d * eK) he' hs1 hsE]
    refine Finset.sum_congr (Finset.filter_congr fun V hV => ?_) fun _ _ => rfl
    refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
    · have h2 := hgrid' V hV h.1 e' (e' * E - d * eK) h.2
      have h3 : e' * E - d * eK = e' * E - depth V * eK := by
        have h4 : (e' * E - d * eK) * e' = (e' * E - depth V * eK) * e' := by rw [h2]; ring
        exact Nat.eq_of_mul_eq_mul_right (by omega) h4
      have hle := (hgrid V hV h.1).1
      have hdep : depth V * eK ≤ e' * E := by rw [hE']; exact Nat.mul_le_mul_right _ hle
      have hdk : d * eK ≤ e' * E := by omega
      have : depth V * eK = d * eK := by
        rw [← Nat.sub_sub_self hdep, ← h3, Nat.sub_sub_self hdk]
      exact Nat.eq_of_mul_eq_mul_right heK this
    · obtain ⟨-, hx⟩ := hgrid V hV h.1
      rw [hx, h.2]

private theorem depth_window {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {x y vϖ vq vε : Γ₀} {eK ew d : ℕ}
    (hx1 : x < 1) (hy1 : y < 1) (hprod : x * y = vϖ ^ (ew * eK)) (hy : y = vq ^ d)
    (hvq : vq = vϖ ^ eK * vε) (hvε : vε = 1) (hle : vϖ ≤ 1) (hne : vϖ ≠ 0) : 0 < d ∧ d < ew := by
  rw [hvε, mul_one] at hvq
  rw [hvq, ← pow_mul] at hy
  refine ⟨Nat.pos_of_ne_zero fun hd => ?_, lt_of_not_ge fun hd => ?_⟩
  · rw [hd, mul_zero, pow_zero] at hy
    exact (lt_irrefl (1 : Γ₀)) (hy ▸ hy1)
  · have hy0 : y ≠ 0 := by rw [hy]; exact pow_ne_zero _ hne
    have h1 : x * y < y := by
      calc x * y < 1 * y := mul_lt_mul_of_pos_right hx1 (zero_lt_iff.mpr hy0)
        _ = y := one_mul y
    have h2 : y ≤ vϖ ^ (ew * eK) := by
      rw [hy]
      exact pow_le_pow_right_of_le_one' hle (by rw [Nat.mul_comm ew eK]; exact Nat.mul_le_mul_left eK hd)
    exact (lt_irrefl _) (lt_of_lt_of_le (hprod ▸ h1) h2)

private theorem grid_of_depth {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {x y vϖ vq vε : Γ₀} {eK ew d : ℕ}
    (hx1 : x < 1) (hy1 : y < 1) (hprod : x * y = vϖ ^ (ew * eK)) (hy : y = vq ^ d)
    (hvq : vq = vϖ ^ eK * vε) (hvε : vε = 1) (hle : vϖ ≤ 1) (hne : vϖ ≠ 0) :
    d < ew ∧ x = vϖ ^ (ew * eK - d * eK) := by
  obtain ⟨-, hdew⟩ := depth_window hx1 hy1 hprod hy hvq hvε hle hne
  refine ⟨hdew, ?_⟩
  rw [hvε, mul_one] at hvq
  rw [hvq, ← pow_mul] at hy
  have hy0 : y ≠ 0 := by rw [hy]; exact pow_ne_zero _ hne
  have hdk : d * eK ≤ ew * eK := Nat.mul_le_mul_right _ hdew.le
  apply mul_right_cancel₀ hy0
  rw [hprod, hy, ← pow_add, Nat.mul_comm eK d, Nat.sub_add_cancel hdk]

private theorem grid_of_depth_scaled {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {x y vϖ vq vε : Γ₀} {eK ew d e' : ℕ}
    (he' : 1 ≤ e') (hx1 : x < 1) (hprod : x * y = vϖ ^ (ew * eK)) (hy : y ^ e' = vq ^ d)
    (hvq : vq = vϖ ^ eK * vε) (hvε : vε = 1) (hle : vϖ ≤ 1) (hne : vϖ ≠ 0) :
    d ≤ e' * ew ∧ x ^ e' = vϖ ^ (e' * (ew * eK) - d * eK) := by
  rw [hvε, mul_one] at hvq
  rw [hvq, ← pow_mul] at hy
  have hprod' : x ^ e' * vϖ ^ (eK * d) = vϖ ^ (e' * (ew * eK)) := by
    rw [← hy, ← mul_pow, hprod, ← pow_mul, Nat.mul_comm]
  have hxe : x ^ e' < 1 := pow_lt_one' hx1 (by omega)
  have hyd0 : vϖ ^ (eK * d) ≠ 0 := pow_ne_zero _ hne
  have hdle : d ≤ e' * ew := by
    refine le_of_not_gt fun hd => ?_
    have h1 : x ^ e' * vϖ ^ (eK * d) < vϖ ^ (eK * d) := by
      calc x ^ e' * vϖ ^ (eK * d) < 1 * vϖ ^ (eK * d) := mul_lt_mul_of_pos_right hxe (zero_lt_iff.mpr hyd0)
        _ = vϖ ^ (eK * d) := one_mul _
    have h2 : vϖ ^ (eK * d) ≤ vϖ ^ (e' * (ew * eK)) := by
      refine pow_le_pow_right_of_le_one' hle ?_
      calc e' * (ew * eK) = eK * (e' * ew) := by ring
        _ ≤ eK * d := Nat.mul_le_mul_left eK hd.le
    exact (lt_irrefl _) (lt_of_lt_of_le (hprod' ▸ h1) h2)
  refine ⟨hdle, ?_⟩
  have hdk : d * eK ≤ e' * (ew * eK) := by
    calc d * eK ≤ (e' * ew) * eK := Nat.mul_le_mul_right _ hdle
      _ = e' * (ew * eK) := Nat.mul_assoc _ _ _
  apply mul_right_cancel₀ hyd0
  rw [hprod', ← pow_add, Nat.mul_comm eK d, Nat.sub_add_cancel hdk]

open Classical in
set_option maxHeartbeats 3200000 in

private theorem total_eq_of_sub_total (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) [IsLocalRing ↥(R.nodeIntegersOver K w)]
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) ≃+* UVCrossingModel W (π ^ E))
    (fc : ↥(modularFunctionFieldBar (N * q))) (a b : ↥(R.nodeIntegersOver K w)) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hfab : fc * (b : ↥(modularFunctionFieldBar (N * q))) = a)
    (hιa : ι (algebraMap _ _ a) ≠ 0) (hιb : ι (algebraMap _ _ b) ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hab2 : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (π ^ E) (inU ab.1 + inV ab.2) = ι (algebraMap _ _ a))
    (ab' : PowerSeries W × PowerSeries W) (hab'2 : PowerSeries.constantCoeff ab'.2 = 0)
    (habx' : mk (π ^ E) (inU ab'.1 + inV ab'.2) = ι (algebraMap _ _ b))
    (Ta : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hTa : ∀ V, V ∈ Ta ↔ (V.ord ((a : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w))
    (Tb : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hTb : ∀ V, V ∈ Tb ↔ (V.ord ((b : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w))
    (htotb : ((∑ V ∈ Tb, (V.ord ((b : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) =
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ b)})))
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : ∀ V, D V = V.ord fc) (Nw : ℤ)
    (hN : (∑ V ∈ D.support with P.reduceFst V = w, D V) = Nw)
    (hends : (sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) 0 ab) - sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) (1 * E) ab)) -
        (sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) 0 ab') - sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) (1 * E) ab')) = Nw)
    (hX : 0 ≤ sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) 0 ab') - sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) (1 * E) ab')) :
    ((∑ V ∈ Ta, (V.ord ((a : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) =
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ a)})) := by
  classical
  have ha0' : (a : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h => ha0 (Subtype.ext h)
  have hb0' : (b : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h => hb0 (Subtype.ext h)

  have hWa := ModularCurve.UVCrossingModel.finsum_rank_mul_length_eq_sInf_sub_sSup π hπ E hE 1 le_rfl
    (ι (algebraMap _ _ a)) hιa ab hab2 habx
  have hWb := ModularCurve.UVCrossingModel.finsum_rank_mul_length_eq_sInf_sub_sSup π hπ E hE 1 le_rfl
    (ι (algebraMap _ _ b)) hιb ab' hab'2 habx'
  rw [hWa]

  have hbN : (∑ V ∈ Tb, (V.ord ((b : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) =
      (sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) 0 ab') - sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) (1 * E) ab')).toNat :=
    ENat.coe_inj.mp (htotb.trans hWb)
  have hordb : ∀ V ∈ Tb, 0 ≤ V.ord (b : ↥(modularFunctionFieldBar (N * q))) := fun V hV => ord_nonneg_of_reduceFst_eq R K w b V ((hTb V).mp hV).2
  have horda : ∀ V ∈ Ta, 0 ≤ V.ord (a : ↥(modularFunctionFieldBar (N * q))) := fun V hV => ord_nonneg_of_reduceFst_eq R K w a V ((hTa V).mp hV).2
  have hbZ : (∑ V ∈ Tb, V.ord (b : ↥(modularFunctionFieldBar (N * q)))) =
      sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) 0 ab') - sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) (1 * E) ab') := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hbN
    simp only [Nat.cast_sum] at h
    rw [Int.toNat_of_nonneg hX] at h
    rw [← h]
    exact Finset.sum_congr rfl fun V hV => (Int.toNat_of_nonneg (hordb V hV)).symm

  have hsplit := sum_support_filter_eq_sum_ord_sub_sum_ord fc (a : ↥(modularFunctionFieldBar (N * q))) (b : ↥(modularFunctionFieldBar (N * q))) ha0' hb0' hfab D hD
    (fun V => P.reduceFst V = w) Ta Tb hTa hTb
  have haZ : (∑ V ∈ Ta, V.ord (a : ↥(modularFunctionFieldBar (N * q)))) =
      sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) 0 ab) - sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) (1 * E) ab) := by
    have h1 : (∑ V ∈ D.support with P.reduceFst V = w, D V) = ∑ V ∈ Ta, V.ord (a : ↥(modularFunctionFieldBar (N * q))) - ∑ V ∈ Tb, V.ord (b : ↥(modularFunctionFieldBar (N * q))) := by
      convert hsplit using 2 <;> first | rfl | (congr 1 <;> exact Subsingleton.elim _ _)
    linarith [hN, hends, hbZ, h1]
  have hanonneg : 0 ≤ ∑ V ∈ Ta, V.ord (a : ↥(modularFunctionFieldBar (N * q))) := Finset.sum_nonneg horda
  congr 1
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sum, Int.toNat_of_nonneg (haZ ▸ hanonneg), ← haZ]
  exact Finset.sum_congr rfl fun V hV => Int.toNat_of_nonneg (horda V hV)

end Slope1

section CoeffValuation

private theorem eq_one_of_mul_eq_one_of_le_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a b : Γ₀}
    (ha : a ≤ 1) (hb : b ≤ 1) (hab : a * b = 1) : a = 1 :=
  le_antisymm ha (by calc (1 : Γ₀) = a * b := hab.symm
    _ ≤ a * 1 := mul_le_mul_right hb a
    _ = a := mul_one a)

private theorem coeff_valuation (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (q : ℕ) (hq : q ≠ 0) (ϖ ε : ↥(NodeLocalized.coeffSubring A K)) (eK : ℕ) (heK : 1 ≤ eK) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε) :
    A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) =
        A.valuation (ϖ : AlgebraicClosure ℚ) ^ eK * A.valuation (ε : AlgebraicClosure ℚ) ∧
      A.valuation (ε : AlgebraicClosure ℚ) = 1 ∧
      A.valuation (ϖ : AlgebraicClosure ℚ) ≤ 1 ∧ A.valuation (ϖ : AlgebraicClosure ℚ) ≠ 0 := by
  have hSA : ∀ z : ↥(NodeLocalized.coeffSubring A K), (z : AlgebraicClosure ℚ) ∈ A := fun z => z.2.1
  have hvq : A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) =
      A.valuation (ϖ : AlgebraicClosure ℚ) ^ eK * A.valuation (ε : AlgebraicClosure ℚ) := by
    have h := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K) => (z : AlgebraicClosure ℚ)) hqϖ
    simp only [Subring.coe_natCast, Subring.coe_mul, Subring.coe_pow] at h
    rw [h, map_mul, map_pow]
  refine ⟨hvq, ?_, (A.valuation_le_one_iff _).mpr (hSA ϖ), ?_⟩
  · obtain ⟨b, hb⟩ := hε.exists_right_inv
    have h := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K) => (z : AlgebraicClosure ℚ)) hb
    simp only [Subring.coe_mul, Subring.coe_one] at h
    have h' := congrArg A.valuation h
    rw [map_mul, map_one] at h'
    exact eq_one_of_mul_eq_one_of_le_one ((A.valuation_le_one_iff _).mpr (hSA ε))
      ((A.valuation_le_one_iff _).mpr (hSA b)) h'
  · intro h0
    rw [h0, zero_pow (by omega), zero_mul, map_eq_zero] at hvq
    exact (Nat.cast_ne_zero.mpr hq) hvq

end CoeffValuation

section Main
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

set_option maxHeartbeats 25600000 in
open Classical in
open _root_.ModularCurve.UVCrossingModel _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq.ModularCurve.UVCrossingModel in

private theorem nodeGauss_scaled
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) (hW₀ : ∀ v ∈ W₀, v ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W₀) (hval : R.NodeValueLaw W₀)

    (K K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKK' : K ≤ K') [FiniteDimensional ℚ K']
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W₀) (hwφ : arithFrobC q k N • w ∈ W₀) (hVI : R.ValueIntegralityLaw w)
    (hBB' : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w)

    (ϖ : ↥(NodeLocalized.coeffSubring A K'))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K')) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K')) = ϖ ^ eK * ε)

    (c : R.NodeCoordinates K w) (ew : ℕ) (hew : 1 ≤ ew) (e' : ℕ) (he' : 1 ≤ e')
    (u : ↥(R.nodeIntegersOver K' w)) (hu : IsUnit u)
    (hxy : (c.x : ↥(modularFunctionFieldBar (N * q))) * c.y = (R.nodeConst K' w ϖ : ↥(modularFunctionFieldBar (N * q))) ^ (ew * eK) * u)
    (hmax : (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K' w), M.IsMaximal → M = Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y})
    [IsLocalRing ↥(R.nodeIntegersOver K' w)] [IsNoetherianRing ↥(R.nodeIntegersOver K' w)]
    (hmax' : maximalIdeal ↥(R.nodeIntegersOver K' w) = Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y})
    (hbr : (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.y}).IsPrime ∧
        Subring.inclusion hBB' c.y ∉ Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x} ∧ Subring.inclusion hBB' c.x ∉ Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K' w), ∃ o : ↥(NodeLocalized.coeffSubring A K'), ¬ IsUnit (g - R.nodeConst K' w o))

    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)

    (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ≠ 0)
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K')
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K', ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K' w ∧ y ∈ R.nodeIntegersOver K' w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    (c₁ c₂ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (hu₁ : R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (h₂ : c₂ • f ∈ R.R₂.integers) (hu₂ : R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)
    (hc₁ : c₁ ∈ K') (hc₂ : c₂ ∈ K') (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0)

    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hDf : ∀ V, D V = V.ord f)
    (hdepth : ∀ V ∈ D.support, P.reduceFst V = w →
      c.yDepth V ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ depth V)

    (hN : (∑ V ∈ D.support with P.reduceFst V = w, D V) =
      w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) :
    ∃ G : ℕ → ℤ,
      (∀ d ∈ Finset.Ico 1 (e' * ew), (G d - G (d - 1)) - (G (d + 1) - G d) =
        ∑ V ∈ D.support with (P.reduceFst V = w ∧ depth V = d), D V) ∧
      G 1 - G 0 = w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) ∧
      G (e' * ew) - G (e' * ew - 1) = -((arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) ∧
      A.valuation (c₁ / c₂) ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (G (e' * ew) - G 0) := by

  have hE : 1 ≤ ew * eK := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hker : ∀ a : A, red a = 0 ↔ a ∈ maximalIdeal A := red_eq_zero_iff R
  rw [inclusion_x R hBB' c, inclusion_y R hBB' c] at hmax hmax' hbr
  have hxy' : (inclCoords R hBB' c).x * (inclCoords R hBB' c).y = R.nodeConst K' w ϖ ^ (ew * eK) * u := Subtype.ext hxy
  obtain ⟨instD, instV, instC, θ, ι, α, β, hirr, hαu, hβu, hWc, hιx, hιy, hord1, hord2⟩ :=
    model R hqN hmodel W₀ hW₀ hreg hval K' hker w hw (inclCoords R hBB' c) ϖ hϖ (ew * eK) hE u hu hxy' hmax hbr.1 hbr.2.2.1 hres

  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  obtain ⟨hvqε, hvε, hvle, hv0⟩ := coeff_valuation A K' q hq0 ϖ ε eK heK hε hqϖ
  have hvq : A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) =
      A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ eK := by rw [hvqε, hvε, mul_one]
  have hredϖ : NodeLocalized.redRestrict red K' ϖ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩
  have hv1 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) < 1 :=
    (A.valuation_lt_one_iff _).mp ((hker _).mp hredϖ)
  have hϖ0 : ϖ ≠ 0 := fun h => hv0 (by rw [h, ZeroMemClass.coe_zero, map_zero])
  have hι0 : ∀ z : ↥(R.nodeIntegersOver K' w), z ≠ 0 → ι (algebraMap _ _ z) ≠ 0 := fun z hz h =>
    ConstantUnits.algebraMap_adicCompletion_ne_zero z hz ((map_eq_zero_iff ι ι.injective).mp h)
  have hne0 : ∀ z : ↥(R.nodeIntegersOver K' w), (z : ↥(modularFunctionFieldBar (N * q))) ≠ 0 → z ≠ 0 := fun z hz h => hz (by rw [h]; rfl)

  have hkerx := AnnulusLocBranch.ker_res₁_eq R K' w (inclCoords R hBB' c) ϖ hredϖ hmax hbr.1 hbr.2.2.1
  have hres₁_of : ∀ s : ↥(R.nodeIntegersOver K' w), s ∉ Ideal.span {R.nodeConst K' w ϖ, (inclCoords R hBB' c).x} →
      R.nodeResidue₁ w ⟨s, s.2.1⟩ ≠ 0 := by
    intro s hs h; apply hs; rw [← hkerx]; exact h
  have hφw : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w :=
    frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr w (hW₀ w hw)
  have hnr : ∀ g : ↥(R.nodeIntegersOver K' w), (R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0 → 0 ≤ w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩)) ∧
      (R.nodeResidue₂ w ⟨g, g.2.1⟩ ≠ 0 → 0 ≤ (frobOnPlacesGeomLevel k N data hKr w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩)) :=
    fun g => hreg.1 (g : ↥(modularFunctionFieldBar (N * q))) g.2.1.1 g.2.1.2.1 w hφw (hW₀ w hw).2.1 (fun V hV => R.ord_nonneg_of_mem_nodeIntegers g.2.1 hV)
  have hnr₁ : ∀ g : ↥(R.nodeIntegersOver K' w), R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0 → ∃ n : ℕ, w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) = (n : ℤ) :=
    fun g hg => ⟨_, (Int.toNat_of_nonneg ((hnr g).1 hg)).symm⟩
  have hnr₂ : ∀ g : ↥(R.nodeIntegersOver K' w), R.nodeResidue₂ w ⟨g, g.2.1⟩ ≠ 0 →
      ∃ n : ℕ, (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) = (n : ℤ) := by
    intro g hg
    rw [arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w]
    exact ⟨_, (Int.toNat_of_nonneg ((hnr g).2 hg)).symm⟩

  have hcst : ∃ cst : AlgebraicClosure ℚ, cst ≠ 0 ∧ cst ∈ K' ∧ cst • f ∈ R.R₁.integers ∧ cst • f ∈ R.R₂.integers ∧
      cst / c₁ ∈ A ∧ cst / c₂ ∈ A := by
    rcases le_total (A.valuation c₁) (A.valuation c₂) with hle | hle
    · have hA : c₁ / c₂ ∈ A := (A.valuation_le_one_iff _).mp (by
        rw [map_div₀]; exact (div_le_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hc₂0))).mpr hle)
      refine ⟨c₁, hc₁0, hc₁, h₁, ?_, by rw [div_self hc₁0]; exact A.one_mem, hA⟩
      have e : c₁ • f = (c₁ / c₂) • (c₂ • f) := by rw [smul_smul, div_mul_cancel₀ _ hc₂0]
      rw [e, Algebra.smul_def]
      exact mul_mem ((R.R₂.algebraMap_mem_iff _).mpr hA) h₂
    · have hA : c₂ / c₁ ∈ A := (A.valuation_le_one_iff _).mp (by
        rw [map_div₀]; exact (div_le_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hc₁0))).mpr hle)
      refine ⟨c₂, hc₂0, hc₂, ?_, h₂, hA, by rw [div_self hc₂0]; exact A.one_mem⟩
      have e : c₂ • f = (c₂ / c₁) • (c₁ • f) := by rw [smul_smul, div_mul_cancel₀ _ hc₁0]
      rw [e, Algebra.smul_def]
      exact mul_mem ((R.R₁.algebraMap_mem_iff _).mpr hA) h₁
  obtain ⟨cst, hcst0, hcstK, hz₁, hz₂, hκ₁A, hκ₂A⟩ := hcst

  obtain ⟨a, b, hb₁, hb₂, hfab⟩ := rep_common R K' w (inclCoords R hBB' c) ϖ hϖ hmax hbr (ew * eK) hE u hu hxy' f hfK hfrac cst hcstK hz₁ hz₂

  obtain ⟨a₁, b₁, ha₁r, hb₁r, hfab₁⟩ := rep_smul_fst R K' w (inclCoords R hBB' c) ϖ hϖ hmax hbr (ew * eK) hE u hu hxy' f hfK hfrac c₁ hc₁ h₁ hu₁
  obtain ⟨a₂, b₂, ha₂r, hb₂r, hfab₂⟩ := rep_smul_snd R K' w (inclCoords R hBB' c) ϖ hϖ hmax hbr (ew * eK) hE u hu hxy' f hfK hfrac c₂ hc₂ h₂ hu₂

  have hb0 : b ≠ 0 := fun h => hb₁ (by rw [show (⟨(b : ↥(modularFunctionFieldBar (N * q))), b.2.1⟩ : ↥(R.nodeIntegers w)) = 0 from Subtype.ext (by rw [h]; rfl), map_zero])
  have hb₁0 : b₁ ≠ 0 := fun h => hb₁r (by rw [show (⟨(b₁ : ↥(modularFunctionFieldBar (N * q))), b₁.2.1⟩ : ↥(R.nodeIntegers w)) = 0 from Subtype.ext (by rw [h]; rfl), map_zero])
  have hb₂0 : b₂ ≠ 0 := fun h => hb₂r (by rw [show (⟨(b₂ : ↥(modularFunctionFieldBar (N * q))), b₂.2.1⟩ : ↥(R.nodeIntegers w)) = 0 from Subtype.ext (by rw [h]; rfl), map_zero])
  have hcf0 : cst • f ≠ 0 := smul_ne_zero hcst0 hf
  have ha0 : a ≠ 0 := hne0 a (by rw [← hfab]; exact mul_ne_zero hcf0 fun h => hb0 (Subtype.ext h))
  have ha₁0 : a₁ ≠ 0 := hne0 a₁ (by rw [← hfab₁]; exact mul_ne_zero (smul_ne_zero hc₁0 hf) fun h => hb₁0 (Subtype.ext h))
  have ha₂0 : a₂ ≠ 0 := hne0 a₂ (by rw [← hfab₂]; exact mul_ne_zero (smul_ne_zero hc₂0 hf) fun h => hb₂0 (Subtype.ext h))
  have hιa := hι0 a ha0
  have hιb := hι0 b hb0
  have hιa₁ := hι0 a₁ ha₁0
  have hιb₁ := hι0 b₁ hb₁0
  have hιa₂ := hι0 a₂ ha₂0
  have hιb₂ := hι0 b₂ hb₂0

  haveI hcompl : IsAdicComplete (Ideal.span {(Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ))}) (PowerSeries ↥(NodeLocalized.coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) := by
    rw [← hirr.maximalIdeal_eq]; exact instC
  obtain ⟨abA, ⟨habA2, habA⟩, -⟩ := ModularCurve.UVCrossingModel.existsUnique_normalForm _ (ew * eK) hE (ι (algebraMap _ _ a))
  obtain ⟨abB, ⟨habB2, habB⟩, -⟩ := ModularCurve.UVCrossingModel.existsUnique_normalForm _ (ew * eK) hE (ι (algebraMap _ _ b))
  obtain ⟨abA₁, ⟨habA₁2, habA₁⟩, -⟩ := ModularCurve.UVCrossingModel.existsUnique_normalForm _ (ew * eK) hE (ι (algebraMap _ _ a₁))
  obtain ⟨abB₁, ⟨habB₁2, habB₁⟩, -⟩ := ModularCurve.UVCrossingModel.existsUnique_normalForm _ (ew * eK) hE (ι (algebraMap _ _ b₁))
  obtain ⟨abA₂, ⟨habA₂2, habA₂⟩, -⟩ := ModularCurve.UVCrossingModel.existsUnique_normalForm _ (ew * eK) hE (ι (algebraMap _ _ a₂))
  obtain ⟨abB₂, ⟨habB₂2, habB₂⟩, -⟩ := ModularCurve.UVCrossingModel.existsUnique_normalForm _ (ew * eK) hE (ι (algebraMap _ _ b₂))

  obtain ⟨nb, hnb⟩ := hnr₁ b hb₁
  obtain ⟨mbb, hmbb⟩ := hnr₂ b hb₂
  obtain ⟨na₁, hna₁⟩ := hnr₁ a₁ ha₁r
  obtain ⟨nb₁, hnb₁⟩ := hnr₁ b₁ hb₁r
  obtain ⟨ma₂, hma₂⟩ := hnr₂ a₂ ha₂r
  obtain ⟨mb₂, hmb₂⟩ := hnr₂ b₂ hb₂r

  obtain ⟨γb, hγb, hxγb⟩ := hord1 b nb hb₁ hnb
  have hGTb := (ModularCurve.UVCrossingModel.sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem _ hirr (ew * eK) hE 1 le_rfl
    (ι (algebraMap _ _ b)) hιb abB habB2 habB γb hγb nb hxγb).2
  obtain ⟨δb, hδb, hxδb⟩ := hord2 b mbb hb₂ hmbb
  have hGSb := (ModularCurve.UVCrossingModel.sInf_dominantIndices_eq_of_sub_mul_U_pow_mem _ hirr (ew * eK) hE 1 le_rfl
    (ι (algebraMap _ _ b)) hιb abB habB2 habB δb hδb mbb hxδb).2
  obtain ⟨γa₁, hγa₁, hxγa₁⟩ := hord1 a₁ na₁ ha₁r hna₁
  have hGTa₁ := (ModularCurve.UVCrossingModel.sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem _ hirr (ew * eK) hE 1 le_rfl
    (ι (algebraMap _ _ a₁)) hιa₁ abA₁ habA₁2 habA₁ γa₁ hγa₁ na₁ hxγa₁).2
  obtain ⟨γb₁, hγb₁, hxγb₁⟩ := hord1 b₁ nb₁ hb₁r hnb₁
  have hGTb₁ := (ModularCurve.UVCrossingModel.sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem _ hirr (ew * eK) hE 1 le_rfl
    (ι (algebraMap _ _ b₁)) hιb₁ abB₁ habB₁2 habB₁ γb₁ hγb₁ nb₁ hxγb₁).2
  obtain ⟨δa₂, hδa₂, hxδa₂⟩ := hord2 a₂ ma₂ ha₂r hma₂
  have hGSa₂ := (ModularCurve.UVCrossingModel.sInf_dominantIndices_eq_of_sub_mul_U_pow_mem _ hirr (ew * eK) hE 1 le_rfl
    (ι (algebraMap _ _ a₂)) hιa₂ abA₂ habA₂2 habA₂ δa₂ hδa₂ ma₂ hxδa₂).2
  obtain ⟨δb₂, hδb₂, hxδb₂⟩ := hord2 b₂ mb₂ hb₂r hmb₂
  have hGSb₂ := (ModularCurve.UVCrossingModel.sInf_dominantIndices_eq_of_sub_mul_U_pow_mem _ hirr (ew * eK) hE 1 le_rfl
    (ι (algebraMap _ _ b₂)) hιb₂ abB₂ habB₂2 habB₂ δb₂ hδb₂ mb₂ hxδb₂).2

  have hκ₁K : cst / c₁ ∈ K' := div_mem hcstK hc₁
  have hκ₂K : cst / c₂ ∈ K' := div_mem hcstK hc₂
  have hsmul : ∀ (γ : AlgebraicClosure ℚ) (z : ↥(modularFunctionFieldBar (N * q))), γ • z = algebraMap _ ↥(modularFunctionFieldBar (N * q)) γ * z := fun γ z => Algebra.smul_def γ z
  have hc₁F : algebraMap _ ↥(modularFunctionFieldBar (N * q)) c₁ ≠ 0 := (map_ne_zero _).mpr hc₁0
  have hc₂F : algebraMap _ ↥(modularFunctionFieldBar (N * q)) c₂ ≠ 0 := (map_ne_zero _).mpr hc₂0
  have hcstF : algebraMap _ ↥(modularFunctionFieldBar (N * q)) cst ≠ 0 := (map_ne_zero _).mpr hcst0
  have hrel₁ : a * b₁ = R.nodeConst K' w ⟨cst / c₁, hκ₁A, hκ₁K⟩ * (a₁ * b) := by
    apply Subtype.ext
    simp only [Subring.coe_mul, ProlongationTuple.coe_nodeConst]
    rw [← hfab, ← hfab₁, hsmul, hsmul, map_div₀]
    field_simp
  have hrel₂ : a * b₂ = R.nodeConst K' w ⟨cst / c₂, hκ₂A, hκ₂K⟩ * (a₂ * b) := by
    apply Subtype.ext
    simp only [Subring.coe_mul, ProlongationTuple.coe_nodeConst]
    rw [← hfab, ← hfab₂, hsmul, hsmul, map_div₀]
    field_simp

  have hcW : ∀ o : ↥(NodeLocalized.coeffSubring A K'), o ≠ 0 →
      (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C o)) ≠ 0 := by
    intro o ho h
    have h1 := hWc o
    rw [h, show UVCrossingModel.const ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ (ew * eK)) (0 : (PowerSeries ↥(NodeLocalized.coeffSubring A K') ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ})) = 0 from map_zero (UVCrossingModel.constHom ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K')) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) ^ (ew * eK)))] at h1
    refine hι0 (R.nodeConst K' w o) ?_ h1
    intro h2
    apply ho
    have h3 := congrArg (fun z : ↥(R.nodeIntegersOver K' w) => (z : ↥(modularFunctionFieldBar (N * q)))) h2
    simp only [ProlongationTuple.coe_nodeConst, ZeroMemClass.coe_zero, map_eq_zero] at h3
    exact Subtype.ext h3
  have hκ₁0 : (⟨cst / c₁, hκ₁A, hκ₁K⟩ : ↥(NodeLocalized.coeffSubring A K')) ≠ 0 := fun h =>
    (div_ne_zero hcst0 hc₁0) (congrArg Subtype.val h)
  have hκ₂0 : (⟨cst / c₂, hκ₂A, hκ₂K⟩ : ↥(NodeLocalized.coeffSubring A K')) ≠ 0 := fun h =>
    (div_ne_zero hcst0 hc₂0) (congrArg Subtype.val h)
  have hrel₁' : ι (algebraMap _ _ a) * ι (algebraMap _ _ b₁) =
      UVCrossingModel.const _ (Ideal.Quotient.mk _ (PowerSeries.C (⟨cst / c₁, hκ₁A, hκ₁K⟩ : ↥(NodeLocalized.coeffSubring A K')))) *
        (ι (algebraMap _ _ a₁) * ι (algebraMap _ _ b)) := by
    rw [← map_mul, ← map_mul, hrel₁, map_mul, map_mul, hWc, ← map_mul, ← map_mul]
  have hrel₂' : ι (algebraMap _ _ a) * ι (algebraMap _ _ b₂) =
      UVCrossingModel.const _ (Ideal.Quotient.mk _ (PowerSeries.C (⟨cst / c₂, hκ₂A, hκ₂K⟩ : ↥(NodeLocalized.coeffSubring A K')))) *
        (ι (algebraMap _ _ a₂) * ι (algebraMap _ _ b)) := by
    rw [← map_mul, ← map_mul, hrel₂, map_mul, map_mul, hWc, ← map_mul, ← map_mul]
  have hprod0 : ∀ x y : ↥(R.nodeIntegersOver K' w), x ≠ 0 → y ≠ 0 → ι (algebraMap _ _ x) * ι (algebraMap _ _ y) ≠ 0 := by
    intro x y hx hy; rw [← map_mul, ← map_mul]; exact hι0 _ (mul_ne_zero hx hy)
  obtain ⟨hEtop, -⟩ := AnnulusEnds.extremes_sub_eq_of_mul_eq_const_mul _ hirr (ew * eK) hE
    (ι (algebraMap _ _ a)) (ι (algebraMap _ _ b)) (ι (algebraMap _ _ a₁)) (ι (algebraMap _ _ b₁)) hιa hιb hιa₁ hιb₁
    _ (hcW _ hκ₁0) hrel₁' (hprod0 a b₁ ha0 hb₁0) (hprod0 a₁ b ha₁0 hb0)
    abA abB abA₁ abB₁ habA2 habA habB2 habB habA₁2 habA₁ habB₁2 habB₁
  obtain ⟨-, hEbot⟩ := AnnulusEnds.extremes_sub_eq_of_mul_eq_const_mul _ hirr (ew * eK) hE
    (ι (algebraMap _ _ a)) (ι (algebraMap _ _ b)) (ι (algebraMap _ _ a₂)) (ι (algebraMap _ _ b₂)) hιa hιb hιa₂ hιb₂
    _ (hcW _ hκ₂0) hrel₂' (hprod0 a b₂ ha0 hb₂0) (hprod0 a₂ b ha₂0 hb0)
    abA abB abA₂ abB₂ habA2 habA habB2 habB habA₂2 habA₂ habB₂2 habB₂

  have hres₁cf : w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) = (na₁ : ℤ) - nb₁ := by
    have hmul : (⟨(a₁ : ↥(modularFunctionFieldBar (N * q))), a₁.2.1.1⟩ : ↥R.R₁.integers) = ⟨c₁ • f, h₁⟩ * ⟨(b₁ : ↥(modularFunctionFieldBar (N * q))), b₁.2.1.1⟩ :=
      Subtype.ext hfab₁.symm
    have hb₁r' : R.residue₁ ⟨(b₁ : ↥(modularFunctionFieldBar (N * q))), b₁.2.1.1⟩ ≠ 0 := hb₁r
    have hu : R.residue₁ ⟨c₁ • f, h₁⟩ ≠ 0 := by
      rw [ProlongationTuple.residue₁_apply]; exact (map_ne_zero R.ι).mpr hu₁
    have e : R.residue₁ ⟨(a₁ : ↥(modularFunctionFieldBar (N * q))), a₁.2.1.1⟩ = R.residue₁ ⟨c₁ • f, h₁⟩ * R.residue₁ ⟨(b₁ : ↥(modularFunctionFieldBar (N * q))), b₁.2.1.1⟩ := by
      rw [hmul, map_mul]
    have h := congrArg (fun z => w.ord z) e
    beta_reduce at h
    rw [w.ord_mul hu hb₁r'] at h
    have hna₁' : w.ord (R.residue₁ ⟨(a₁ : ↥(modularFunctionFieldBar (N * q))), a₁.2.1.1⟩) = (na₁ : ℤ) := hna₁
    have hnb₁' : w.ord (R.residue₁ ⟨(b₁ : ↥(modularFunctionFieldBar (N * q))), b₁.2.1.1⟩) = (nb₁ : ℤ) := hnb₁
    rw [hna₁', hnb₁'] at h
    linarith
  have hres₂cf : (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) = (ma₂ : ℤ) - mb₂ := by
    have hmul : (⟨(a₂ : ↥(modularFunctionFieldBar (N * q))), a₂.2.1.2.1⟩ : ↥R.R₂.integers) = ⟨c₂ • f, h₂⟩ * ⟨(b₂ : ↥(modularFunctionFieldBar (N * q))), b₂.2.1.2.1⟩ :=
      Subtype.ext hfab₂.symm
    have hb₂r' : R.residue₂ ⟨(b₂ : ↥(modularFunctionFieldBar (N * q))), b₂.2.1.2.1⟩ ≠ 0 := hb₂r
    have hu : R.residue₂ ⟨c₂ • f, h₂⟩ ≠ 0 := by
      rw [ProlongationTuple.residue₂_apply]; exact (map_ne_zero R.ι).mpr hu₂
    have e : R.residue₂ ⟨(a₂ : ↥(modularFunctionFieldBar (N * q))), a₂.2.1.2.1⟩ = R.residue₂ ⟨c₂ • f, h₂⟩ * R.residue₂ ⟨(b₂ : ↥(modularFunctionFieldBar (N * q))), b₂.2.1.2.1⟩ := by
      rw [hmul, map_mul]
    have h := congrArg (fun z => (arithFrobC q k N • w).ord z) e
    beta_reduce at h
    rw [(arithFrobC q k N • w).ord_mul hu hb₂r'] at h
    have hma₂' : (arithFrobC q k N • w).ord (R.residue₂ ⟨(a₂ : ↥(modularFunctionFieldBar (N * q))), a₂.2.1.2.1⟩) = (ma₂ : ℤ) := hma₂
    have hmb₂' : (arithFrobC q k N • w).ord (R.residue₂ ⟨(b₂ : ↥(modularFunctionFieldBar (N * q))), b₂.2.1.2.1⟩) = (mb₂ : ℤ) := hmb₂
    rw [hma₂', hmb₂'] at h
    linarith
  have hsupAB : sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (1 * (ew * eK)) (1 * (ew * eK)) abA)
      - sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (1 * (ew * eK)) (1 * (ew * eK)) abB)
      = -(w.ord (R.residue₁ ⟨c₁ • f, h₁⟩)) := by
    rw [hEtop, hGTa₁, hGTb₁, hres₁cf]; ring
  have hinfAB : sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (1 * (ew * eK)) 0 abA)
      - sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (1 * (ew * eK)) 0 abB)
      = (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) := by
    rw [hEbot, hGSa₂, hGSb₂, hres₂cf]
  have hends : (sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (1 * (ew * eK)) 0 abA)
        - sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (1 * (ew * eK)) (1 * (ew * eK)) abA))
      - (sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (1 * (ew * eK)) 0 abB)
        - sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (1 * (ew * eK)) (1 * (ew * eK)) abB))
      = w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) := by
    linarith [hsupAB, hinfAB]
  have hX : 0 ≤ sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (1 * (ew * eK)) 0 abB)
      - sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (1 * (ew * eK)) (1 * (ew * eK)) abB) := by
    rw [hGSb, hGTb]; omega

  haveI hCurveBar : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    isCurveOver_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) (N * q)
  obtain ⟨Da, hDa, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldBar (N * q))) (fun h => ha0 (Subtype.ext h))
  obtain ⟨Db, hDb, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (b : ↥(modularFunctionFieldBar (N * q))) (fun h => hb0 (Subtype.ext h))
  have hTa : ∀ V, V ∈ Da.support.filter (fun V => P.reduceFst V = w) ↔ (V.ord (a : ↥(modularFunctionFieldBar (N * q))) ≠ 0 ∧ P.reduceFst V = w) :=
    fun V => by rw [Finset.mem_filter, Finsupp.mem_support_iff, hDa V]
  have hTb : ∀ V, V ∈ Db.support.filter (fun V => P.reduceFst V = w) ↔ (V.ord (b : ↥(modularFunctionFieldBar (N * q))) ≠ 0 ∧ P.reduceFst V = w) :=
    fun V => by rw [Finset.mem_filter, Finsupp.mem_support_iff, hDb V]
  have hb2nn : 0 ≤ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨b, b.2.1⟩) := by rw [hmbb]; exact Int.natCast_nonneg _
  have htotb := ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_eq_finsum_rank_mul_length_total_of_nodeResidue_ne_zero
    R K' w (inclCoords R hBB' c) ϖ hmax' hres hVI (hW₀ w hw) _ hirr (ew * eK) hE ι (hWc ϖ) α hαu hιx b hqN hO hb₁ hb₂ hord1 hord2
    ((hnr b).1 hb₁) hb2nn (Db.support.filter fun V => P.reduceFst V = w) hTb
  have hD' : ∀ V, D V = V.ord (cst • f) := fun V => by rw [hDf V, Place.ord_smul_of_ne_zero V hcst0]
  have htota := total_eq_of_sub_total R K' w _ hirr (ew * eK) hE ι (cst • f) a b ha0 hb0 hfab hιa hιb abA habA2 habA abB habB2 habB
    (Da.support.filter fun V => P.reduceFst V = w) hTa (Db.support.filter fun V => P.reduceFst V = w) hTb htotb D hD' _ hN hends hX

  have hgrid : ∀ V ∈ D.support, P.reduceFst V = w →
      depth V ≤ e' * ew ∧ (inclCoords R hBB' c).xDepth V ^ e' = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ (e' * (ew * eK) - depth V * eK) := by
    intro V hV hVw
    obtain ⟨hx1, -, hprod⟩ := ModularCurve.PlaceSpecialization.ProlongationTuple.nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed
      R hqN hmodel hO W₀ hW₀ hreg hval K' w hw hVI ϖ (inclCoords R hBB' c) (ew * eK) u hu hxy' V hVw
    have hy : (inclCoords R hBB' c).yDepth V ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ depth V := hdepth V hV hVw
    exact grid_of_depth_scaled he' hx1 hprod hy hvqε hvε hvle hv0
  obtain ⟨hagree, hgridId⟩ := circleIndexDrop_sub_eq_sum_div_of_total_eq R K' w (hW₀ w hw) (inclCoords R hBB' c) ϖ hmax' hres hVI hv0 hv1
    _ hirr (ew * eK) hE ι (hWc ϖ) α hαu hιx ew eK hew heK rfl e' he' (cst • f) a b ha0 hb0 hfab hιa hιb abA habA2 habA abB habB2 habB
    (Da.support.filter fun V => P.reduceFst V = w) hTa htota (Db.support.filter fun V => P.reduceFst V = w) hTb htotb D hD' depth hgrid

  have hmaxS : (Ideal.span {R.nodeConst K' w ϖ, (inclCoords R hBB' c).y, (inclCoords R hBB' c).x}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K' w), M.IsMaximal → M = Ideal.span {R.nodeConst K' w ϖ, (inclCoords R hBB' c).y, (inclCoords R hBB' c).x} := by
    have e : ({R.nodeConst K' w ϖ, (inclCoords R hBB' c).y, (inclCoords R hBB' c).x} : Set ↥(R.nodeIntegersOver K' w)) = {R.nodeConst K' w ϖ, (inclCoords R hBB' c).x, (inclCoords R hBB' c).y} := by
      rw [Set.pair_comm]
    rw [e]; exact hmax
  have hkery := AnnulusLocBranchSnd.ker_res₂_eq R K' w (inclCoords R hBB' c) ϖ hredϖ hmaxS hbr.2.1 hbr.2.2.2
  have hres₂_of : ∀ s : ↥(R.nodeIntegersOver K' w), s ∉ Ideal.span {R.nodeConst K' w ϖ, (inclCoords R hBB' c).y} → R.nodeResidue₂ w ⟨s, s.2.1⟩ ≠ 0 := by
    intro s hs h; apply hs; rw [← hkery]; exact h
  have hxy'' : (inclCoords R hBB' c).y * (inclCoords R hBB' c).x = R.nodeConst K' w ϖ ^ (ew * eK) * u :=
    (mul_comm _ _).trans hxy'
  obtain ⟨ma, sa, ta, hsa0, hta0, hfa⟩ := AnnulusLocBranch.exists_mul_eq_pow_mul R K' w (inclCoords R hBB' c) ϖ hbr.1 hbr.2.2.1 hbr.2.2.2 (ew * eK) hE u hu hxy' a ha0
  obtain ⟨mb, sb, tb, hsb0, htb0, hfb⟩ := AnnulusLocBranch.exists_mul_eq_pow_mul R K' w (inclCoords R hBB' c) ϖ hbr.1 hbr.2.2.1 hbr.2.2.2 (ew * eK) hE u hu hxy' b hb0
  obtain ⟨na, sa', ta', hsa'0, hta'0, hga⟩ := AnnulusLocBranchSnd.exists_mul_eq_pow_mul R K' w (inclCoords R hBB' c) ϖ hbr.2.1 hbr.2.2.2 hbr.2.2.1 (ew * eK) hE u hu hxy'' a ha0
  obtain ⟨nb', sb', tb', hsb'0, htb'0, hgb⟩ := AnnulusLocBranchSnd.exists_mul_eq_pow_mul R K' w (inclCoords R hBB' c) ϖ hbr.2.1 hbr.2.2.2 hbr.2.2.1 (ew * eK) hE u hu hxy'' b hb0
  have hsa := hres₁_of sa hsa0
  have hta := hres₁_of ta hta0
  have hsb := hres₁_of sb hsb0
  have htb := hres₁_of tb htb0
  have hsa' := hres₂_of sa' hsa'0
  have hta' := hres₂_of ta' hta'0
  have hsb' := hres₂_of sb' hsb'0
  have htb' := hres₂_of tb' htb'0
  obtain ⟨nsa, hnsa⟩ := hnr₁ sa hsa
  obtain ⟨nta, hnta⟩ := hnr₁ ta hta
  obtain ⟨nsb, hnsb⟩ := hnr₁ sb hsb
  obtain ⟨ntb, hntb⟩ := hnr₁ tb htb
  obtain ⟨nsa', hnsa'⟩ := hnr₂ sa' hsa'
  obtain ⟨nta', hnta'⟩ := hnr₂ ta' hta'
  obtain ⟨nsb', hnsb'⟩ := hnr₂ sb' hsb'
  obtain ⟨ntb', hntb'⟩ := hnr₂ tb' htb'

  have hfinA : ∀ t, t ≤ ew * eK → gaussOrder (IsDiscreteValuationRing.addVal _) (_ ^ (ew * eK)) (ew * eK) t (ι (algebraMap _ _ a)) ≠ ⊤ :=
    fun t ht => ModularCurve.UVCrossingModel.gaussOrder_ne_top_of_ne_zero _ hirr (ew * eK) hE _ hιa t ht
  have hfinB : ∀ t, t ≤ ew * eK → gaussOrder (IsDiscreteValuationRing.addVal _) (_ ^ (ew * eK)) (ew * eK) t (ι (algebraMap _ _ b)) ≠ ⊤ :=
    fun t ht => ModularCurve.UVCrossingModel.gaussOrder_ne_top_of_ne_zero _ hirr (ew * eK) hE _ hιb t ht

  let φ : ℕ → ℤ := fun t =>
    ((gaussOrder (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (_ ^ (ew * eK)) (e' * (ew * eK)) t (ι (algebraMap _ _ a))).toNat : ℤ)
      - (gaussOrder (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (_ ^ (ew * eK)) (e' * (ew * eK)) t (ι (algebraMap _ _ b))).toNat

  have hφ : ∀ t, φ t = ((gaussOrder (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (_ ^ (ew * eK)) (e' * (ew * eK)) t (ι (algebraMap _ _ a))).toNat : ℤ)
      - (gaussOrder (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (_ ^ (ew * eK)) (e' * (ew * eK)) t (ι (algebraMap _ _ b))).toNat := fun t => rfl
  let G : ℕ → ℤ := fun d => (φ (e' * (ew * eK) - d * eK) - φ (e' * (ew * eK))) / eK
  have hG : ∀ d, G d = (φ (e' * (ew * eK) - d * eK) - φ (e' * (ew * eK))) / eK := fun d => rfl

  obtain ⟨hdiv, hsecond, htop, hbot, hraw1, hraw2⟩ :=
    ModularCurve.UVCrossingModel.gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq_scaled
      _ hirr ew eK hew heK (ew * eK) rfl e' he' (ι (algebraMap _ _ a)) hιa abA habA2 habA (ι (algebraMap _ _ b)) hιb abB habB2 habB
      hagree φ hφ G hG

  have he'0 : e' ≠ 0 := by omega
  have hdomBA := ModularCurve.UVCrossingModel.dominantIndices_mul_scale (IsDiscreteValuationRing.addVal _) e' (ew * eK) 0 he'0 abA
  have hdomBB := ModularCurve.UVCrossingModel.dominantIndices_mul_scale (IsDiscreteValuationRing.addVal _) e' (ew * eK) 0 he'0 abB
  have hdomBA1 := ModularCurve.UVCrossingModel.dominantIndices_mul_scale (IsDiscreteValuationRing.addVal _) 1 (ew * eK) 0 one_ne_zero abA
  have hdomBB1 := ModularCurve.UVCrossingModel.dominantIndices_mul_scale (IsDiscreteValuationRing.addVal _) 1 (ew * eK) 0 one_ne_zero abB
  rw [Nat.mul_zero] at hdomBA hdomBB hdomBA1 hdomBB1
  have hsupAB' : sSup (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (e' * (ew * eK)) (e' * (ew * eK)) abA)
      - sSup (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (e' * (ew * eK)) (e' * (ew * eK)) abB)
      = -(w.ord (R.residue₁ ⟨c₁ • f, h₁⟩)) := by
    have h := hsupAB
    rw [ModularCurve.UVCrossingModel.dominantIndices_mul_scale (IsDiscreteValuationRing.addVal _) 1 (ew * eK) (ew * eK) one_ne_zero abA, ModularCurve.UVCrossingModel.dominantIndices_mul_scale (IsDiscreteValuationRing.addVal _) 1 (ew * eK) (ew * eK) one_ne_zero abB] at h
    rw [ModularCurve.UVCrossingModel.dominantIndices_mul_scale (IsDiscreteValuationRing.addVal _) e' (ew * eK) (ew * eK) he'0 abA, ModularCurve.UVCrossingModel.dominantIndices_mul_scale (IsDiscreteValuationRing.addVal _) e' (ew * eK) (ew * eK) he'0 abB]
    exact h
  have hinfAB' : sInf (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (e' * (ew * eK)) 0 abA)
      - sInf (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (e' * (ew * eK)) 0 abB)
      = (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) := by
    have h := hinfAB
    rw [hdomBA1, hdomBB1] at h
    rw [hdomBA, hdomBB]
    exact h
  have hC1 : ∀ d ∈ Finset.Ico 1 (e' * ew), (G d - G (d - 1)) - (G (d + 1) - G d) =
      ∑ V ∈ D.support with (P.reduceFst V = w ∧ depth V = d), D V := by
    intro d hd
    rw [hsecond d hd]
    exact hgridId d hd

  have hC2 : G 1 - G 0 = w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) := by
    rw [htop, hsupAB']; ring
  have hC3 : G (e' * ew) - G (e' * ew - 1) = -((arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) := by
    rw [hbot, hinfAB']

  have hgEa := gaussOrder_fst_end_eq_of_mul_eq_nodeConst_pow_mul R K' w ϖ (ew * eK) hE _ hirr ι (hWc ϖ) hord1 a sa ta ma hfa nsa nta hsa hnsa hta hnta
  have hgEb := gaussOrder_fst_end_eq_of_mul_eq_nodeConst_pow_mul R K' w ϖ (ew * eK) hE _ hirr ι (hWc ϖ) hord1 b sb tb mb hfb nsb ntb hsb hnsb htb hntb
  have hg0a := gaussOrder_snd_end_eq_of_mul_eq_nodeConst_pow_mul R K' w ϖ (ew * eK) hE _ hirr ι (hWc ϖ) hord2 a sa' ta' na hga nsa' nta' hsa' hnsa' hta' hnta'
  have hg0b := gaussOrder_snd_end_eq_of_mul_eq_nodeConst_pow_mul R K' w ϖ (ew * eK) hE _ hirr ι (hWc ϖ) hord2 b sb' tb' nb' hgb nsb' ntb' hsb' hnsb' htb' hntb'

  have hbrA : ∀ t, gaussOrder (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (_ ^ (ew * eK)) (e' * (ew * eK)) (e' * t) (ι (algebraMap _ _ a))
      = ((e' : ℕ) : ℕ∞) * gaussOrder (IsDiscreteValuationRing.addVal _) (_ ^ (ew * eK)) (ew * eK) t (ι (algebraMap _ _ a)) :=
    fun t => ModularCurve.UVCrossingModel.gaussOrder_mul_scale' _ _ e' (ew * eK) t he'0 _
  have hbrB : ∀ t, gaussOrder (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal _ w) (_ ^ (ew * eK)) (e' * (ew * eK)) (e' * t) (ι (algebraMap _ _ b))
      = ((e' : ℕ) : ℕ∞) * gaussOrder (IsDiscreteValuationRing.addVal _) (_ ^ (ew * eK)) (ew * eK) t (ι (algebraMap _ _ b)) :=
    fun t => ModularCurve.UVCrossingModel.gaussOrder_mul_scale' _ _ e' (ew * eK) t he'0 _
  have hφE : φ (e' * (ew * eK)) = (e' : ℤ) * ((ma : ℤ) - mb) := by
    rw [hφ, hbrA, hbrB, hgEa, hgEb]
    simp only [← Nat.cast_mul, ENat.toNat_coe]
    push_cast; ring
  have hφ0 : φ 0 = (e' : ℤ) * ((na : ℤ) - nb') := by
    have h0 : (0 : ℕ) = e' * 0 := (Nat.mul_zero _).symm
    rw [hφ, h0, hbrA, hbrB, hg0a, hg0b]
    simp only [← Nat.cast_mul, ENat.toNat_coe]
    push_cast; ring
  have hsm₁ : (c₁ / cst) • (cst • f) = c₁ • f := by rw [smul_smul, div_mul_cancel₀ _ hcst0]
  have hsm₂ : (c₂ / cst) • (cst • f) = c₂ • f := by rw [smul_smul, div_mul_cancel₀ _ hcst0]
  have hk₁0 : c₁ / cst ≠ 0 := div_ne_zero hc₁0 hcst0
  have hk₂0 : c₂ / cst ≠ 0 := div_ne_zero hc₂0 hcst0

  have hz1 : (c₁ / cst) • (cst • f) ∈ R.R₁.integers := by rw [hsm₁]; exact h₁
  have hzu1 : R.R₁.residue ⟨(c₁ / cst) • (cst • f), hz1⟩ ≠ 0 := by
    have : (⟨(c₁ / cst) • (cst • f), hz1⟩ : ↥R.R₁.integers) = ⟨c₁ • f, h₁⟩ := Subtype.ext hsm₁
    rw [this]; exact hu₁
  have hz2 : (c₂ / cst) • (cst • f) ∈ R.R₂.integers := by rw [hsm₂]; exact h₂
  have hzu2 : R.R₂.residue ⟨(c₂ / cst) • (cst • f), hz2⟩ ≠ 0 := by
    have : (⟨(c₂ / cst) • (cst • f), hz2⟩ : ↥R.R₂.integers) = ⟨c₂ • f, h₂⟩ := Subtype.ext hsm₂
    rw [this]; exact hu₂
  have hval1 := valuation_const_eq_of_smul_isUnit_fst R K' w ϖ hϖ0 (cst • f) (c₁ / cst) hk₁0 hz1 hzu1 a b sa ta sb tb hb0 hfab ma mb hfa hfb hsa hta hsb htb
  have hval2 := valuation_const_eq_of_smul_isUnit_snd R K' w ϖ hϖ0 (cst • f) (c₂ / cst) hk₂0 hz2 hzu2 a b sa' ta' sb' tb' hb0 hfab na nb' hga hgb hsa' hta' hsb' htb'

  have hidx0 : e' * (ew * eK) - e' * ew * eK = 0 := by rw [Nat.mul_assoc, Nat.sub_self]
  have hGew : G (e' * ew) - G 0 = (φ 0 - φ (e' * (ew * eK))) / eK := by
    simp only [hG, hidx0, Nat.zero_mul, Nat.sub_zero, sub_self, Int.zero_ediv, sub_zero]
  obtain ⟨kq, hkq⟩ := hdiv (e' * ew) le_rfl
  rw [hidx0] at hkq
  have heK0 : (eK : ℤ) ≠ 0 := by exact_mod_cast (show eK ≠ 0 by omega)
  have hkq' : G (e' * ew) - G 0 = kq := by
    rw [hGew, hkq]
    exact Int.mul_ediv_cancel_left _ heK0
  have hexp : ((eK : ℤ) * kq) = (e' : ℤ) * (((mb : ℤ) - ma) - ((nb' : ℤ) - na)) := by
    rw [← hkq, hφ0, hφE]; ring
  have hcd : c₁ / c₂ = (c₁ / cst) / (c₂ / cst) := by field_simp
  have hpow : ∀ n : ℕ, A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ n ≠ 0 := fun n => pow_ne_zero _ hv0
  have e1 : A.valuation (c₁ / cst) = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ mb / A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ ma := eq_div_of_mul_eq (hpow ma) hval1
  have e2 : A.valuation (c₂ / cst) = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ nb' / A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ na := eq_div_of_mul_eq (hpow na) hval2
  have hv : A.valuation (c₁ / c₂) = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ (((mb : ℤ) - ma) - ((nb' : ℤ) - na)) := by
    rw [hcd, map_div₀, e1, e2]
    rw [zpow_sub₀ hv0, zpow_sub₀ hv0, zpow_sub₀ hv0]
    simp only [zpow_natCast]
  have hC4 : A.valuation (c₁ / c₂) ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (G (e' * ew) - G 0) := by
    rw [hkq', hvq, hv, ← zpow_natCast _ e', ← zpow_mul, ← zpow_natCast _ eK, ← zpow_mul, hexp]
    congr 1
    ring
  exact ⟨G, hC1, hC2, hC3, hC4⟩

end Main
end SlopeLaw

open Classical in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) (hW₀ : ∀ v ∈ W₀, v ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W₀) (hval : R.NodeValueLaw W₀)

    (K K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKK' : K ≤ K') [FiniteDimensional ℚ K']
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W₀) (hwφ : arithFrobC q k N • w ∈ W₀) (hVI : R.ValueIntegralityLaw w)
    (hBB' : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w)

    (ϖ : ↥(NodeLocalized.coeffSubring A K'))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K')) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K')) = ϖ ^ eK * ε)

    (c : R.NodeCoordinates K w) (ew : ℕ) (hew : 1 ≤ ew) (e' : ℕ) (he' : 1 ≤ e')
    (u : ↥(R.nodeIntegersOver K' w)) (hu : IsUnit u)
    (hxy : (c.x : ↥(modularFunctionFieldBar (N * q))) * c.y = (R.nodeConst K' w ϖ : ↥(modularFunctionFieldBar (N * q))) ^ (ew * eK) * u)
    (hmax : (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K' w), M.IsMaximal → M = Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y})
    [IsLocalRing ↥(R.nodeIntegersOver K' w)] [IsNoetherianRing ↥(R.nodeIntegersOver K' w)]
    (hmax' : maximalIdeal ↥(R.nodeIntegersOver K' w) = Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y})
    (hbr : (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.y}).IsPrime ∧
        Subring.inclusion hBB' c.y ∉ Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x} ∧ Subring.inclusion hBB' c.x ∉ Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K' w), ∃ o : ↥(NodeLocalized.coeffSubring A K'), ¬ IsUnit (g - R.nodeConst K' w o))

    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)

    (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ≠ 0)
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K')
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K', ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K' w ∧ y ∈ R.nodeIntegersOver K' w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    (c₁ c₂ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (hu₁ : R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (h₂ : c₂ • f ∈ R.R₂.integers) (hu₂ : R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)
    (hc₁ : c₁ ∈ K') (hc₂ : c₂ ∈ K') (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0)

    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hDf : ∀ V, D V = V.ord f)
    (hdepth : ∀ V ∈ D.support, P.reduceFst V = w →
      c.yDepth V ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ depth V)

    (hN : (∑ V ∈ D.support with P.reduceFst V = w, D V) =
      w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) :
    ∃ G : ℕ → ℤ,
      (∀ d ∈ Finset.Ico 1 (e' * ew), (G d - G (d - 1)) - (G (d + 1) - G d) =
        ∑ V ∈ D.support with (P.reduceFst V = w ∧ depth V = d), D V) ∧
      G 1 - G 0 = w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) ∧
      G (e' * ew) - G (e' * ew - 1) = -((arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) ∧
      A.valuation (c₁ / c₂) ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (G (e' * ew) - G 0) := by
  exact SlopeLaw.nodeGauss_scaled R hqN hmodel hO W₀ hW₀ hreg hval K K' hKK' w hw hwφ hVI hBB' ϖ hϖ eK heK ε hε hqϖ c ew hew e' he' u hu hxy hmax hmax' hbr hres depth f hf hfK hfrac c₁ c₂ h₁ hu₁ h₂ hu₂ hc₁ hc₂ hc₁0 hc₂0 D hDf hdepth hN

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_yDepth_pow_eq (solution)
