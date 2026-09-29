-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_zpow_unit_principle_evalAt_y_of_ringEquiv_uvCrossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/aa82fda5-1dd2-5772-bc48-ce2882f690de

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_red_surjective_of_level
import Theorems.Thm_ValuationSubring_exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_evalAt_lt_one_iff_mem_maximalIdeal
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_evalAt_zpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_zpow_unit_principle_evalAt_y_of_ringEquiv_uvCrossingModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_zero"
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace SolE3_j1

section Eval

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

private theorem evalAt_add_j1 (v : Place L F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  refine v.algebraMap_residueField_injective ?_
  have hsum := v.algebraMap_evalAt hv (add_mem hf hg)
  rw [hsum, map_add, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg]
  exact map_add (residue v.toValuationSubring) ⟨f, hf⟩ ⟨g, hg⟩

private theorem evalAt_mul_j1 (v : Place L F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  refine v.algebraMap_residueField_injective ?_
  have hprod := v.algebraMap_evalAt hv (mul_mem hf hg)
  rw [hprod, map_mul, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg]
  exact map_mul (residue v.toValuationSubring) ⟨f, hf⟩ ⟨g, hg⟩

private theorem evalAt_algebraMap_j1 (v : Place L F) (a : L) : v.evalAt (algebraMap L F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have ha : (⟨algebraMap L F a, v.algebraMap_mem' a⟩ : v.toValuationSubring) = algebraMap L v.toValuationSubring a :=
    Subtype.ext (v.coe_algebraMap a).symm
  rw [ha, ← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply L v.toValuationSubring v.ResidueField,
    v.residueInv_algebraMap]

private theorem evalAt_pow_j1 (v : Place L F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, v.evalAt_one]
  | succ n ih => rw [pow_succ, evalAt_mul_j1 v hv (pow_mem hf n) hf, ih, pow_succ]

private theorem evalAt_eq_zero_of_one_le_ord_j1 (v : Place L F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : 1 ≤ v.ord f) : v.evalAt f = 0 := by
  rw [v.evalAt_of_mem hf]
  have h0 : residue v.toValuationSubring ⟨f, hf⟩ = 0 :=
    (residue_eq_zero_iff _).mpr (v.mk_mem_maximalIdeal_of_ord_pos hf (by omega))
  rw [h0, ← map_zero (algebraMap L v.ResidueField), v.residueInv_algebraMap]

private theorem one_le_ord_of_hasValue_zero_j1 (v : Place L F) {g : F} (hg0 : g ≠ 0) (hg : v.HasValue g 0) :
    1 ≤ v.ord g := by
  have hnonneg : 0 ≤ v.ord g := v.ord_nonneg_of_mem hg.mem
  have hne : v.ord g ≠ 0 := by
    intro h0
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hg0 h0
    have hr : residue v.toValuationSubring ⟨g, hm⟩ = 0 := by
      have h := hg.residue_eq
      rw [map_zero] at h
      exact h
    exact (residue_ne_zero_iff_isUnit _).mpr hu hr
  omega

private theorem hasValue_zero_of_one_le_ord_j1 (v : Place L F) {g : F} (hg0 : g ≠ 0) (h : 1 ≤ v.ord g) :
    v.HasValue g 0 := by
  have hmem : g ∈ v.toValuationSubring := v.mem_of_ord_nonneg hg0 (by omega)
  refine ⟨hmem, ?_⟩
  rw [map_zero]
  exact (residue_eq_zero_iff _).mpr (v.mk_mem_maximalIdeal_of_ord_pos hmem (by omega))

private theorem hasValue_add_j1 (v : Place L F) {g g' : F} {a a' : L} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') :=
  ⟨add_mem h.mem h'.mem, by
    rw [map_add (algebraMap L v.ResidueField), ← h.residue_eq, ← h'.residue_eq]
    exact map_add (residue v.toValuationSubring) ⟨g, h.mem⟩ ⟨g', h'.mem⟩⟩

end Eval

section Units

variable {F : Type*} [Field F]

private theorem inv_mem_j1 (S : ValuationSubring F) {f : F} (hf : f ∈ S) (hu : IsUnit (⟨f, hf⟩ : S)) : f⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have h1 : f * (((u⁻¹ : Sˣ) : S) : F) = 1 := by
    have h := congrArg (fun z : S => (z : F)) u.mul_inv
    simpa [hu] using h
  rw [(eq_inv_of_mul_eq_one_right h1).symm]
  exact SetLike.coe_mem _

private theorem zpow_mem_j1 (S : ValuationSubring F) {f : F} (hf : f ∈ S) (hu : IsUnit (⟨f, hf⟩ : S)) (n : ℤ) :
    f ^ n ∈ S := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast]
    exact pow_mem hf m
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_mem (inv_mem_j1 S hf hu) m

private theorem map_mk_inv_j1 (S : ValuationSubring F) {E : Type*} [Field E] (φ : S →+* E) {f : F} (hf : f ∈ S)
    (hu : IsUnit (⟨f, hf⟩ : S)) : φ ⟨f⁻¹, inv_mem_j1 S hf hu⟩ = (φ ⟨f, hf⟩)⁻¹ := by
  have hf0 : f ≠ 0 := fun h0 => hu.ne_zero (Subtype.ext h0)
  have hprod : φ ⟨f, hf⟩ * φ ⟨f⁻¹, inv_mem_j1 S hf hu⟩ = 1 := by
    rw [← map_mul]
    have hone : (⟨f, hf⟩ * ⟨f⁻¹, inv_mem_j1 S hf hu⟩ : S) = 1 := Subtype.ext (by simp [hf0])
    rw [hone, map_one]
  exact eq_inv_of_mul_eq_one_right hprod

private theorem map_mk_zpow_j1 (S : ValuationSubring F) {E : Type*} [Field E] (φ : S →+* E) {f : F} (hf : f ∈ S)
    (hu : IsUnit (⟨f, hf⟩ : S)) (n : ℤ) : φ ⟨f ^ n, zpow_mem_j1 S hf hu n⟩ = φ ⟨f, hf⟩ ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · have hpow : (⟨f ^ (m : ℤ), zpow_mem_j1 S hf hu m⟩ : S) = ⟨f, hf⟩ ^ m := Subtype.ext (by simp)
    rw [hpow, map_pow, zpow_natCast]
  · have hpow : (⟨f ^ (-(m : ℤ)), zpow_mem_j1 S hf hu (-(m : ℤ))⟩ : S) = ⟨f⁻¹, inv_mem_j1 S hf hu⟩ ^ m :=
      Subtype.ext (by simp)
    rw [hpow, map_pow, map_mk_inv_j1 S φ hf hu, inv_pow, zpow_neg, zpow_natCast]

end Units

section Finish

private theorem valuation_q_lt_one_j1 (q : ℕ) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) :
    A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := by
  have hmem : ((q : ℕ) : A) ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have h := hunit.map red
    rw [map_natCast, CharP.cast_eq_zero] at h
    exact not_isUnit_zero h
  have h := (A.valuation_lt_one_iff ((q : ℕ) : A)).mp hmem
  simpa using h

private theorem exists_pow_div_mem_j1 {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ} (hq : q.Prime)
    (hAq : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1) {b b' : AlgebraicClosure ℚ} (hb0 : b ≠ 0)
    (hb : A.valuation b < 1) (hb'0 : b' ≠ 0) (hb' : A.valuation b' < 1) : ∃ t : ℕ, b ^ t / b' ∈ A := by
  obtain ⟨n, hn, e, he⟩ := A.exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic hq hAq hb0
  obtain ⟨n', hn', e', he'⟩ := A.exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic hq hAq hb'0
  have hτ0 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]
    exact Nat.cast_ne_zero.mpr hq.ne_zero

  have hpow_lt : ∀ {s : A.ValueGroup}, s < 1 → ∀ m : ℕ, s ^ (m + 1) < 1 := fun {s} hs m => by
    rw [pow_succ]
    exact lt_of_le_of_lt ((mul_le_mul_left (pow_le_one' hs.le m) s).trans (one_mul s).le) hs

  have hnat : ∀ z : ℤ, A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ z ≤ 1 →
      ∃ c : ℕ, A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ z = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ c := by
    intro z hz
    rcases z with c | c
    · exact ⟨c, by rw [Int.ofNat_eq_natCast, zpow_natCast]⟩
    · exfalso
      rw [zpow_negSucc] at hz
      have h := mul_le_mul_right hz (A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ (c + 1))
      rw [mul_inv_cancel₀ (pow_ne_zero _ hτ0), mul_one] at h
      exact absurd (lt_of_le_of_lt h (hpow_lt hAq c)) (lt_irrefl _)
  have hbn : A.valuation b ^ n < 1 := by
    rw [← Nat.sub_add_cancel hn]
    exact hpow_lt hb (n - 1)
  have hb'n : A.valuation b' ^ n' < 1 := by
    rw [← Nat.sub_add_cancel hn']
    exact hpow_lt hb' (n' - 1)
  obtain ⟨c, hc⟩ := hnat e (by rw [← he]; exact hbn.le)
  obtain ⟨c', hc'⟩ := hnat e' (by rw [← he']; exact hb'n.le)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [he, hc, pow_zero] at hbn
    exact lt_irrefl _ hbn
  refine ⟨n * c', ?_⟩

  have h₁ : A.valuation (b ^ (n * c')) = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ (c * c') := by
    rw [map_pow, pow_mul, he, hc, ← pow_mul]
  have h₂ : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ (c * c')
      ≤ A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ c' := by
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.le_mul_of_pos_left c' (Nat.pos_of_ne_zero hc0))
    rw [hr, pow_add]
    exact (mul_le_mul_right (pow_le_one' hAq.le r) _).trans (mul_one _).le
  have h₃ : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ c' ≤ A.valuation b' := by
    rw [← hc', ← he', ← Nat.sub_add_cancel hn', pow_succ]
    exact (mul_le_mul_left (pow_le_one' hb'.le _) _).trans (one_mul _).le

  have hb'v : A.valuation b' ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]
    exact hb'0
  have hmul : b ^ (n * c') / b' * b' = b ^ (n * c') := by
    rw [div_mul_cancel₀ _ hb'0]
  have hle : A.valuation (b ^ (n * c') / b') * A.valuation b' ≤ A.valuation b' := by
    rw [← map_mul, hmul, h₁]
    exact h₂.trans h₃
  have hval := mul_le_mul_right hle (A.valuation b')⁻¹
  rw [mul_comm (A.valuation _) (A.valuation b'), ← mul_assoc, inv_mul_cancel₀ hb'v, one_mul] at hval
  exact A.mem_of_valuation_le_one _ hval

end Finish

section Node

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem rat_j1 (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : V.IsRational :=
  isRational_place_modularFunctionFieldBar (N * q) V

private theorem isUnit_of_red_ne_zero_j1 (P : PlaceSpecialization A q N data hKr k red hα hβ) (a : A)
    (ha : red a ≠ 0) : IsUnit a := by
  by_contra hu
  obtain ⟨b, hb⟩ := P.red_surjective_of_level (red a)⁻¹
  have hm : a * b ∈ maximalIdeal A := (maximalIdeal A).mul_mem_right b ((mem_maximalIdeal a).mpr hu)
  have hunit : IsUnit (a * b - 1) := by
    have h := isUnit_one_sub_self_of_mem_nonunits (a * b) ((mem_maximalIdeal _).mp hm)
    rwa [← IsUnit.neg_iff, neg_sub] at h
  have h0 : red (a * b - 1) = 0 := by rw [map_sub, map_mul, hb, mul_inv_cancel₀ ha, map_one, sub_self]
  exact (hunit.map red).ne_zero h0

private theorem red_eq_zero_of_not_isUnit_j1 (P : PlaceSpecialization A q N data hKr k red hα hβ) (a : A)
    (ha : ¬ IsUnit a) : red a = 0 := by
  by_contra h
  exact ha (isUnit_of_red_ne_zero_j1 P a h)

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

set_option synthInstance.maxHeartbeats 1600000 in

private abbrev gauss₁_j1 : ValuationSubring ↥(modularFunctionFieldBar (N * q)) := R.R₁.integers

set_option synthInstance.maxHeartbeats 1600000 in

private abbrev gauss₂_j1 : ValuationSubring ↥(modularFunctionFieldBar (N * q)) := R.R₂.integers

set_option synthInstance.maxHeartbeats 1600000 in

private theorem isUnit_gauss₁_j1 {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ gauss₁_j1 R)
    (h : R.residue₁ ⟨f, hf⟩ ≠ 0) : IsUnit (⟨f, hf⟩ : gauss₁_j1 R) :=
  R.R₁.isUnit_of_residue_ne_zero fun h0 => h (by show R.ι (R.R₁.residue _) = 0; rw [h0, map_zero])

set_option synthInstance.maxHeartbeats 1600000 in

private theorem isUnit_gauss₂_j1 {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ gauss₂_j1 R)
    (h : R.residue₂ ⟨f, hf⟩ ≠ 0) : IsUnit (⟨f, hf⟩ : gauss₂_j1 R) :=
  R.R₂.isUnit_of_residue_ne_zero fun h0 => h (by show R.ι (R.R₂.residue _) = 0; rw [h0, map_zero])

set_option synthInstance.maxHeartbeats 1600000 in

private theorem residue_pre_ne_zero_j1 {f : ↥(modularFunctionFieldBar (N * q))} (h₁ : f ∈ gauss₁_j1 R)
    (h₂ : f ∈ gauss₂_j1 R) (hr₁ : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hr₂ : R.residue₂ ⟨f, h₂⟩ ≠ 0) :
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨f, h₂⟩ ≠ 0 :=
  ⟨fun h0 => hr₁ (by show R.ι (R.R₁.residue _) = 0; rw [h0, map_zero]),
    fun h0 => hr₂ (by show R.ι (R.R₂.residue _) = 0; rw [h0, map_zero])⟩

set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_scaling₁_j1 {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ≠ 0) :
    ∃ d : AlgebraicClosure ℚ, d ≠ 0 ∧
      ∃ h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d * f ∈ gauss₁_j1 R,
        R.residue₁ ⟨_, h⟩ ≠ 0 := by
  obtain ⟨d, hd, hres⟩ := R.R₁.exists_smul_mem f hf
  have hdf : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d * f ∈ gauss₁_j1 R := by
    rw [← Algebra.smul_def]
    exact hd
  refine ⟨d, R.R₁.smul_const_ne_zero hd hres, hdf, ?_⟩
  have hcongr : R.residue₁ ⟨_, hdf⟩ = R.residue₁ ⟨d • f, hd⟩ :=
    congrArg R.residue₁ (Subtype.ext (Algebra.smul_def d f).symm)
  rw [hcongr]
  exact (map_ne_zero R.ι).mpr hres

set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_scaling₂_j1 {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ≠ 0) :
    ∃ d : AlgebraicClosure ℚ, d ≠ 0 ∧
      ∃ h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d * f ∈ gauss₂_j1 R,
        R.residue₂ ⟨_, h⟩ ≠ 0 := by
  obtain ⟨d, hd, hres⟩ := R.R₂.exists_smul_mem f hf
  have hdf : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d * f ∈ gauss₂_j1 R := by
    rw [← Algebra.smul_def]
    exact hd
  refine ⟨d, R.R₂.smul_const_ne_zero hd hres, hdf, ?_⟩
  have hcongr : R.residue₂ ⟨_, hdf⟩ = R.residue₂ ⟨d • f, hd⟩ :=
    congrArg R.residue₂ (Subtype.ext (Algebra.smul_def d f).symm)
  rw [hcongr]
  exact (map_ne_zero R.ι).mpr hres

set_option synthInstance.maxHeartbeats 1600000 in

private theorem algebraMap_mem_gauss_j1 (a : A) :
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ gauss₁_j1 R ∧
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ gauss₂_j1 R :=
  ⟨(R.R₁.algebraMap_mem_iff _).mpr a.2, (R.R₂.algebraMap_mem_iff _).mpr a.2⟩

set_option synthInstance.maxHeartbeats 1600000 in

private theorem residue_algebraMap_j1 (a : A) :
    R.residue₁ ⟨_, (algebraMap_mem_gauss_j1 R a).1⟩ = algebraMap k (modularFunctionFieldC k N) (red a) ∧
      R.residue₂ ⟨_, (algebraMap_mem_gauss_j1 R a).2⟩ = algebraMap k (modularFunctionFieldC k N) (red a) := by
  have hcoe : ∀ x : ResidueField A, R.ι (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) x)
      = algebraMap k (modularFunctionFieldC k N) (R.redBar x) := by
    intro x
    apply Subtype.ext
    rw [R.ι_coe]
    have h₁ : ((algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) x
          : modularFunctionFieldFullC (ResidueField A) N) : LaurentSeries (ResidueField A))
        = algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) x := rfl
    have h₂ : ((algebraMap k (modularFunctionFieldC k N) (R.redBar x) : modularFunctionFieldC k N) : LaurentSeries k)
        = algebraMap k (LaurentSeries k) (R.redBar x) := rfl
    rw [h₁, h₂, algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]
  constructor
  · show R.ι (R.R₁.residue _) = _
    rw [R.R₁.residue_algebraMap a, hcoe, R.redBar_residue]
  · show R.ι (R.R₂.residue _) = _
    rw [R.R₂.residue_algebraMap a, hcoe, R.redBar_residue]

private theorem exists_pow_div_mem_gauss₂_j1 {G y : ↥(modularFunctionFieldBar (N * q))} (hG : G ∈ gauss₂_j1 R)
    (hG0 : G ≠ 0) (hGr : R.residue₂ ⟨G, hG⟩ = 0) (hy : y ∈ gauss₂_j1 R) (hy0 : y ≠ 0) (hyr : R.residue₂ ⟨y, hy⟩ = 0) :
    ∃ t : ℕ, G ^ t / y ∈ gauss₂_j1 R := by
  have key : ∀ {z : ↥(modularFunctionFieldBar (N * q))} (hz : z ∈ gauss₂_j1 R), R.residue₂ ⟨z, hz⟩ = 0 →
      ∀ {d : AlgebraicClosure ℚ} (hdz : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d * z
        ∈ gauss₂_j1 R), R.residue₂ ⟨_, hdz⟩ ≠ 0 → d ∉ A := by
    intro z hz hzr d hdz hdr hdA
    apply hdr
    have hsplit : R.residue₂ ⟨_, hdz⟩ = R.residue₂ (⟨_, (algebraMap_mem_gauss_j1 R ⟨d, hdA⟩).2⟩ * ⟨z, hz⟩) := rfl
    rw [hsplit, map_mul R.residue₂, hzr, mul_zero]
  obtain ⟨d, hd0, hdG, hdGr⟩ := exists_scaling₂_j1 R hG0
  obtain ⟨d', hd'0, hd'y, hd'yr⟩ := exists_scaling₂_j1 R hy0
  have hdA : d ∉ A := key hG hGr hdG hdGr
  have hd'A : d' ∉ A := key hy hyr hd'y hd'yr

  have hinvA : ∀ {e : AlgebraicClosure ℚ}, e ∉ A → A.valuation e⁻¹ < 1 := by
    intro e heA
    have he : e⁻¹ ∈ A := (A.mem_or_inv_mem e).resolve_left heA
    have hnu : ¬ IsUnit (⟨e⁻¹, he⟩ : A) := fun hu => heA (by simpa using inv_mem_j1 A he hu)
    have h := (A.valuation_lt_one_iff ⟨e⁻¹, he⟩).mp ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu))
    simpa using h
  obtain ⟨t, hmem⟩ := exists_pow_div_mem_j1 (Fact.out : q.Prime) (valuation_q_lt_one_j1 q red) (inv_ne_zero hd0)
    (hinvA hdA) (inv_ne_zero hd'0) (hinvA hd'A)
  refine ⟨t, ?_⟩
  have hdF : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d ≠ 0 :=
    (map_ne_zero (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))).mpr hd0
  have hd'F : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d' ≠ 0 :=
    (map_ne_zero (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))).mpr hd'0
  have hG_eq : G = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d⁻¹
      * (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d * G) := by
    rw [← mul_assoc, map_inv₀ (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      inv_mul_cancel₀ hdF, one_mul]
  have hy_eq : y = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d'⁻¹
      * (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d' * y) := by
    rw [← mul_assoc, map_inv₀ (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      inv_mul_cancel₀ hd'F, one_mul]
  have hid : G ^ t / y = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (d⁻¹ ^ t / d'⁻¹)
      * ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d * G) ^ t
        * (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d' * y)⁻¹) := by
    conv_lhs => rw [hG_eq, hy_eq]
    simp only [map_div₀, map_pow, map_inv₀]
    ring
  rw [hid]
  exact mul_mem (algebraMap_mem_gauss_j1 R ⟨_, hmem⟩).2
    (mul_mem (pow_mem hdG t) (inv_mem_j1 _ hd'y (isUnit_gauss₂_j1 R hd'y hd'yr)))

variable (w : Place k (modularFunctionFieldC k N))

private theorem isUnit_evalAt_j1 (hvalA : R.ValueIntegralityLaw w) {g : ↥(modularFunctionFieldBar (N * q))}
    (hg : g ∈ R.nodeIntegers w) (hgi : g⁻¹ ∈ R.nodeIntegers w) (hg0 : g ≠ 0)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    ∃ h : V.evalAt g ∈ A, IsUnit (⟨V.evalAt g, h⟩ : A) := by
  refine ⟨hvalA g hg V hV, isUnit_iff_exists_inv.mpr ⟨⟨V.evalAt g⁻¹, hvalA g⁻¹ hgi V hV⟩, ?_⟩⟩
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
  show V.evalAt g * V.evalAt g⁻¹ = 1
  rw [← evalAt_mul_j1 V (rat_j1 V) (hg.2.2 V hV) (hgi.2.2 V hV), mul_inv_cancel₀ hg0, V.evalAt_one]

private theorem mem_nodeIntegers_of_ord_j1 {g : ↥(modularFunctionFieldBar (N * q))} (h₁ : g ∈ gauss₁_j1 R)
    (h₂ : g ∈ gauss₂_j1 R)
    (hord : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → V.ord g = 0)
    (hg0 : g ≠ 0) : g ∈ R.nodeIntegers w :=
  ⟨h₁, h₂, fun V hV => V.mem_of_ord_nonneg hg0 (hord V hV).ge⟩

private theorem inv_mem_nodeIntegers_j1 {g : ↥(modularFunctionFieldBar (N * q))} (h₁ : g⁻¹ ∈ gauss₁_j1 R)
    (h₂ : g⁻¹ ∈ gauss₂_j1 R)
    (hord : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → V.ord g = 0)
    (hg0 : g ≠ 0) : g⁻¹ ∈ R.nodeIntegers w :=
  ⟨h₁, h₂, fun V hV => V.mem_of_ord_nonneg (inv_ne_zero hg0) (le_of_eq (by rw [V.ord_inv, hord V hV, neg_zero]))⟩

private theorem residue₁_add_j1 {a b : ↥(modularFunctionFieldBar (N * q))} (ha : a ∈ gauss₁_j1 R)
    (hb : b ∈ gauss₁_j1 R) :
    R.residue₁ ⟨a + b, add_mem ha hb⟩ = R.residue₁ ⟨a, ha⟩ + R.residue₁ ⟨b, hb⟩ := by
  have hsplit : R.residue₁ ⟨a + b, add_mem ha hb⟩ = R.residue₁ (⟨a, ha⟩ + ⟨b, hb⟩) := rfl
  rw [hsplit, map_add R.residue₁]

private theorem residue₂_add_j1 {a b : ↥(modularFunctionFieldBar (N * q))} (ha : a ∈ gauss₂_j1 R)
    (hb : b ∈ gauss₂_j1 R) :
    R.residue₂ ⟨a + b, add_mem ha hb⟩ = R.residue₂ ⟨a, ha⟩ + R.residue₂ ⟨b, hb⟩ := by
  have hsplit : R.residue₂ ⟨a + b, add_mem ha hb⟩ = R.residue₂ (⟨a, ha⟩ + ⟨b, hb⟩) := rfl
  rw [hsplit, map_add R.residue₂]

private theorem residue₁_mul_j1 {a b : ↥(modularFunctionFieldBar (N * q))} (ha : a ∈ gauss₁_j1 R)
    (hb : b ∈ gauss₁_j1 R) :
    R.residue₁ ⟨a * b, mul_mem ha hb⟩ = R.residue₁ ⟨a, ha⟩ * R.residue₁ ⟨b, hb⟩ := by
  have hsplit : R.residue₁ ⟨a * b, mul_mem ha hb⟩ = R.residue₁ (⟨a, ha⟩ * ⟨b, hb⟩) := rfl
  rw [hsplit, map_mul R.residue₁]

private theorem residue₂_mul_j1 {a b : ↥(modularFunctionFieldBar (N * q))} (ha : a ∈ gauss₂_j1 R)
    (hb : b ∈ gauss₂_j1 R) :
    R.residue₂ ⟨a * b, mul_mem ha hb⟩ = R.residue₂ ⟨a, ha⟩ * R.residue₂ ⟨b, hb⟩ := by
  have hsplit : R.residue₂ ⟨a * b, mul_mem ha hb⟩ = R.residue₂ (⟨a, ha⟩ * ⟨b, hb⟩) := rfl
  rw [hsplit, map_mul R.residue₂]

private theorem residue₁_one_j1 : R.residue₁ ⟨1, one_mem _⟩ = 1 := map_one R.residue₁

private theorem residue₂_one_j1 : R.residue₂ ⟨1, one_mem _⟩ = 1 := map_one R.residue₂

private theorem residue₁_zpow_j1 {g : ↥(modularFunctionFieldBar (N * q))} (hg : g ∈ gauss₁_j1 R)
    (hgr : R.residue₁ ⟨g, hg⟩ ≠ 0) (n : ℤ) (hgn : g ^ n ∈ gauss₁_j1 R) :
    R.residue₁ ⟨g ^ n, hgn⟩ = R.residue₁ ⟨g, hg⟩ ^ n :=
  map_mk_zpow_j1 (gauss₁_j1 R) R.residue₁ hg (isUnit_gauss₁_j1 R hg hgr) n

private theorem residue₁_inv_j1 {g : ↥(modularFunctionFieldBar (N * q))} (hg : g ∈ gauss₁_j1 R)
    (hgr : R.residue₁ ⟨g, hg⟩ ≠ 0) (hgi : g⁻¹ ∈ gauss₁_j1 R) : R.residue₁ ⟨g⁻¹, hgi⟩ = (R.residue₁ ⟨g, hg⟩)⁻¹ :=
  map_mk_inv_j1 (gauss₁_j1 R) R.residue₁ hg (isUnit_gauss₁_j1 R hg hgr)

private theorem residue₂_eq_zero_of_eq_mul_j1 {e : A} (he : red e = 0) {H : ↥(modularFunctionFieldBar (N * q))}
    (hH : H ∈ gauss₂_j1 R) {G : ↥(modularFunctionFieldBar (N * q))} (hG : G ∈ gauss₂_j1 R)
    (hGH : G = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (e : AlgebraicClosure ℚ) * H) :
    R.residue₂ ⟨G, hG⟩ = 0 := by
  have hsplit : R.residue₂ ⟨G, hG⟩ = R.residue₂ ⟨_, mul_mem (algebraMap_mem_gauss_j1 R e).2 hH⟩ :=
    congrArg R.residue₂ (Subtype.ext hGH)
  rw [hsplit, residue₂_mul_j1 R (algebraMap_mem_gauss_j1 R e).2 hH, (residue_algebraMap_j1 R e).2, he,
    map_zero (algebraMap k (modularFunctionFieldC k N)), zero_mul]

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private theorem y_ne_zero_j1 [IsAlgClosed k] (c : R.NodeCoordinates K w) :
    ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
  intro h0
  apply c.nodeResidue₁_y_ne_zero
  rw [show (⟨c.y, c.y.2.1⟩ : ↥(R.nodeIntegers w)) = 0 from Subtype.ext h0, map_zero]

private theorem x_ne_zero_j1 [IsAlgClosed k] (c : R.NodeCoordinates K w) :
    ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
  intro h0
  apply c.nodeResidue₂_x_ne_zero
  rw [show (⟨c.x, c.x.2.1⟩ : ↥(R.nodeIntegers w)) = 0 from Subtype.ext h0, map_zero]

private theorem ord_unit_eq_zero_j1 {u : ↥(R.nodeIntegersOver K w)} (hu : IsUnit u)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    V.ord (u : ↥(modularFunctionFieldBar (N * q))) = 0 := by
  obtain ⟨u', hu'⟩ : ∃ u' : ↥(R.nodeIntegersOver K w), u * u' = 1 :=
    ⟨(hu.unit⁻¹ : (↥(R.nodeIntegersOver K w))ˣ), hu.mul_val_inv⟩
  have hprod : (u : ↥(modularFunctionFieldBar (N * q))) * u' = 1 := by
    have h := congrArg (fun z : ↥(R.nodeIntegersOver K w) => (z : ↥(modularFunctionFieldBar (N * q)))) hu'
    simpa using h
  have hsum := V.ord_mul (left_ne_zero_of_mul_eq_one hprod) (right_ne_zero_of_mul_eq_one hprod)
  rw [hprod, V.ord_one] at hsum
  have h₁ := R.ord_nonneg_of_mem_nodeIntegers u.2.1 hV
  have h₂ := R.ord_nonneg_of_mem_nodeIntegers u'.2.1 hV
  omega

private theorem ord_y_eq_zero_j1 [IsAlgClosed k] (c : R.NodeCoordinates K w) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    V.ord (c.y : ↥(modularFunctionFieldBar (N * q))) = 0 := by
  have hx0 := x_ne_zero_j1 R w K c
  have hy0 := y_ne_zero_j1 R w K c

  have heq : (c.x : ↥(modularFunctionFieldBar (N * q))) * c.y
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((ϖ : AlgebraicClosure ℚ) ^ E₀) * u := by
    have h := congrArg (fun z : ↥(R.nodeIntegersOver K w) => (z : ↥(modularFunctionFieldBar (N * q)))) hxy
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, R.coe_nodeConst] at h
    rw [h, map_pow (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))]
  have hu0 : (u : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at heq
    exact mul_ne_zero hx0 hy0 heq
  have hconst0 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((ϖ : AlgebraicClosure ℚ) ^ E₀)
      ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at heq
    exact mul_ne_zero hx0 hy0 heq
  have hϖ0 : (ϖ : AlgebraicClosure ℚ) ^ E₀ ≠ 0 := fun h0 => hconst0 (by rw [h0, map_zero])
  have hords := V.ord_mul hx0 hy0
  rw [heq, V.ord_mul hconst0 hu0, ConstantReduction.ord_algebraMap V hϖ0, ord_unit_eq_zero_j1 R w K hu V hV] at hords
  have h₁ := R.ord_nonneg_of_mem_nodeIntegers c.x.2.1 hV
  have h₂ := R.ord_nonneg_of_mem_nodeIntegers c.y.2.1 hV
  omega

private theorem y_mem_maximalIdeal_j1 [IsAlgClosed k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (c : R.NodeCoordinates K w) : c.y ∈ maximalIdeal ↥(R.nodeIntegersOver K w) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u', hu'⟩ : ∃ u' : ↥(R.nodeIntegersOver K w), c.y * u' = 1 :=
    ⟨(hu.unit⁻¹ : (↥(R.nodeIntegersOver K w))ˣ), hu.mul_val_inv⟩
  have hprod : (c.y : ↥(modularFunctionFieldBar (N * q))) * u' = 1 := by
    have h := congrArg (fun z : ↥(R.nodeIntegersOver K w) => (z : ↥(modularFunctionFieldBar (N * q)))) hu'
    simpa using h
  have hy : (c.y : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegers w := c.y.2.1
  have hysnd : R.residue₂ ⟨c.y, hy.2.1⟩ = 0 := c.y_snd
  have hu'₂ : (u' : ↥(modularFunctionFieldBar (N * q))) ∈ gauss₂_j1 R := u'.2.1.2.1
  have e : R.residue₂ ⟨_, mul_mem hy.2.1 hu'₂⟩ = R.residue₂ ⟨1, one_mem _⟩ := congrArg R.residue₂ (Subtype.ext hprod)
  rw [residue₂_mul_j1 R hy.2.1 hu'₂, hysnd, zero_mul, residue₂_one_j1 R] at e
  exact zero_ne_one e

private theorem valuation_evalAt_y_lt_one_j1 [IsAlgClosed k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hvalA : R.ValueIntegralityLaw w) (c : R.NodeCoordinates K w)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (N * q)))) < 1 :=
  (R.valuation_evalAt_lt_one_iff_mem_maximalIdeal K w hvalA V hV c.y).mpr (y_mem_maximalIdeal_j1 R w K c)

private theorem exists_zero_over_j1 [DecidableEq k] (hqN : ¬ q ∣ N) (hord : R.OrderLawFixed)
    (hw : w ∈ ssPlaces q N k) {G : ↥(modularFunctionFieldBar (N * q))} (hG : G ∈ R.nodeIntegers w)
    (hr₁ : R.residue₁ ⟨G, hG.1⟩ ≠ 0) (hr₂ : R.residue₂ ⟨G, hG.2.1⟩ ≠ 0) (hw₁ : 1 ≤ w.ord (R.residue₁ ⟨G, hG.1⟩))
    (hw₂ : 0 ≤ (frobOnPlacesGeomLevel k N data hKr w).ord (R.residue₂ ⟨G, hG.2.1⟩)) :
    ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w ∧ 1 ≤ V.ord G := by
  have hG0 : G ≠ 0 := by
    rintro rfl
    exact hr₁ (map_zero R.residue₁)
  obtain ⟨hp₁, hp₂⟩ := residue_pre_ne_zero_j1 R hG.1 hG.2.1 hr₁ hr₂
  obtain ⟨D, hD, -⟩ := (hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)).exists_divisor G hG0
  have hsum := hord G hG.1 hG.2.1 hp₁ hp₂ D hD w
    (frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P w hw) hw.2.1
  have hpos : Finsupp.mapDomain P.reduceFst D w ≠ 0 := by rw [hsum]; omega
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply] at hpos
  obtain ⟨V, -, hV⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
  simp only [Finsupp.single_apply] at hV
  split_ifs at hV with hfV
  · refine ⟨V, hfV, ?_⟩
    have hnonneg := R.ord_nonneg_of_mem_nodeIntegers hG hfV
    rw [hD V] at hV
    omega
  · exact absurd rfl hV

private theorem residue₂_crossing_j1 {G aF h : ↥(modularFunctionFieldBar (N * q))} (hG : G ∈ R.nodeIntegers w)
    (haF : aF ∈ R.nodeIntegers w) (hh : h ∈ R.nodeIntegers w) (hG₂ : R.residue₂ ⟨G, hG.2.1⟩ = 0) {β : k}
    (ha₂ : R.residue₂ ⟨aF, haF.2.1⟩ = algebraMap k (modularFunctionFieldC k N) (-β))
    (hh₂ : R.residue₂ ⟨h, hh.2.1⟩ = 1) :
    R.residue₂ ⟨G + aF * h, (add_mem hG (mul_mem haF hh)).2.1⟩ = algebraMap k (modularFunctionFieldC k N) (-β) := by
  rw [residue₂_add_j1 R hG.2.1 (mul_mem haF.2.1 hh.2.1), residue₂_mul_j1 R haF.2.1 hh.2.1, hG₂, ha₂, hh₂, zero_add,
    mul_one]

private theorem hasValue_crossing_j1 {G aF h : ↥(modularFunctionFieldBar (N * q))} (hG : G ∈ R.nodeIntegers w)
    (haF : aF ∈ R.nodeIntegers w) (hh : h ∈ R.nodeIntegers w) {β : k} (hGβ : w.HasValue (R.residue₁ ⟨G, hG.1⟩) β)
    (ha₁ : R.residue₁ ⟨aF, haF.1⟩ = algebraMap k (modularFunctionFieldC k N) (-β))
    (hh₁ : w.HasValue (R.residue₁ ⟨h, hh.1⟩) 1) :
    w.HasValue (R.residue₁ ⟨G + aF * h, (add_mem hG (mul_mem haF hh)).1⟩) 0 := by
  rw [residue₁_add_j1 R hG.1 (mul_mem haF.1 hh.1), residue₁_mul_j1 R haF.1 hh.1, ha₁]
  have hv := hasValue_add_j1 w hGβ ((w.hasValue_algebraMap (-β)).mul hh₁)
  rwa [mul_one, add_neg_cancel] at hv

private theorem exists_zero_crossing_j1 [DecidableEq k] (hqN : ¬ q ∣ N) (hord : R.OrderLawFixed)
    (hw : w ∈ ssPlaces q N k) {G aF h : ↥(modularFunctionFieldBar (N * q))} (hG : G ∈ R.nodeIntegers w)
    (haF : aF ∈ R.nodeIntegers w) (hh : h ∈ R.nodeIntegers w) {β : k} (hβ : β ≠ 0)
    (hval : w.HasValue (R.residue₁ ⟨G + aF * h, (add_mem hG (mul_mem haF hh)).1⟩) 0)
    (hres₂ : R.residue₂ ⟨G + aF * h, (add_mem hG (mul_mem haF hh)).2.1⟩
      = algebraMap k (modularFunctionFieldC k N) (-β))
    (hne : R.residue₁ ⟨G + aF * h, (add_mem hG (mul_mem haF hh)).1⟩ ≠ 0) :
    ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = w ∧ 1 ≤ V.ord (G + aF * h) := by
  have hβ' : (-β) ≠ 0 := neg_ne_zero.mpr hβ
  refine exists_zero_over_j1 R w hqN hord hw (add_mem hG (mul_mem haF hh)) hne ?_ ?_ ?_
  · rw [hres₂]
    exact (map_ne_zero (algebraMap k (modularFunctionFieldC k N))).mpr hβ'
  · exact one_le_ord_of_hasValue_zero_j1 w hne hval
  · exact le_of_eq (by rw [hres₂, ConstantReduction.ord_algebraMap _ hβ'])

private theorem valuation_evalAt_eq_one_crossing_j1 {G aF h : ↥(modularFunctionFieldBar (N * q))}
    (hG : G ∈ R.nodeIntegers w) (haF : aF ∈ R.nodeIntegers w) (hh : h ∈ R.nodeIntegers w) {a : A} (hau : IsUnit a)
    (haV : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V.evalAt aF = (a : AlgebraicClosure ℚ))
    {V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hV₀ : P.reduceFst V₀ = w)
    (hhV : A.valuation (V₀.evalAt h) = 1) (hzero : 1 ≤ V₀.ord (G + aF * h)) : A.valuation (V₀.evalAt G) = 1 := by
  have h0 := evalAt_eq_zero_of_one_le_ord_j1 V₀ ((add_mem hG (mul_mem haF hh)).2.2 V₀ hV₀) hzero
  rw [evalAt_add_j1 V₀ (rat_j1 V₀) (hG.2.2 V₀ hV₀) (mul_mem (haF.2.2 V₀ hV₀) (hh.2.2 V₀ hV₀)),
    evalAt_mul_j1 V₀ (rat_j1 V₀) (haF.2.2 V₀ hV₀) (hh.2.2 V₀ hV₀), haV V₀] at h0
  rw [eq_neg_of_add_eq_zero_left h0, A.valuation.map_neg, map_mul A.valuation, hhV, mul_one]
  exact (A.valuation_eq_one_iff a).mp hau

private theorem exists_pow_div_y_mem_nodeIntegers_j1 [IsAlgClosed k] (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u) {G : ↥(modularFunctionFieldBar (N * q))} (hG : G ∈ R.nodeIntegers w)
    (hG0 : G ≠ 0)
    (hGord : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → V.ord G = 0)
    (hG₂ : R.residue₂ ⟨G, hG.2.1⟩ = 0) :
    ∃ t : ℕ, G ^ t / (c.y : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegers w := by
  have hy : (c.y : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegers w := c.y.2.1
  have hy0 := y_ne_zero_j1 R w K c
  have hyne : R.residue₁ ⟨c.y, hy.1⟩ ≠ 0 := c.nodeResidue₁_y_ne_zero
  have hysnd : R.residue₂ ⟨c.y, hy.2.1⟩ = 0 := c.y_snd
  obtain ⟨t, hZ₂⟩ := exists_pow_div_mem_gauss₂_j1 R hG.2.1 hG0 hG₂ hy.2.1 hy0 hysnd
  have hZ₁ : G ^ t / c.y ∈ gauss₁_j1 R := by
    rw [div_eq_mul_inv]
    exact mul_mem (pow_mem hG.1 t) (inv_mem_j1 _ hy.1 (isUnit_gauss₁_j1 R hy.1 hyne))
  refine ⟨t, mem_nodeIntegers_of_ord_j1 R w hZ₁ hZ₂ (fun V hV => ?_) (div_ne_zero (pow_ne_zero t hG0) hy0)⟩
  rw [div_eq_mul_inv, V.ord_mul (pow_ne_zero t hG0) (inv_ne_zero hy0), V.ord_inv,
    ord_y_eq_zero_j1 R w K c ϖ E₀ u hu hxy V hV, ← zpow_natCast, V.ord_zpow, hGord V hV]
  simp

private theorem crossing_contradiction_j1 [IsAlgClosed k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hvalA : R.ValueIntegralityLaw w) (c : R.NodeCoordinates K w) {G : ↥(modularFunctionFieldBar (N * q))}
    (hG : G ∈ R.nodeIntegers w) {t : ℕ} (hZ : G ^ t / (c.y : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegers w)
    {V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hV₀ : P.reduceFst V₀ = w)
    (hGval : A.valuation (V₀.evalAt G) = 1) : False := by
  have hy : (c.y : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegers w := c.y.2.1
  have hy0 := y_ne_zero_j1 R w K c
  have hyZ : (c.y : ↥(modularFunctionFieldBar (N * q))) * (G ^ t / c.y) = G ^ t := by
    rw [div_eq_mul_inv, mul_comm (G ^ t), ← mul_assoc, mul_inv_cancel₀ hy0, one_mul]
  have hfac : V₀.evalAt G ^ t = V₀.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))) * V₀.evalAt (G ^ t / c.y) := by
    rw [← evalAt_mul_j1 V₀ (rat_j1 V₀) (hy.2.2 V₀ hV₀) (hZ.2.2 V₀ hV₀), hyZ,
      evalAt_pow_j1 V₀ (rat_j1 V₀) (hG.2.2 V₀ hV₀)]
  have hZle : A.valuation (V₀.evalAt (G ^ t / c.y)) ≤ 1 := (A.valuation_le_one_iff _).mpr (hvalA _ hZ V₀ hV₀)
  have hlt := valuation_evalAt_y_lt_one_j1 R w K hvalA c V₀ hV₀
  have hcontra : A.valuation (V₀.evalAt G) ^ t < 1 := by
    rw [← map_pow A.valuation, hfac, map_mul A.valuation]
    calc A.valuation (V₀.evalAt (c.y : ↥(modularFunctionFieldBar (N * q)))) * A.valuation (V₀.evalAt (G ^ t / c.y))
        ≤ A.valuation (V₀.evalAt (c.y : ↥(modularFunctionFieldBar (N * q)))) * 1 := mul_le_mul_right hZle _
      _ = A.valuation (V₀.evalAt (c.y : ↥(modularFunctionFieldBar (N * q)))) := mul_one _
      _ < 1 := hlt
  rw [hGval, one_pow] at hcontra
  exact lt_irrefl _ hcontra

private theorem branch_cross_aux_j1 [IsAlgClosed k] [DecidableEq k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hqN : ¬ q ∣ N) (hord : R.OrderLawFixed) (hw : w ∈ ssPlaces q N k) (hvalA : R.ValueIntegralityLaw w)
    (c : R.NodeCoordinates K w) (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w))
    (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u)
    {G : ↥(modularFunctionFieldBar (N * q))} (hG : G ∈ R.nodeIntegers w) (hG0 : G ≠ 0)
    (hGord : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → V.ord G = 0)
    (hG₂ : R.residue₂ ⟨G, hG.2.1⟩ = 0) {β : k} (hβ : β ≠ 0) (hGβ : w.HasValue (R.residue₁ ⟨G, hG.1⟩) β)
    {a : A} (hau : IsUnit a) {aF : ↥(modularFunctionFieldBar (N * q))} (haF : aF ∈ R.nodeIntegers w)
    (ha₁ : R.residue₁ ⟨aF, haF.1⟩ = algebraMap k (modularFunctionFieldC k N) (-β))
    (ha₂ : R.residue₂ ⟨aF, haF.2.1⟩ = algebraMap k (modularFunctionFieldC k N) (-β))
    (haV : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V.evalAt aF = (a : AlgebraicClosure ℚ))
    {h : ↥(modularFunctionFieldBar (N * q))} (hh : h ∈ R.nodeIntegers w) (hh₁ : w.HasValue (R.residue₁ ⟨h, hh.1⟩) 1)
    (hh₂ : R.residue₂ ⟨h, hh.2.1⟩ = 1)
    (hhV : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      A.valuation (V.evalAt h) = 1)
    (hne : R.residue₁ ⟨G + aF * h, (add_mem hG (mul_mem haF hh)).1⟩ ≠ 0) : False := by
  obtain ⟨V₀, hV₀, hzero⟩ := exists_zero_crossing_j1 R w hqN hord hw hG haF hh hβ
    (hasValue_crossing_j1 R w hG haF hh hGβ ha₁ hh₁) (residue₂_crossing_j1 R w hG haF hh hG₂ ha₂ hh₂) hne
  obtain ⟨t, hZ⟩ := exists_pow_div_y_mem_nodeIntegers_j1 R w K c ϖ E₀ u hu hxy hG hG0 hGord hG₂
  exact crossing_contradiction_j1 R w K hvalA c hG hZ hV₀
    (valuation_evalAt_eq_one_crossing_j1 R w hG haF hh hau haV hV₀ (hhV V₀ hV₀) hzero)

private theorem candidate_one_j1 :
    ∃ hh : (1 : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegers w,
      w.HasValue (R.residue₁ ⟨1, hh.1⟩) 1 ∧ R.residue₂ ⟨1, hh.2.1⟩ = 1 ∧
        ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
          A.valuation (V.evalAt (1 : ↥(modularFunctionFieldBar (N * q)))) = 1 := by
  refine ⟨one_mem _, ?_, residue₂_one_j1 R, fun V _ => ?_⟩
  · rw [residue₁_one_j1 R]
    exact w.hasValue_one
  · rw [V.evalAt_one, map_one]

private theorem candidate_one_add_y_j1 [IsAlgClosed k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hvalA : R.ValueIntegralityLaw w) (c : R.NodeCoordinates K w) :
    ∃ hh : (1 : ↥(modularFunctionFieldBar (N * q))) + c.y ∈ R.nodeIntegers w,
      w.HasValue (R.residue₁ ⟨(1 : ↥(modularFunctionFieldBar (N * q))) + c.y, hh.1⟩) 1 ∧
        R.residue₂ ⟨(1 : ↥(modularFunctionFieldBar (N * q))) + c.y, hh.2.1⟩ = 1 ∧
        ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
          A.valuation (V.evalAt ((1 : ↥(modularFunctionFieldBar (N * q))) + c.y)) = 1 := by
  have hy : (c.y : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegers w := c.y.2.1
  have hone : (1 : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegers w := one_mem _
  have hyne : R.residue₁ ⟨c.y, hy.1⟩ ≠ 0 := c.nodeResidue₁_y_ne_zero
  have hyfst : w.ord (R.residue₁ ⟨c.y, hy.1⟩) = 1 := c.y_fst
  have hysnd : R.residue₂ ⟨c.y, hy.2.1⟩ = 0 := c.y_snd
  refine ⟨add_mem hone hy, ?_, ?_, fun V hV => ?_⟩
  · rw [residue₁_add_j1 R hone.1 hy.1, residue₁_one_j1 R]
    have hv := hasValue_add_j1 w w.hasValue_one (hasValue_zero_of_one_le_ord_j1 w hyne hyfst.ge)
    rwa [add_zero] at hv
  · rw [residue₂_add_j1 R hone.2.1 hy.2.1, residue₂_one_j1 R, hysnd, add_zero]
  · rw [evalAt_add_j1 V (rat_j1 V) (one_mem _) (hy.2.2 V hV), V.evalAt_one]
    exact Valuation.map_one_add_of_lt _ (valuation_evalAt_y_lt_one_j1 R w K hvalA c V hV)

private theorem residue₁_second_candidate_j1 [IsAlgClosed k] (c : R.NodeCoordinates K w)
    {G aF : ↥(modularFunctionFieldBar (N * q))} (hG : G ∈ R.nodeIntegers w) (haF : aF ∈ R.nodeIntegers w) {β : k}
    (hβ : β ≠ 0) (ha₁ : R.residue₁ ⟨aF, haF.1⟩ = algebraMap k (modularFunctionFieldC k N) (-β))
    (hone : R.residue₁ ⟨G + aF * 1, (add_mem hG (mul_mem haF (one_mem _))).1⟩ = 0) :
    R.residue₁ ⟨G + aF * ((1 : ↥(modularFunctionFieldBar (N * q))) + c.y),
      (add_mem hG (mul_mem haF (add_mem (one_mem _) c.y.2.1))).1⟩ ≠ 0 := by
  have hy : (c.y : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegers w := c.y.2.1
  have hyne : R.residue₁ ⟨c.y, hy.1⟩ ≠ 0 := c.nodeResidue₁_y_ne_zero
  have hone' : R.residue₁ ⟨G, hG.1⟩ + R.residue₁ ⟨aF, haF.1⟩ = 0 := by
    rw [residue₁_add_j1 R hG.1 (mul_mem haF.1 (one_mem _)), residue₁_mul_j1 R haF.1 (one_mem _), residue₁_one_j1 R,
      mul_one] at hone
    exact hone
  rw [residue₁_add_j1 R hG.1 (mul_mem haF.1 (add_mem (one_mem _) hy.1)),
    residue₁_mul_j1 R haF.1 (add_mem (one_mem _) hy.1), residue₁_add_j1 R (one_mem _) hy.1, residue₁_one_j1 R, mul_add,
    mul_one, ← add_assoc, hone', zero_add, ha₁]
  exact mul_ne_zero ((map_ne_zero (algebraMap k (modularFunctionFieldC k N))).mpr (neg_ne_zero.mpr hβ)) hyne

private theorem branch_cross_j1 [IsAlgClosed k] [DecidableEq k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hqN : ¬ q ∣ N) (hord : R.OrderLawFixed) (hw : w ∈ ssPlaces q N k) (hvalA : R.ValueIntegralityLaw w)
    (c : R.NodeCoordinates K w) (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w))
    (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u)
    {G : ↥(modularFunctionFieldBar (N * q))} (hG : G ∈ R.nodeIntegers w)
    (hGord : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → V.ord G = 0)
    (hG₂ : R.residue₂ ⟨G, hG.2.1⟩ = 0) (hG₁ : R.residue₁ ⟨G, hG.1⟩ ≠ 0) (hG₁w : w.ord (R.residue₁ ⟨G, hG.1⟩) = 0) :
    False := by
  have hG0 : G ≠ 0 := by
    rintro rfl
    exact hG₁ (map_zero R.residue₁)

  obtain ⟨hmem, hunit⟩ := w.exists_isUnit_of_ord_eq_zero hG₁ hG₁w
  obtain ⟨β, hGβ, hβ'⟩ := w.exists_hasValue_of_surjective hw.1 hmem
  have hβ : β ≠ 0 := hβ' hunit

  obtain ⟨a, ha⟩ := P.red_surjective_of_level (-β)
  have hau : IsUnit a := isUnit_of_red_ne_zero_j1 P a (by rw [ha]; exact neg_ne_zero.mpr hβ)
  have haF := R.algebraMap_mem_nodeIntegers w a
  have ha₁ := (residue_algebraMap_j1 R a).1
  have ha₂ := (residue_algebraMap_j1 R a).2
  rw [ha] at ha₁ ha₂
  have haV : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ))
        = (a : AlgebraicClosure ℚ) := fun V => evalAt_algebraMap_j1 V _
  obtain ⟨hone, hone₁, hone₂, honeV⟩ := candidate_one_j1 R w
  by_cases hcase : R.residue₁ ⟨G + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))
      (a : AlgebraicClosure ℚ) * 1, (add_mem hG (mul_mem haF hone)).1⟩ = 0
  · obtain ⟨hh, hh₁, hh₂, hhV⟩ := candidate_one_add_y_j1 R w K hvalA c
    exact branch_cross_aux_j1 R w K hqN hord hw hvalA c ϖ E₀ u hu hxy hG hG0 hGord hG₂ hβ hGβ hau haF ha₁ ha₂ haV hh
      hh₁ hh₂ hhV (residue₁_second_candidate_j1 R w K c hG haF hβ ha₁ hcase)
  · exact branch_cross_aux_j1 R w K hqN hord hw hvalA c ϖ E₀ u hu hxy hG hG0 hGord hG₂ hβ hGβ hau haF ha₁ ha₂ haV hone
      hone₁ hone₂ honeV hcase

private theorem branch_cross_self_j1 [IsAlgClosed k] [DecidableEq k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hqN : ¬ q ∣ N) (hord : R.OrderLawFixed) (hw : w ∈ ssPlaces q N k) (hvalA : R.ValueIntegralityLaw w)
    (c : R.NodeCoordinates K w) (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w))
    (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u)
    {g : ↥(modularFunctionFieldBar (N * q))} (hg₁ : g ∈ gauss₁_j1 R) (hg0 : g ≠ 0) (hgr : R.residue₁ ⟨g, hg₁⟩ ≠ 0)
    (hgw : w.ord (R.residue₁ ⟨g, hg₁⟩) = 0)
    (hgord : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → V.ord g = 0)
    (hg₂ : g ∈ gauss₂_j1 R) (hg₂r : R.residue₂ ⟨g, hg₂⟩ = 0) : False :=
  branch_cross_j1 R w K hqN hord hw hvalA c ϖ E₀ u hu hxy (mem_nodeIntegers_of_ord_j1 R w hg₁ hg₂ hgord hg0) hgord hg₂r
    hgr hgw

private theorem branch_cross_inv_j1 [IsAlgClosed k] [DecidableEq k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hqN : ¬ q ∣ N) (hord : R.OrderLawFixed) (hw : w ∈ ssPlaces q N k) (hvalA : R.ValueIntegralityLaw w)
    (c : R.NodeCoordinates K w) (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w))
    (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u)
    {g : ↥(modularFunctionFieldBar (N * q))} (hg₁ : g ∈ gauss₁_j1 R) (hg0 : g ≠ 0) (hgr : R.residue₁ ⟨g, hg₁⟩ ≠ 0)
    (hgw : w.ord (R.residue₁ ⟨g, hg₁⟩) = 0)
    (hgord : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → V.ord g = 0)
    (hgi₂ : g⁻¹ ∈ gauss₂_j1 R) (hgi₂r : R.residue₂ ⟨g⁻¹, hgi₂⟩ = 0) : False := by
  have hgi₁ : g⁻¹ ∈ gauss₁_j1 R := inv_mem_j1 _ hg₁ (isUnit_gauss₁_j1 R hg₁ hgr)
  have hgiord : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      V.ord g⁻¹ = 0 := fun V hV => by rw [V.ord_inv, hgord V hV, neg_zero]
  have hgi := residue₁_inv_j1 R hg₁ hgr hgi₁
  refine branch_cross_j1 R w K hqN hord hw hvalA c ϖ E₀ u hu hxy (inv_mem_nodeIntegers_j1 R w hgi₁ hgi₂ hgord hg0)
    hgiord hgi₂r ?_ ?_
  · rw [hgi]
    exact inv_ne_zero hgr
  · rw [hgi, w.ord_inv, hgw, neg_zero]

private theorem isUnit_evalAt_of_normalised_j1 [IsAlgClosed k] [DecidableEq k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hqN : ¬ q ∣ N) (hord : R.OrderLawFixed) (hw : w ∈ ssPlaces q N k) (hvalA : R.ValueIntegralityLaw w)
    (c : R.NodeCoordinates K w) (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w))
    (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u)
    {g : ↥(modularFunctionFieldBar (N * q))} (hg₁ : g ∈ gauss₁_j1 R) (hg0 : g ≠ 0) (hgr : R.residue₁ ⟨g, hg₁⟩ ≠ 0)
    (hgw : w.ord (R.residue₁ ⟨g, hg₁⟩) = 0)
    (hgord : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → V.ord g = 0)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    ∃ h : V.evalAt g ∈ A, IsUnit (⟨V.evalAt g, h⟩ : A) := by
  obtain ⟨d', hd'0, hH, hHr⟩ := exists_scaling₂_j1 R hg0
  have hd'F : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d' ≠ 0 :=
    (map_ne_zero (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))).mpr hd'0
  have hHi : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d' * g)⁻¹ ∈ gauss₂_j1 R :=
    inv_mem_j1 _ hH (isUnit_gauss₂_j1 R hH hHr)

  have hg_eq : g = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d'⁻¹
      * (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d' * g) := by
    rw [← mul_assoc, map_inv₀ (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      inv_mul_cancel₀ hd'F, one_mul]
  have hgi_eq : g⁻¹ = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d'
      * (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d' * g)⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, mul_comm _ g⁻¹, mul_assoc, mul_inv_cancel₀ hd'F, mul_one]
  by_cases hd'A : d' ∈ A
  · by_cases hd'i : d'⁻¹ ∈ A
    ·
      have hg₂ : g ∈ gauss₂_j1 R := by
        rw [hg_eq]
        exact mul_mem (algebraMap_mem_gauss_j1 R ⟨d'⁻¹, hd'i⟩).2 hH
      have hgi₂ : g⁻¹ ∈ gauss₂_j1 R := by
        rw [hgi_eq]
        exact mul_mem (algebraMap_mem_gauss_j1 R ⟨d', hd'A⟩).2 hHi
      exact isUnit_evalAt_j1 R w hvalA (mem_nodeIntegers_of_ord_j1 R w hg₁ hg₂ hgord hg0)
        (inv_mem_nodeIntegers_j1 R w (inv_mem_j1 _ hg₁ (isUnit_gauss₁_j1 R hg₁ hgr)) hgi₂ hgord hg0) hg0 V hV
    ·
      exfalso
      have hred : red ⟨d', hd'A⟩ = 0 := red_eq_zero_of_not_isUnit_j1 P _ fun hu' => hd'i (inv_mem_j1 A hd'A hu')
      have hgi₂ : g⁻¹ ∈ gauss₂_j1 R := by
        rw [hgi_eq]
        exact mul_mem (algebraMap_mem_gauss_j1 R ⟨d', hd'A⟩).2 hHi
      exact branch_cross_inv_j1 R w K hqN hord hw hvalA c ϖ E₀ u hu hxy hg₁ hg0 hgr hgw hgord hgi₂
        (residue₂_eq_zero_of_eq_mul_j1 R hred hHi hgi₂ hgi_eq)
  ·
    exfalso
    have hd'i : d'⁻¹ ∈ A := (A.mem_or_inv_mem d').resolve_left hd'A
    have hred : red ⟨d'⁻¹, hd'i⟩ = 0 :=
      red_eq_zero_of_not_isUnit_j1 P _ fun hu' => hd'A (by simpa using inv_mem_j1 A hd'i hu')
    have hg₂ : g ∈ gauss₂_j1 R := by
      rw [hg_eq]
      exact mul_mem (algebraMap_mem_gauss_j1 R ⟨d'⁻¹, hd'i⟩).2 hH
    exact branch_cross_self_j1 R w K hqN hord hw hvalA c ϖ E₀ u hu hxy hg₁ hg0 hgr hgw hgord hg₂
      (residue₂_eq_zero_of_eq_mul_j1 R hred hH hg₂ hg_eq)

private theorem residue₁_normalised_j1 [IsAlgClosed k] (c : R.NodeCoordinates K w)
    {df : ↥(modularFunctionFieldBar (N * q))} (hdf : df ∈ gauss₁_j1 R) (hdr : R.residue₁ ⟨df, hdf⟩ ≠ 0) :
    ∃ hg : df * (c.y : ↥(modularFunctionFieldBar (N * q))) ^ (-w.ord (R.residue₁ ⟨df, hdf⟩)) ∈ gauss₁_j1 R,
      R.residue₁ ⟨_, hg⟩ ≠ 0 ∧ w.ord (R.residue₁ ⟨_, hg⟩) = 0 := by
  have hy : (c.y : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegers w := c.y.2.1
  have hyne : R.residue₁ ⟨c.y, hy.1⟩ ≠ 0 := c.nodeResidue₁_y_ne_zero
  have hyfst : w.ord (R.residue₁ ⟨c.y, hy.1⟩) = 1 := c.y_fst
  have hyunit := isUnit_gauss₁_j1 R hy.1 hyne
  have hypow := zpow_mem_j1 _ hy.1 hyunit (-w.ord (R.residue₁ ⟨df, hdf⟩))
  refine ⟨mul_mem hdf hypow, ?_⟩
  rw [residue₁_mul_j1 R hdf hypow, residue₁_zpow_j1 R hy.1 hyne _ hypow]
  have hyres0 : R.residue₁ ⟨c.y, hy.1⟩ ^ (-w.ord (R.residue₁ ⟨df, hdf⟩)) ≠ 0 := zpow_ne_zero _ hyne
  refine ⟨mul_ne_zero hdr hyres0, ?_⟩
  rw [w.ord_mul hdr hyres0, w.ord_zpow, hyfst]
  ring

private theorem ord_normalised_j1 [IsAlgClosed k] (c : R.NodeCoordinates K w) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u)
    {d : AlgebraicClosure ℚ} (hd0 : d ≠ 0) {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ≠ 0)
    (hf0 : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w → V'.ord f = 0)
    (n : ℤ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    V.ord (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d * f
      * (c.y : ↥(modularFunctionFieldBar (N * q))) ^ n) = 0 := by
  have hdF : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d ≠ 0 :=
    (map_ne_zero (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))).mpr hd0
  rw [V.ord_mul (mul_ne_zero hdF hf) (zpow_ne_zero n (y_ne_zero_j1 R w K c)), V.ord_mul hdF hf,
    ConstantReduction.ord_algebraMap V hd0, hf0 V hV, V.ord_zpow, ord_y_eq_zero_j1 R w K c ϖ E₀ u hu hxy V hV]
  ring

private theorem evalAt_normalised_j1 [IsAlgClosed k] (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u)
    (d : AlgebraicClosure ℚ) {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ≠ 0)
    (hf0 : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w → V'.ord f = 0)
    (m : ℤ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    V.evalAt f * d⁻¹⁻¹ * V.evalAt (↑c.y : ↥(modularFunctionFieldBar (N * q))) ^ (-m)
      = V.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d * f
          * (c.y : ↥(modularFunctionFieldBar (N * q))) ^ (-m)) := by
  have hy : (c.y : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegers w := c.y.2.1
  have hy0 := y_ne_zero_j1 R w K c
  have hyord := ord_y_eq_zero_j1 R w K c ϖ E₀ u hu hxy V hV
  have hfV : f ∈ V.toValuationSubring := V.mem_of_ord_nonneg hf (hf0 V hV).ge
  have hyV : (c.y : ↥(modularFunctionFieldBar (N * q))) ^ (-m) ∈ V.toValuationSubring := by
    obtain ⟨hmem, hunit⟩ := V.exists_isUnit_of_ord_eq_zero hy0 hyord
    exact zpow_mem_j1 V.toValuationSubring hmem hunit (-m)
  rw [evalAt_mul_j1 V (rat_j1 V) (mul_mem (V.algebraMap_mem' d) hfV) hyV,
    evalAt_mul_j1 V (rat_j1 V) (V.algebraMap_mem' d) hfV, evalAt_algebraMap_j1, V.evalAt_zpow (rat_j1 V) hy0 hyord,
    inv_inv]
  ring

private theorem unit_principle_j1 [IsAlgClosed k] [DecidableEq k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hqN : ¬ q ∣ N) (hord : R.OrderLawFixed) (hw : w ∈ ssPlaces q N k) (hvalA : R.ValueIntegralityLaw w)
    (c : R.NodeCoordinates K w) (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w))
    (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u) (f : ↥(modularFunctionFieldBar (N * q)))
    (hf : f ≠ 0)
    (hf0 : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w → V'.ord f = 0) :
    ∃ (m : ℤ) (c₁ : AlgebraicClosure ℚ), c₁ ≠ 0 ∧
      ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w →
        ∃ h : V'.evalAt f * c₁⁻¹ * V'.evalAt (↑c.y : ↥(modularFunctionFieldBar (N * q))) ^ (-m) ∈ A,
          IsUnit (⟨_, h⟩ : A) := by
  obtain ⟨d, hd0, hdf, hdr⟩ := exists_scaling₁_j1 R hf
  obtain ⟨hg₁, hgr, hgw⟩ := residue₁_normalised_j1 R w K c hdf hdr
  refine ⟨w.ord (R.residue₁ ⟨_, hdf⟩), d⁻¹, inv_ne_zero hd0, fun V hV => ?_⟩
  rw [evalAt_normalised_j1 R w K c ϖ E₀ u hu hxy d hf hf0 _ V hV]
  have hdF : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) d ≠ 0 :=
    (map_ne_zero (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))).mpr hd0
  exact isUnit_evalAt_of_normalised_j1 R w K hqN hord hw hvalA c ϖ E₀ u hu hxy hg₁
    (mul_ne_zero (mul_ne_zero hdF hf) (zpow_ne_zero _ (y_ne_zero_j1 R w K c))) hgr hgw
    (ord_normalised_j1 R w K c ϖ E₀ u hu hxy hd0 hf hf0 _) V hV

end Node

end SolE3_j1

open SolE3_j1 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (hord : R.OrderLawFixed)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hvalA : R.ValueIntegralityLaw w)
    (hres : ∀ g : ↥(R.nodeIntegersOver K w),
      ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))
    (hσπ : σ π = algebraMap _ _ (R.nodeConst K w ϖ))
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (hres₁ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨f, f.2.1⟩ ≠ 0 →
          w.ord (R.nodeResidue₁ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hres₂ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨f, f.2.1⟩ ≠ 0 →
          (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (c : R.NodeCoordinates K w) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u) :
    ∀ f : ↥(modularFunctionFieldBar (N * q)), f ≠ 0 →
      (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w → V'.ord f = 0) →
      ∃ (m : ℤ) (c₁ : AlgebraicClosure ℚ), c₁ ≠ 0 ∧
        ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w →
          ∃ h : V'.evalAt f * c₁⁻¹ * V'.evalAt (↑c.y : ↥(modularFunctionFieldBar (N * q))) ^ (-m) ∈ A,
            IsUnit (⟨_, h⟩ : A) := by
  have _ := hmodel
  have _ := hres
  have _ := hϖ
  have _ := hπ
  have _ := hσπ
  have _ := hE
  have _ := hconst
  have _ := hres₁
  have _ := hres₂
  intro f hf hf0
  exact unit_principle_j1 R w K hqN hord hw hvalA c ϖ E₀ u hu hxy f hf hf0

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_zpow_unit_principle_evalAt_y_of_ringEquiv_uvCrossingModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_zpow_unit_principle_evalAt_y_of_ringEquiv_uvCrossingModel (solution)
