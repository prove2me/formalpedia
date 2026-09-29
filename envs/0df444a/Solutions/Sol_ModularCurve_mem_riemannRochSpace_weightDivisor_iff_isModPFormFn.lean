-- Prove2me | solution 1 for ModularCurve.mem_riemannRochSpace_weightDivisor_iff_isModPFormFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/272ab055-2de8-599d-a5fa-26ba46c108a5

import Mathlib
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_stackOrd_nonneg_and_le_ord_of_isModPFormFn
import Theorems.Thm_ModularCurve_isModPFormFn_of_forall_stackOrd_nonneg_of_forall_le_ord
import Theorems.Thm_ModularCurve_isModPFormFn_zero_and_add_and_smul
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_neg
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_riemannRochSpace_weightDivisor_iff_isModPFormFn
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois"
p2m_attr_erase "simp" "ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open AlgebraicCurve ModularCurve

noncomputable section

namespace WDRR

section Places

variable (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]

theorem isRational (x : Place K ↥(modularFunctionFieldC K N)) : x.IsRational := by
  haveI := isCurveOver_modularFunctionFieldC_of_perfectField K N
  exact (Place.isRational_iff_deg_eq_one x).2 (IsCurveOver.deg_eq_one_of_isAlgClosed x)

variable {K N}

theorem ord_sub_algebraMap_eq_zero_of_evalAt_ne {F : Type*} [Field F] [Algebra K F] (x : Place K F)
    {f : F} (hf : f ∈ x.toValuationSubring) {c : K} (hc : x.evalAt f ≠ c) (hne : f - algebraMap K F c ≠ 0) :
    x.ord (f - algebraMap K F c) = 0 := by
  have hmem : f - algebraMap K F c ∈ x.toValuationSubring := sub_mem hf (x.algebraMap_mem' c)
  have h0 : 0 ≤ x.ord (f - algebraMap K F c) := (x.mem_iff_ord_nonneg hne).1 hmem
  by_contra h
  have hpos : 0 < x.ord (f - algebraMap K F c) := lt_of_le_of_ne h0 (Ne.symm h)
  apply hc
  rw [x.evalAt_congr hf (x.algebraMap_mem' c) (Or.inr hpos), x.evalAt_algebraMap]

theorem ord_sub_algebraMap_of_ord_neg {F : Type*} [Field F] [Algebra K F] (x : Place K F) {f : F}
    (hf : x.ord f < 0) (c : K) : x.ord (f - algebraMap K F c) = x.ord f := by
  by_cases hc : c = 0
  · rw [hc, map_zero, sub_zero]
  have hf0 : f ≠ 0 := fun h => by rw [h, x.ord_zero] at hf; exact lt_irrefl _ hf
  rw [sub_eq_add_neg]
  refine x.ord_add_eq_of_lt hf0 (neg_ne_zero.2 ((map_ne_zero _).2 hc)) ?_
  rw [x.ord_neg, x.ord_algebraMap]; exact hf

theorem natCast_placeRamificationJ {x : Place K ↥(modularFunctionFieldC K N)} (haff : IsAffineGeomPlace K N x) :
    (placeRamificationJ N x : ℤ) = x.ord (jGeomGen K N -
      algebraMap K ↥(modularFunctionFieldC K N) (x.evalAt (jGeomGen K N))) := by
  unfold placeRamificationJ
  exact Int.toNat_of_nonneg (ord_sub_evalAt_pos_of_isRational (isRational K N x) haff.1
    (jGeomGen_sub_algebraMap_ne_zero K N _)).le

theorem placeRamificationJ_pos {x : Place K ↥(modularFunctionFieldC K N)} (haff : IsAffineGeomPlace K N x) :
    0 < placeRamificationJ N x := by
  have h := ord_sub_evalAt_pos_of_isRational (isRational K N x) haff.1
    (jGeomGen_sub_algebraMap_ne_zero K N (x.evalAt (jGeomGen K N)))
  have h2 := natCast_placeRamificationJ haff
  omega

theorem ord_jGeomGen_sub {x : Place K ↥(modularFunctionFieldC K N)} (haff : IsAffineGeomPlace K N x) (c : K) :
    x.ord (jGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) c)
      = if x.evalAt (jGeomGen K N) = c then (placeRamificationJ N x : ℤ) else 0 := by
  split_ifs with h
  · rw [natCast_placeRamificationJ haff, h]
  · exact ord_sub_algebraMap_eq_zero_of_evalAt_ne x haff.1 h (jGeomGen_sub_algebraMap_ne_zero K N c)

variable (K) in
omit [IsAlgClosed K] [DecidableEq K] in
theorem ofNat1728_ne_zero (p : ℕ) [hp : Fact p.Prime] [CharP K p] (hp5 : 5 ≤ p) : (1728 : K) ≠ 0 := by
  intro h
  have hqp : p.Prime := hp.out
  have h' : ((1728 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  have h1728 : (1728 : ℕ) = 2 ^ 6 * 3 ^ 3 := by norm_num
  rw [h1728] at h'
  rcases (Nat.Prime.dvd_mul hqp).mp h' with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (hqp.dvd_of_dvd_pow h2); omega
  · have := Nat.le_of_dvd (by norm_num) (hqp.dvd_of_dvd_pow h3); omega

end Places

section Affine

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

theorem isAffineGeomPlace_of_mem (x : Place K ↥(modularFunctionFieldC K N))
    (hj : jGeomGen K N ∈ x.toValuationSubring) : IsAffineGeomPlace K N x :=
  ⟨hj, x.mem_toValuationSubring_of_isIntegral_adjoin hj (isIntegral_jNGeomGen K N)⟩

end Affine

section Exist

variable (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N] (m : ℕ)

omit [IsAlgClosed K] [DecidableEq K] in
theorem jlit : (⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N)) = jGeomGen K N := rfl

omit [IsAlgClosed K] [DecidableEq K] in
theorem jGeomGen_ne_zero : (jGeomGen K N : ↥(modularFunctionFieldC K N)) ≠ 0 := by
  simpa using jGeomGen_sub_algebraMap_ne_zero K N 0

omit [IsAlgClosed K] [DecidableEq K] in

theorem weightFloor_eq_zero_of (w : Place K ↥(modularFunctionFieldC K N))
    (h0 : w.ord (jGeomGen K N) = 0) (h1 : w.ord (jGeomGen K N - algebraMap K _ 1728) = 0) :
    weightFloor K N m w = 0 := by
  unfold weightFloor
  rw [jlit, h0, h1]
  simp

private theorem _root_.WDRR.exists_divisor : ∃ D : Divisor K ↥(modularFunctionFieldC K N), ∀ w, D w = weightFloor K N m w := by
  classical
  have hPD := (isCurveOver_modularFunctionFieldC_of_perfectField K N).toHasPrincipalDivisors
  obtain ⟨Dj, hDj, -⟩ := hPD.exists_divisor (jGeomGen K N) (jGeomGen_ne_zero K N)
  obtain ⟨D1, hD1, -⟩ := hPD.exists_divisor (jGeomGen K N - algebraMap K _ 1728)
    (jGeomGen_sub_algebraMap_ne_zero K N 1728)
  refine ⟨Finsupp.onFinset (Dj.support ∪ D1.support) (weightFloor K N m) ?_, fun w => by
    rw [Finsupp.onFinset_apply]⟩
  intro w hw
  by_contra hnot
  rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff, hDj, hD1] at hnot
  exact hw (weightFloor_eq_zero_of K N m w hnot.1 hnot.2)

p2m_export "WDRR" "exists_divisor"
end Exist

section Bridge

variable (p : ℕ) [hp : Fact p.Prime] (N : ℕ) [NeZero N]
  (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (m : ℕ)

theorem weightFloor_of_ord_neg (w : Place K ↥(modularFunctionFieldC K N)) (hw : w.ord (jGeomGen K N) < 0) :
    weightFloor K N m w = (m : ℤ) * w.ord (jGeomGen K N) := by
  unfold weightFloor
  rw [jlit, ord_sub_algebraMap_of_ord_neg w hw 1728, if_neg (by omega), if_neg (by omega), if_pos hw]
  ring

theorem bridge_affine (hp5 : 5 ≤ p) (hpN : ¬ p ∣ N) (G : ↥(modularFunctionFieldC K N))
    (w : Place K ↥(modularFunctionFieldC K N)) (haff : IsAffineGeomPlace K N w) :
    -weightFloor K N m w ≤ w.ord G ↔ 0 ≤ stackOrd N (m : ℤ) G w := by
  set a₀ := w.evalAt (jGeomGen K N) with ha₀
  set e := placeRamificationJ N w with he
  have hepos : 0 < e := placeRamificationJ_pos haff
  have hdvd : e ∣ jWidth a₀ := placeRamificationJ_dvd_jWidth_of_ord_pos hp5 hpN hepos
  have hWn : placeWidth N w * e = jWidth a₀ := by
    unfold placeWidth; rw [← ha₀, ← he]; exact Nat.div_mul_cancel hdvd
  have h0 : w.ord (jGeomGen K N) = if a₀ = 0 then (e : ℤ) else 0 := by
    rw [← ord_jGeomGen_sub haff 0, map_zero, sub_zero]
  have h1 : w.ord (jGeomGen K N - algebraMap K _ 1728) = if a₀ = 1728 then (e : ℤ) else 0 :=
    ord_jGeomGen_sub haff 1728
  have h1728 : (1728 : K) ≠ 0 := ofNat1728_ne_zero K p hp5
  unfold weightFloor stackOrd
  rw [jlit, ← ha₀]
  by_cases hz : a₀ = 0
  · have hW3 : jWidth a₀ = 3 := jWidth_of_eq_zero hz
    have hne : a₀ ≠ 1728 := by rw [hz]; exact h1728.symm
    rw [if_pos hz] at h0; rw [if_neg hne] at h1
    rw [hW3] at hWn ⊢
    rw [h0, h1]
    have hepos' : (0 : ℤ) < e := by exact_mod_cast hepos
    rw [if_pos hepos', if_neg (lt_irrefl 0), if_neg (by omega)]

    have h3 : Nat.Prime 3 := by norm_num
    rcases (Nat.dvd_prime h3).1 ⟨placeWidth N w, by rw [mul_comm]; exact hWn.symm⟩ with he1 | he3
    · have hu : placeWidth N w = 3 := by rw [he1] at hWn; omega
      rw [hu, he1]; push_cast; omega
    · have hu : placeWidth N w = 1 := by rw [he3] at hWn; omega
      rw [hu, he3]; push_cast; omega
  by_cases hs : a₀ = 1728
  · have hW2 : jWidth a₀ = 2 := jWidth_of_eq_1728 hs hz
    rw [if_neg hz] at h0; rw [if_pos hs] at h1
    rw [hW2] at hWn ⊢
    rw [h0, h1]
    have hepos' : (0 : ℤ) < e := by exact_mod_cast hepos
    rw [if_neg (lt_irrefl 0), if_pos hepos', if_neg (lt_irrefl 0)]
    have h2 : Nat.Prime 2 := by norm_num
    rcases (Nat.dvd_prime h2).1 ⟨placeWidth N w, by rw [mul_comm]; exact hWn.symm⟩ with he1 | he2
    · have hu : placeWidth N w = 2 := by rw [he1] at hWn; omega
      rw [hu, he1]; push_cast; omega
    · have hu : placeWidth N w = 1 := by rw [he2] at hWn; omega
      rw [hu, he2]; push_cast; omega
  · have hW1 : jWidth a₀ = 1 := jWidth_of_ne hz hs
    rw [if_neg hz] at h0; rw [if_neg hs] at h1
    rw [hW1] at hWn ⊢
    rw [h0, h1]
    have hu : placeWidth N w = 1 := Nat.eq_one_of_mul_eq_one_right hWn
    rw [if_neg (lt_irrefl 0), if_neg (lt_irrefl 0), if_neg (lt_irrefl 0), hu]
    push_cast; omega

end Bridge

theorem main (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] (m : ℕ) (G : ↥(modularFunctionFieldC K N)) :
    G ∈ riemannRochSpace (weightDivisor K N m) ↔ IsModPFormFn K m (G : LaurentSeries K) := by
  classical
  have hex := exists_divisor K N m
  rw [mem_riemannRochSpace_iff]
  simp_rw [weightDivisor_apply K N m hex]

  by_cases hG0 : G = 0
  · subst hG0
    simp only [true_or, ZeroMemClass.coe_zero]
    exact ⟨fun _ => (isModPFormFn_zero_and_add_and_smul K m).1, fun _ _ => trivial⟩

  have hj0 := jGeomGen_ne_zero K N
  constructor
  · intro h
    have h' : ∀ w : Place K ↥(modularFunctionFieldC K N), -weightFloor K N m w ≤ w.ord G :=
      fun w => (h w).resolve_left hG0
    refine isModPFormFn_of_forall_stackOrd_nonneg_of_forall_le_ord p hp5 N hpN K m G hG0 ?_ ?_
    · intro x hx
      exact (bridge_affine p N K m hp5 hpN G x hx).1 (h' x)
    · intro x hx
      have := h' x
      rw [weightFloor_of_ord_neg N K m x hx] at this
      linarith
  · intro hG w
    right
    obtain ⟨haff, hcusp⟩ := stackOrd_nonneg_and_le_ord_of_isModPFormFn p hp5 N hpN K m G hG0 hG
    rcases lt_or_ge (w.ord (jGeomGen K N)) 0 with hneg | hnn
    · rw [weightFloor_of_ord_neg N K m w hneg]
      have := hcusp w hneg
      linarith
    · have hmem : jGeomGen K N ∈ w.toValuationSubring := (w.mem_iff_ord_nonneg hj0).2 hnn
      have hx := isAffineGeomPlace_of_mem K N w hmem
      exact (bridge_affine p N K m hp5 hpN G w hx).2 (haff w hx)

end WDRR

end

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type*) [Field K] [CharP K p] [IsAlgClosed K]
    (m : ℕ) (G : ↥(modularFunctionFieldC K N)) :
    G ∈ riemannRochSpace (weightDivisor K N m) ↔ IsModPFormFn K m (G : LaurentSeries K) :=
  WDRR.main p hp5 N hpN K m G

end S_ModularCurve_mem_riemannRochSpace_weightDivisor_iff_isModPFormFn
end P2MW
export P2MW.S_ModularCurve_mem_riemannRochSpace_weightDivisor_iff_isModPFormFn (solution)
