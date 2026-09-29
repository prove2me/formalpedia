-- Prove2me | solution 1 for ModularCurve.isModPFormFn_of_forall_stackOrd_nonneg_of_forall_le_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/06743804-86a8-5ca4-b5b4-18e2c0158a03

import Mathlib
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_mem_toValuationSubring
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
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

namespace P2MW.S_ModularCurve_isModPFormFn_of_forall_stackOrd_nonneg_of_forall_le_ord
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open AlgebraicCurve ModularCurve

noncomputable section

namespace DictConv

section Transport

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem isIntegral_coe_of_adjoin (S : IntermediateField K L) (y z : ↥S)
    (h : IsIntegral (Algebra.adjoin K ({y} : Set ↥S)) z) :
    IsIntegral (Algebra.adjoin K ({(y : L)} : Set L)) (z : L) := by
  set A := Algebra.adjoin K ({y} : Set ↥S) with hA
  set B := Algebra.adjoin K ({(y : L)} : Set L) with hB
  have hmap : A.map S.val = B := by
    rw [hA, AlgHom.map_adjoin, Set.image_singleton]; rfl
  have hmem : ∀ a : ↥A, ((a : ↥S) : L) ∈ B := fun a => by
    rw [← hmap]; exact ⟨a, a.2, rfl⟩
  let φ : ↥A →+* ↥B :=
    { toFun := fun a => ⟨((a : ↥S) : L), hmem a⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hcomp : (algebraMap ↥B L).comp φ = (algebraMap ↥S L).comp (algebraMap ↥A ↥S) :=
    RingHom.ext fun _ => rfl
  obtain ⟨Q, hQm, hQz⟩ := h
  refine ⟨Q.map φ, hQm.map φ, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  show Polynomial.eval₂ _ (algebraMap ↥S L z) Q = 0
  rw [← Polynomial.hom_eval₂, hQz, map_zero]

end Transport

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

section Main

variable (p : ℕ) [hp : Fact p.Prime] (N : ℕ) [NeZero N]
  (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (m : ℕ)

omit hp [CharP K p] [IsAlgClosed K] [DecidableEq K] in
theorem jGeomGen_ne_zero : (jGeomGen K N : ↥(modularFunctionFieldC K N)) ≠ 0 := by
  simpa using jGeomGen_sub_algebraMap_ne_zero K N 0

omit hp [CharP K p] [IsAlgClosed K] [DecidableEq K] in
theorem jGeomGen_sub_ne_zero :
    (jGeomGen K N : ↥(modularFunctionFieldC K N)) - algebraMap K _ 1728 ≠ 0 :=
  jGeomGen_sub_algebraMap_ne_zero K N 1728

theorem affine_ineq (hp5 : 5 ≤ p) (hpN : ¬ p ∣ N) (G : ↥(modularFunctionFieldC K N))
    (x : Place K ↥(modularFunctionFieldC K N)) (haffx : IsAffineGeomPlace K N x)
    (hst : 0 ≤ stackOrd N (m : ℤ) G x) :
    0 ≤ 6 * x.ord G + 4 * m * x.ord (jGeomGen K N) + 3 * m * x.ord (jGeomGen K N - algebraMap K _ 1728) := by
  set a₀ := x.evalAt (jGeomGen K N) with ha₀
  set e := placeRamificationJ N x with he
  have hepos : 0 < e := placeRamificationJ_pos haffx
  have hdvd : e ∣ jWidth a₀ := placeRamificationJ_dvd_jWidth_of_ord_pos hp5 hpN hepos
  have hWn : placeWidth N x * e = jWidth a₀ := by
    unfold placeWidth; rw [← ha₀, ← he]; exact Nat.div_mul_cancel hdvd
  have h0 : x.ord (jGeomGen K N) = if a₀ = 0 then (e : ℤ) else 0 := by
    rw [← ord_jGeomGen_sub haffx 0, map_zero, sub_zero]
  have h1 : x.ord (jGeomGen K N - algebraMap K _ 1728) = if a₀ = 1728 then (e : ℤ) else 0 :=
    ord_jGeomGen_sub haffx 1728
  have h1728 : (1728 : K) ≠ 0 := ofNat1728_ne_zero K p hp5
  have hepos' : (0 : ℤ) < e := by exact_mod_cast hepos
  unfold stackOrd at hst
  rw [← ha₀] at hst
  by_cases hz : a₀ = 0
  · have hW3 : jWidth a₀ = 3 := jWidth_of_eq_zero hz
    have hne : a₀ ≠ 1728 := by rw [hz]; exact h1728.symm
    rw [if_pos hz] at h0; rw [if_neg hne] at h1
    rw [hW3] at hWn hst
    rw [h0, h1]
    have hW' : (placeWidth N x : ℤ) * (e : ℤ) = 3 := by exact_mod_cast hWn
    push_cast at hst
    have key : (e : ℤ) * ((placeWidth N x : ℤ) * x.ord G + (m : ℤ) * (3 - 1)) = 3 * x.ord G + 2 * m * e := by
      linear_combination (x.ord G) * hW'
    have key2 : 0 ≤ (e : ℤ) * ((placeWidth N x : ℤ) * x.ord G + (m : ℤ) * (3 - 1)) := mul_nonneg hepos'.le hst
    rw [key] at key2
    linarith
  by_cases hs : a₀ = 1728
  · have hW2 : jWidth a₀ = 2 := jWidth_of_eq_1728 hs hz
    rw [if_neg hz] at h0; rw [if_pos hs] at h1
    rw [hW2] at hWn hst
    rw [h0, h1]
    have hW' : (placeWidth N x : ℤ) * (e : ℤ) = 2 := by exact_mod_cast hWn
    push_cast at hst
    have key : (e : ℤ) * ((placeWidth N x : ℤ) * x.ord G + (m : ℤ) * (2 - 1)) = 2 * x.ord G + m * e := by
      linear_combination (x.ord G) * hW'
    have key2 : 0 ≤ (e : ℤ) * ((placeWidth N x : ℤ) * x.ord G + (m : ℤ) * (2 - 1)) := mul_nonneg hepos'.le hst
    rw [key] at key2
    linarith
  · have hW1 : jWidth a₀ = 1 := jWidth_of_ne hz hs
    rw [if_neg hz] at h0; rw [if_neg hs] at h1
    rw [hW1] at hWn hst
    rw [h0, h1]
    have hpw : placeWidth N x = 1 := Nat.eq_one_of_mul_eq_one_right hWn
    rw [hpw] at hst
    push_cast at hst
    linarith

theorem X_mem (hp5 : 5 ≤ p) (hpN : ¬ p ∣ N) (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0)
    (haff : ∀ x : Place K (modularFunctionFieldC K N), IsAffineGeomPlace K N x → 0 ≤ stackOrd N (m : ℤ) G x)
    (x : Place K ↥(modularFunctionFieldC K N)) (hj : jGeomGen K N ∈ x.toValuationSubring) :
    G ^ 6 * jGeomGen K N ^ (4 * m) * (jGeomGen K N - algebraMap K _ 1728) ^ (3 * m) ∈ x.toValuationSubring := by
  have hj0 := jGeomGen_ne_zero N K
  have hj1 := jGeomGen_sub_ne_zero N K
  have haffx := isAffineGeomPlace_of_mem K N x hj
  have hineq := affine_ineq p N K m hp5 hpN G x haffx (haff x haffx)
  have hX0 : G ^ 6 * jGeomGen K N ^ (4 * m) * (jGeomGen K N - algebraMap K _ 1728) ^ (3 * m) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0)) (pow_ne_zero _ hj1)
  rw [x.mem_iff_ord_nonneg hX0, x.ord_mul (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0)) (pow_ne_zero _ hj1),
    x.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hj0), ← zpow_natCast, x.ord_zpow, ← zpow_natCast,
    x.ord_zpow, ← zpow_natCast, x.ord_zpow]
  push_cast
  linarith

theorem Y_mem (hp5 : 5 ≤ p) (hpN : ¬ p ∣ N) (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0)
    (haff : ∀ x : Place K (modularFunctionFieldC K N), IsAffineGeomPlace K N x → 0 ≤ stackOrd N (m : ℤ) G x)
    (hcusp : ∀ x : Place K (modularFunctionFieldC K N), x.ord (jGeomGen K N) < 0 →
        (m : ℤ) * (-(x.ord (jGeomGen K N))) ≤ x.ord G)
    (x : Place K ↥(modularFunctionFieldC K N)) (hji : (jGeomGen K N)⁻¹ ∈ x.toValuationSubring) :
    G ^ 2 * jGeomGen K N ^ m * (jGeomGen K N - algebraMap K _ 1728) ^ m ∈ x.toValuationSubring := by
  have hj0 := jGeomGen_ne_zero N K
  have hj1 := jGeomGen_sub_ne_zero N K
  have hY0 : G ^ 2 * jGeomGen K N ^ m * (jGeomGen K N - algebraMap K _ 1728) ^ m ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0)) (pow_ne_zero _ hj1)
  rw [x.mem_iff_ord_nonneg hY0, x.ord_mul (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0)) (pow_ne_zero _ hj1),
    x.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hj0), ← zpow_natCast, x.ord_zpow, ← zpow_natCast,
    x.ord_zpow, ← zpow_natCast, x.ord_zpow]
  push_cast

  have hjle : x.ord (jGeomGen K N) ≤ 0 := by
    have h := (x.mem_iff_ord_nonneg (inv_ne_zero hj0)).1 hji
    rw [x.ord_inv] at h; omega
  rcases hjle.lt_or_eq with hlt | heq
  ·
    have hc := hcusp x hlt
    rw [ord_sub_algebraMap_of_ord_neg x hlt 1728]
    nlinarith [hc, hlt]
  ·
    have hjmem : jGeomGen K N ∈ x.toValuationSubring := (x.mem_iff_ord_nonneg hj0).2 heq.ge
    have haffx := isAffineGeomPlace_of_mem K N x hjmem
    have hineq := affine_ineq p N K m hp5 hpN G x haffx (haff x haffx)
    have hst := haff x haffx

    set a₀ := x.evalAt (jGeomGen K N) with ha₀
    set e := placeRamificationJ N x with he
    have hepos : 0 < e := placeRamificationJ_pos haffx
    have h0 : x.ord (jGeomGen K N) = if a₀ = 0 then (e : ℤ) else 0 := by
      rw [← ord_jGeomGen_sub haffx 0, map_zero, sub_zero]
    have hz : a₀ ≠ 0 := by
      intro hz; rw [if_pos hz] at h0; omega
    have h1 : x.ord (jGeomGen K N - algebraMap K _ 1728) = if a₀ = 1728 then (e : ℤ) else 0 :=
      ord_jGeomGen_sub haffx 1728
    rw [heq]
    by_cases hs : a₀ = 1728
    · rw [if_pos hs] at h1
      rw [h1]
      rw [heq, h1] at hineq

      have hdvd : e ∣ jWidth a₀ := placeRamificationJ_dvd_jWidth_of_ord_pos hp5 hpN hepos
      have hWn : placeWidth N x * e = jWidth a₀ := by
        unfold placeWidth; rw [← ha₀, ← he]; exact Nat.div_mul_cancel hdvd
      rw [jWidth_of_eq_1728 hs hz] at hWn
      unfold stackOrd at hst
      rw [← ha₀, jWidth_of_eq_1728 hs hz] at hst
      have hW' : (placeWidth N x : ℤ) * (e : ℤ) = 2 := by exact_mod_cast hWn
      have hepos' : (0 : ℤ) < e := by exact_mod_cast hepos
      push_cast at hst
      have key : (e : ℤ) * ((placeWidth N x : ℤ) * x.ord G + (m : ℤ) * (2 - 1)) = 2 * x.ord G + m * e := by
        linear_combination (x.ord G) * hW'
      have key2 : 0 ≤ (e : ℤ) * ((placeWidth N x : ℤ) * x.ord G + (m : ℤ) * (2 - 1)) := mul_nonneg hepos'.le hst
      rw [key] at key2
      linarith
    · rw [if_neg hs] at h1
      rw [h1]
      rw [heq, h1] at hineq
      linarith

theorem main (hp5 : 5 ≤ p) (hpN : ¬ p ∣ N) (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0)
    (haff : ∀ x : Place K (modularFunctionFieldC K N), IsAffineGeomPlace K N x → 0 ≤ stackOrd N (m : ℤ) G x)
    (hcusp : ∀ x : Place K (modularFunctionFieldC K N), x.ord (jGeomGen K N) < 0 →
        (m : ℤ) * (-(x.ord (jGeomGen K N))) ≤ x.ord G) :
    IsModPFormFn K m (G : LaurentSeries K) := by

  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have hN : (N : K) ≠ 0 := fun h => hpN ((CharP.cast_eq_zero_iff K p N).1 h)
  have hfs := finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC K N data
    (isSeparable_jqNModC_of_natCast_ne_zero K N hN)
  haveI := hfs.1
  haveI := hfs.2
  have hXint := AlgebraicCurve.isIntegral_adjoin_of_forall_mem_toValuationSubring
    (⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N) (jGeomGen K N)
    (G ^ 6 * jGeomGen K N ^ (4 * m) * (jGeomGen K N - algebraMap K _ 1728) ^ (3 * m))
    (fun x hj => X_mem p N K m hp5 hpN G hG0 haff x hj)
  have hYint := AlgebraicCurve.isIntegral_adjoin_of_forall_mem_toValuationSubring
    (⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N) (jGeomGen K N)⁻¹
    (G ^ 2 * jGeomGen K N ^ m * (jGeomGen K N - algebraMap K _ 1728) ^ m)
    (fun x hj => Y_mem p N K m hp5 hpN G hG0 haff hcusp x hj)
  have hX := isIntegral_coe_of_adjoin _ _ _ hXint
  have hY := isIntegral_coe_of_adjoin _ _ _ hYint
  rw [coe_jGeomGen, IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_pow,
    IntermediateField.coe_pow, IntermediateField.coe_pow, AddSubgroupClass.coe_sub, coe_jGeomGen] at hX
  rw [IntermediateField.coe_inv, coe_jGeomGen, IntermediateField.coe_mul, IntermediateField.coe_mul,
    IntermediateField.coe_pow, IntermediateField.coe_pow, IntermediateField.coe_pow, AddSubgroupClass.coe_sub,
    coe_jGeomGen] at hY
  exact ⟨hX, hY⟩

end Main

end DictConv

end

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (m : ℕ) (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0)
    (haff : ∀ x : Place K (modularFunctionFieldC K N), IsAffineGeomPlace K N x →
        0 ≤ stackOrd N (m : ℤ) G x)
    (hcusp : ∀ x : Place K (modularFunctionFieldC K N), x.ord (jGeomGen K N) < 0 →
        (m : ℤ) * (-(x.ord (jGeomGen K N))) ≤ x.ord G) :
    IsModPFormFn K m (G : LaurentSeries K) :=
  DictConv.main p N K m hp5 hpN G hG0 haff hcusp

end S_ModularCurve_isModPFormFn_of_forall_stackOrd_nonneg_of_forall_le_ord
end P2MW
export P2MW.S_ModularCurve_isModPFormFn_of_forall_stackOrd_nonneg_of_forall_le_ord (solution)
