-- Prove2me | solution 1 for ModularCurve.eq_zero_of_forall_stackOrd_nonneg_of_forall_le_ord_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/73a85eaa-2865-5ae5-940b-7bfcff6b632c

import Mathlib
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
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

namespace P2MW.S_ModularCurve_eq_zero_of_forall_stackOrd_nonneg_of_forall_le_ord_of_neg
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois"
p2m_attr_erase "simp" "ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open AlgebraicCurve ModularCurve

noncomputable section

namespace NegWt

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
  (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]

omit hp [CharP K p] [IsAlgClosed K] [DecidableEq K] in
theorem jGeomGen_ne_zero : (jGeomGen K N : ↥(modularFunctionFieldC K N)) ≠ 0 := by
  simpa using jGeomGen_sub_algebraMap_ne_zero K N 0

def zer (f : ↥(modularFunctionFieldC K N)) (v : Place K ↥(modularFunctionFieldC K N)) : ℤ := max (v.ord f) 0

def pol (f : ↥(modularFunctionFieldC K N)) (v : Place K ↥(modularFunctionFieldC K N)) : ℤ := max (-(v.ord f)) 0

omit hp [CharP K p] [IsAlgClosed K] [DecidableEq K] in
theorem zer_sub_pol (f : ↥(modularFunctionFieldC K N)) (v : Place K ↥(modularFunctionFieldC K N)) :
    zer N K f v - pol N K f v = v.ord f := by
  unfold zer pol
  rcases le_total 0 (v.ord f) with h | h
  · rw [max_eq_left h, max_eq_right (by omega)]; ring
  · rw [max_eq_right h, max_eq_left (by omega)]; ring

theorem pol_sub_algebraMap (c : K) (v : Place K ↥(modularFunctionFieldC K N)) :
    pol N K (jGeomGen K N - algebraMap K _ c) v = pol N K (jGeomGen K N) v := by
  unfold pol
  rcases lt_or_ge (v.ord (jGeomGen K N)) 0 with h | h
  · rw [ord_sub_algebraMap_of_ord_neg v h c]
  · have hmem : jGeomGen K N ∈ v.toValuationSubring := (v.mem_iff_ord_nonneg (jGeomGen_ne_zero N K)).2 h
    have hmem' : jGeomGen K N - algebraMap K _ c ∈ v.toValuationSubring := sub_mem hmem (v.algebraMap_mem' c)
    have h' : 0 ≤ v.ord (jGeomGen K N - algebraMap K _ c) :=
      (v.mem_iff_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero K N c)).1 hmem'
    rw [max_eq_right (by omega), max_eq_right (by omega)]

theorem pointwise (hp5 : 5 ≤ p) (hpN : ¬ p ∣ N) (m : ℤ) (hm : m < 0) (G : ↥(modularFunctionFieldC K N))
    (haff : ∀ x : Place K (modularFunctionFieldC K N), IsAffineGeomPlace K N x → 0 ≤ stackOrd N m G x)
    (hcusp : ∀ x : Place K (modularFunctionFieldC K N), x.ord (jGeomGen K N) < 0 →
        m * (-(x.ord (jGeomGen K N))) ≤ x.ord G)
    (v : Place K ↥(modularFunctionFieldC K N)) :
    -4 * m * zer N K (jGeomGen K N) v - 3 * m * zer N K (jGeomGen K N - algebraMap K _ 1728) v
      + 6 * m * pol N K (jGeomGen K N) v ≤ 6 * v.ord G := by
  have hj0 := jGeomGen_ne_zero N K
  have hj1 : (jGeomGen K N : ↥(modularFunctionFieldC K N)) - algebraMap K _ 1728 ≠ 0 :=
    jGeomGen_sub_algebraMap_ne_zero K N 1728
  unfold zer pol
  rcases lt_or_ge (v.ord (jGeomGen K N)) 0 with hneg | hnn
  ·
    have hc := hcusp v hneg
    rw [ord_sub_algebraMap_of_ord_neg v hneg 1728, max_eq_right hneg.le, max_eq_left (by omega)]
    nlinarith [hc, hneg, hm]
  ·
    have hmem : jGeomGen K N ∈ v.toValuationSubring := (v.mem_iff_ord_nonneg hj0).2 hnn
    have haffx := isAffineGeomPlace_of_mem K N v hmem
    have hst := haff v haffx
    rw [max_eq_right (show -(v.ord (jGeomGen K N)) ≤ 0 by omega)]
    set a₀ := v.evalAt (jGeomGen K N) with ha₀
    set e := placeRamificationJ N v with he
    have hepos : 0 < e := placeRamificationJ_pos haffx
    have hdvd : e ∣ jWidth a₀ := placeRamificationJ_dvd_jWidth_of_ord_pos hp5 hpN hepos
    have hWn : placeWidth N v * e = jWidth a₀ := by
      unfold placeWidth; rw [← ha₀, ← he]; exact Nat.div_mul_cancel hdvd
    have h0 : v.ord (jGeomGen K N) = if a₀ = 0 then (e : ℤ) else 0 := by
      rw [← ord_jGeomGen_sub haffx 0, map_zero, sub_zero]
    have h1 : v.ord (jGeomGen K N - algebraMap K _ 1728) = if a₀ = 1728 then (e : ℤ) else 0 :=
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
      rw [h0, h1, max_eq_left hepos'.le, max_self]
      have hW' : (placeWidth N v : ℤ) * (e : ℤ) = 3 := by exact_mod_cast hWn
      push_cast at hst
      have key : (e : ℤ) * ((placeWidth N v : ℤ) * v.ord G + m * (3 - 1)) = 3 * v.ord G + 2 * m * e := by
        linear_combination (v.ord G) * hW'
      have key2 : 0 ≤ (e : ℤ) * ((placeWidth N v : ℤ) * v.ord G + m * (3 - 1)) := mul_nonneg hepos'.le hst
      rw [key] at key2
      linarith
    by_cases hs : a₀ = 1728
    · have hW2 : jWidth a₀ = 2 := jWidth_of_eq_1728 hs hz
      rw [if_neg hz] at h0; rw [if_pos hs] at h1
      rw [hW2] at hWn hst
      rw [h0, h1, max_self, max_eq_left hepos'.le]
      have hW' : (placeWidth N v : ℤ) * (e : ℤ) = 2 := by exact_mod_cast hWn
      push_cast at hst
      have key : (e : ℤ) * ((placeWidth N v : ℤ) * v.ord G + m * (2 - 1)) = 2 * v.ord G + m * e := by
        linear_combination (v.ord G) * hW'
      have key2 : 0 ≤ (e : ℤ) * ((placeWidth N v : ℤ) * v.ord G + m * (2 - 1)) := mul_nonneg hepos'.le hst
      rw [key] at key2
      linarith
    · have hW1 : jWidth a₀ = 1 := jWidth_of_ne hz hs
      rw [if_neg hz] at h0; rw [if_neg hs] at h1
      rw [hW1] at hWn hst
      rw [h0, h1, max_self]
      have hpw : placeWidth N v = 1 := Nat.eq_one_of_mul_eq_one_right hWn
      rw [hpw] at hst
      push_cast at hst
      linarith

theorem deg_eq_one (v : Place K ↥(modularFunctionFieldC K N)) : v.deg = 1 :=
  (Place.isRational_iff_deg_eq_one v).1 (isRational K N v)

theorem sum_ord_eq_zero {f : ↥(modularFunctionFieldC K N)} (hf : f ≠ 0)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (hT : ∀ v, v.ord f ≠ 0 → v ∈ T) :
    ∑ v ∈ T, v.ord f = 0 := by
  have hPD := (isCurveOver_modularFunctionFieldC_of_perfectField K N).toHasPrincipalDivisors
  obtain ⟨D, hD, hdeg⟩ := hPD.exists_divisor f hf
  have hdeg' : Divisor.degree D = ∑ v ∈ D.support, D v := by
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [AddMonoidHom.mulRight_apply, deg_eq_one N K v, Nat.cast_one, mul_one]
  rw [hdeg'] at hdeg
  have hsub : D.support ⊆ T := fun v hv => hT v (by rw [← hD]; exact Finsupp.mem_support_iff.1 hv)
  rw [← Finset.sum_subset hsub (fun v _ hv => by rw [← hD]; exact Finsupp.notMem_support_iff.1 hv)]
  simp_rw [← hD]
  exact hdeg

theorem main (hp5 : 5 ≤ p) (hpN : ¬ p ∣ N) (m : ℤ) (hm : m < 0) (G : ↥(modularFunctionFieldC K N))
    (haff : ∀ x : Place K (modularFunctionFieldC K N), IsAffineGeomPlace K N x → 0 ≤ stackOrd N m G x)
    (hcusp : ∀ x : Place K (modularFunctionFieldC K N), x.ord (jGeomGen K N) < 0 →
        m * (-(x.ord (jGeomGen K N))) ≤ x.ord G) :
    G = 0 := by
  classical
  by_contra hG0
  have hj0 := jGeomGen_ne_zero N K

  haveI : Fact (Nat.Prime p) := hp
  obtain ⟨v₀, hv₀⟩ := ssPlaces_nonempty p N hpN K
  set a₀ := v₀.evalAt (jGeomGen K N) with ha₀
  have hja : (jGeomGen K N : ↥(modularFunctionFieldC K N)) - algebraMap K _ a₀ ≠ 0 :=
    jGeomGen_sub_algebraMap_ne_zero K N a₀
  have hj1 : (jGeomGen K N : ↥(modularFunctionFieldC K N)) - algebraMap K _ 1728 ≠ 0 :=
    jGeomGen_sub_algebraMap_ne_zero K N 1728

  have hPD := (isCurveOver_modularFunctionFieldC_of_perfectField K N).toHasPrincipalDivisors
  obtain ⟨DG, hDG, -⟩ := hPD.exists_divisor G hG0
  obtain ⟨Dj, hDj, -⟩ := hPD.exists_divisor (jGeomGen K N) hj0
  obtain ⟨D1, hD1, -⟩ := hPD.exists_divisor (jGeomGen K N - algebraMap K _ 1728) hj1
  obtain ⟨Da, hDa, -⟩ := hPD.exists_divisor (jGeomGen K N - algebraMap K _ a₀) hja
  set T := DG.support ∪ Dj.support ∪ D1.support ∪ Da.support with hT
  have memT : ∀ {D : Divisor K ↥(modularFunctionFieldC K N)} {f : ↥(modularFunctionFieldC K N)},
      (∀ v, D v = v.ord f) → D.support ⊆ T → ∀ v, v.ord f ≠ 0 → v ∈ T := by
    intro D f hD hsub v hv
    exact hsub (Finsupp.mem_support_iff.2 (by rw [hD]; exact hv))
  have hTG : ∀ v, v.ord G ≠ 0 → v ∈ T := memT hDG (by intro v hv; simp [hT, hv])
  have hTj : ∀ v, v.ord (jGeomGen K N) ≠ 0 → v ∈ T := memT hDj (by intro v hv; simp [hT, hv])
  have hT1 : ∀ v, v.ord (jGeomGen K N - algebraMap K _ 1728) ≠ 0 → v ∈ T := memT hD1 (by intro v hv; simp [hT, hv])
  have hTa : ∀ v, v.ord (jGeomGen K N - algebraMap K _ a₀) ≠ 0 → v ∈ T := memT hDa (by intro v hv; simp [hT, hv])

  have sG := sum_ord_eq_zero N K hG0 T hTG
  have sj := sum_ord_eq_zero N K hj0 T hTj
  have s1 := sum_ord_eq_zero N K hj1 T hT1
  have sa := sum_ord_eq_zero N K hja T hTa

  simp_rw [← zer_sub_pol N K] at sj s1 sa
  simp_rw [pol_sub_algebraMap N K] at s1 sa
  rw [Finset.sum_sub_distrib, sub_eq_zero] at sj s1 sa
  set P := ∑ v ∈ T, pol N K (jGeomGen K N) v with hP

  have hord₀ : 0 < v₀.ord (jGeomGen K N - algebraMap K _ a₀) :=
    ord_sub_evalAt_pos_of_isRational hv₀.1 hv₀.2.1.1 hja
  have hv₀T : v₀ ∈ T := hTa v₀ hord₀.ne'
  have hP1 : 1 ≤ P := by
    rw [← sa]
    calc (1 : ℤ) ≤ zer N K (jGeomGen K N - algebraMap K _ a₀) v₀ := by unfold zer; rw [max_eq_left hord₀.le]; omega
      _ ≤ ∑ v ∈ T, zer N K (jGeomGen K N - algebraMap K _ a₀) v :=
          Finset.single_le_sum (fun v _ => by unfold zer; exact le_max_right _ _) hv₀T

  have hsum := Finset.sum_le_sum fun v (_ : v ∈ T) => pointwise p N K hp5 hpN m hm G haff hcusp v
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [sG, sj, s1, ← hP] at hsum
  nlinarith [hsum, hP1, hm]

end Main

end NegWt

end

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (m : ℤ) (hm : m < 0) (G : ↥(modularFunctionFieldC K N))
    (haff : ∀ x : Place K (modularFunctionFieldC K N), IsAffineGeomPlace K N x →
        0 ≤ stackOrd N m G x)
    (hcusp : ∀ x : Place K (modularFunctionFieldC K N), x.ord (jGeomGen K N) < 0 →
        m * (-(x.ord (jGeomGen K N))) ≤ x.ord G) :
    G = 0 :=
  NegWt.main p N K hp5 hpN m hm G haff hcusp

end S_ModularCurve_eq_zero_of_forall_stackOrd_nonneg_of_forall_le_ord_of_neg
end P2MW
export P2MW.S_ModularCurve_eq_zero_of_forall_stackOrd_nonneg_of_forall_le_ord_of_neg (solution)
