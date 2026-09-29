-- Prove2me | solution 1 for ModularCurve.placeWidthChar_eq_one_of_mem_ssPlaces_of_eq_three_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/2ce14e63-23fb-5a9b-9d77-2bb381f9c2e7

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_EichlerMass
import Theorems.Thm_ModularCurve_card_eq_ssCountFormula_of_ssPlaces_of_lt_five
import Theorems.Thm_ModularCurve_sum_ord_jGeomGen_sub_eq_dedekindPsi
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_good
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_placeWidthChar_eq_one_of_mem_ssPlaces_of_eq_three_of_dvd
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄"
p2m_attr_erase "simp" "TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"

set_option autoImplicit false

namespace SSCountQ3Rigid

open ModularCurve

theorem noRoot_of_mod_twelve (ℓ : ℕ) (hℓ : ℓ.Prime) (h12 : ℓ % 12 = 11) (x : ZMod ℓ) :
    x ^ 2 + x + 1 ≠ 0 ∧ x ^ 2 + 1 ≠ 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hx1 : x ≠ 1 := by
      rintro rfl; norm_num at hx
      have : ((3 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast hx
      rw [ZMod.natCast_eq_zero_iff] at this
      have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 this; omega
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have hx3 : x ^ 3 = 1 := by
      have : x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by ring
      rw [hx, mul_zero, sub_eq_zero] at this; exact this
    have hord : orderOf (Units.mk0 x hx0) = 3 := by
      refine orderOf_eq_prime ?_ ?_
      · ext; simp [hx3]
      · intro h; apply hx1; have := congrArg Units.val h; simpa using this
    have hdvd : 3 ∣ Fintype.card (ZMod ℓ)ˣ := hord ▸ orderOf_dvd_card
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hℓ] at hdvd
    omega
  · have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have hx2 : x ^ 2 = -1 := eq_neg_of_add_eq_zero_left hx
    have hx1 : x ^ 2 ≠ 1 := by
      rw [hx2]; intro h
      have h2 : (2 : ZMod ℓ) = 0 := by linear_combination -h
      have : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h2
      rw [ZMod.natCast_eq_zero_iff] at this
      have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this; omega
    have hx4 : x ^ 4 = 1 := by rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hx2]; ring
    have hord : orderOf (Units.mk0 x hx0) = 4 := by
      refine (orderOf_eq_iff (by norm_num)).2 ⟨by ext; simp [hx4], fun m hm hm0 h => ?_⟩
      have hm' : (x : ZMod ℓ) ^ m = 1 := by have := congrArg Units.val h; simpa using this
      interval_cases m
      · apply hx1; rw [pow_one] at hm'; rw [hm']; ring
      · exact hx1 hm'
      · have : x ^ 4 = x := by rw [pow_succ, hm', one_mul]
        rw [hx4] at this
        apply hx1; rw [← this]; ring
    have hdvd : 4 ∣ Fintype.card (ZMod ℓ)ˣ := hord ▸ orderOf_dvd_card
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hℓ] at hdvd
    omega

theorem nuTwo_eq_zero_of_dvd (M' ℓ : ℕ) (hℓ : ℓ.Prime) (h12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M') :
    nuTwo M' = 0 := by
  unfold nuTwo
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨fun ⟨x, hx⟩ => ?_⟩
  have := congrArg (ZMod.castHom hℓM' (ZMod ℓ)) hx
  simp only [map_add, map_pow, map_one, map_zero] at this
  exact (noRoot_of_mod_twelve ℓ hℓ h12 _).2 this

theorem nuThree_eq_zero_of_dvd (M' ℓ : ℕ) (hℓ : ℓ.Prime) (h12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M') :
    nuThree M' = 0 := by
  unfold nuThree
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨fun ⟨x, hx⟩ => ?_⟩
  have := congrArg (ZMod.castHom hℓM' (ZMod ℓ)) hx
  simp only [map_add, map_pow, map_one, map_zero] at this
  exact (noRoot_of_mod_twelve ℓ hℓ h12 _).1 this

end SSCountQ3Rigid

noncomputable section

namespace Width3Sol

open AlgebraicCurve ModularCurve

theorem ssJSet_three_eq (k : Type*) [Field k] [CharP k 3] [IsAlgClosed k] [DecidableEq k] :
    ssJSet 3 k = {(0 : k)} := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  ext a
  constructor
  · intro ha
    have hpow := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet 3 ha
    exact ModularCurve.eq_zero_of_mem_ssJSet_three a ha hpow
  · intro ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact ModularCurve.zero_mem_ssJSet_of_lt_five (by norm_num)

theorem jNGeomGen_mem_of_jGeomGen_mem (K : Type*) [Field K] (N : ℕ) [NeZero N]
    {w : Place K (modularFunctionFieldC K N)} (hj : jGeomGen K N ∈ w.toValuationSubring) :
    jNGeomGen K N ∈ w.toValuationSubring := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have hfac : Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldC K N)) (jGeomGen K N)
      = (SubringClass.subtype w.toValuationSubring).comp
          (Polynomial.eval₂RingHom (Int.castRingHom w.toValuationSubring) ⟨jGeomGen K N, hj⟩) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp
  refine w.mem_of_eval_monic_eq_zero
    (P := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldC K N))
      (jGeomGen K N)))
    (data.monic.map _) (fun i => ?_) ?_
  · rw [Polynomial.coeff_map, hfac, RingHom.comp_apply]
    exact SetLike.coe_mem _
  · rw [Polynomial.eval_map]
    exact evalModularPair_jGeomGen_eq_zero K N data

theorem mem_ssPlaces_and_evalAt_eq_iff_ord_pos (q N : ℕ) [NeZero N] (K : Type*) [Field K]
    [DecidableEq K] [IsAlgClosed K] {a : K} (ha : a ∈ ssJSet q K)
    (w : Place K (modularFunctionFieldC K N)) :
    (w ∈ ssPlaces q N K ∧ w.evalAt (jGeomGen K N) = a)
      ↔ 0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) := by
  constructor
  · rintro ⟨hss, hev⟩
    rw [mem_ssPlaces_iff, isSupersingularPlace_iff] at hss
    have hc : 0 < w.ord (jGeomGen K N
        - algebraMap K (modularFunctionFieldC K N) (w.evalAt (jGeomGen K N))) :=
      (exists_isCentreOf_of_isRational hss.1 hss.2.1).1
    rwa [hev] at hc
  · intro hpos
    have hrat : w.IsRational :=
      (Place.isRational_iff_deg_eq_one w).mpr (place_deg_eq_one_of_isAlgClosed K N w)
    have hj : jGeomGen K N ∈ w.toValuationSubring := by
      have h := add_mem (w.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero K N a) hpos.le)
        (w.algebraMap_mem' a)
      rwa [sub_add_cancel] at h
    have hjN : jNGeomGen K N ∈ w.toValuationSubring := jNGeomGen_mem_of_jGeomGen_mem K N hj
    have hev : w.evalAt (jGeomGen K N) = a := by
      rw [w.evalAt_congr hj (w.algebraMap_mem' a) (Or.inr hpos), w.evalAt_algebraMap]
    refine ⟨?_, hev⟩
    rw [mem_ssPlaces_iff, isSupersingularPlace_iff]
    refine ⟨hrat, ⟨hj, hjN⟩, ?_⟩
    rw [hev]
    exact ha

end Width3Sol

end

open AlgebraicCurve ModularCurve in
open Width3Sol in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq3 : q = 3) {M' : ℕ} [NeZero M']
    {K : Type*} [Field K] [CharP K q] [IsAlgClosed K] [DecidableEq K]
    (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    {w : Place K (modularFunctionFieldC K M')} (hw : w ∈ ssPlaces q M' K) :
    placeWidthChar q M' w = 1 := by
  subst hq3

  have hev0 : ∀ {v : Place K (modularFunctionFieldC K M')}, v ∈ ssPlaces 3 M' K →
      v.evalAt (jGeomGen K M') = 0 := by
    intro v hv
    rw [mem_ssPlaces_iff, isSupersingularPlace_iff] at hv
    have h := hv.2.2
    rw [ssJSet_three_eq K] at h
    exact h
  have hsep := ModularCurve.isSeparable_jqNModC_of_good K M' 3 hqM'

  obtain ⟨T, hT⟩ : ∃ T : Finset (Place K (modularFunctionFieldC K M')),
      ∀ v, v ∈ T ↔ 0 < v.ord (jGeomGen K M' - algebraMap K (modularFunctionFieldC K M') 0) :=
    ⟨(ModularCurve.finite_setOf_ord_jGeomGen_sub_pos K M' hsep 0).toFinset, fun v => by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]⟩
  have hsum := ModularCurve.sum_ord_jGeomGen_sub_eq_dedekindPsi 3 M' hqM' K hsep 0 T hT

  have h0mem : (0 : K) ∈ ssJSet 3 K := ModularCurve.zero_mem_ssJSet_of_lt_five (by norm_num)
  have hTss : ∀ v, v ∈ T ↔ v ∈ ssPlaces 3 M' K := by
    intro v
    rw [hT, ← mem_ssPlaces_and_evalAt_eq_iff_ord_pos 3 M' K h0mem v]
    exact ⟨And.left, fun hv => ⟨hv, hev0 hv⟩⟩
  have hcount : 6 * T.card = dedekindPsi M' := by
    have h := ModularCurve.card_eq_ssCountFormula_of_ssPlaces_of_lt_five 3 M' (by omega) hqM' K T hTss
    rw [ssCountFormula, eichlerMass, SSCountQ3Rigid.nuTwo_eq_zero_of_dvd M' ℓ hℓ hℓ12 hℓM',
      SSCountQ3Rigid.nuThree_eq_zero_of_dvd M' ℓ hℓ hℓ12 hℓM'] at h
    have h' : ((6 * T.card : ℕ) : ℚ) = (dedekindPsi M' : ℚ) := by
      push_cast
      rw [h]
      ring
    exact_mod_cast h'

  have hram : ∀ {v : Place K (modularFunctionFieldC K M')}, v ∈ ssPlaces 3 M' K →
      placeRamificationJ M' v = (v.ord (jGeomGen K M' - algebraMap K (modularFunctionFieldC K M') 0)).toNat := by
    intro v hv
    unfold placeRamificationJ
    rw [hev0 hv]
  have hle : ∀ v ∈ T, v.ord (jGeomGen K M' - algebraMap K (modularFunctionFieldC K M') 0) ≤ 6 := by
    intro v hv
    have hvss := (hTss v).mp hv
    have hpos := (hT v).mp hv
    have hd := ModularCurve.placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces hqM' hvss
    rw [jWidthChar_three_of_eq_zero (hev0 hvss), hram hvss] at hd
    have h6 := Nat.le_of_dvd (by norm_num) hd
    omega

  have hsum6 : ∑ v ∈ T, v.ord (jGeomGen K M' - algebraMap K (modularFunctionFieldC K M') 0)
      = ∑ v ∈ T, (6 : ℤ) := by
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    have : ((6 * T.card : ℕ) : ℤ) = (dedekindPsi M' : ℤ) := by exact_mod_cast hcount
    push_cast at this
    linarith
  have hall := (Finset.sum_eq_sum_iff_of_le hle).mp hsum6
  have hwT : w ∈ T := (hTss w).mpr hw
  have hord := hall w hwT

  unfold placeWidthChar
  rw [hram hw, hord, jWidthChar_three_of_eq_zero (hev0 hw)]
  rfl

end S_ModularCurve_placeWidthChar_eq_one_of_mem_ssPlaces_of_eq_three_of_dvd
end P2MW
export P2MW.S_ModularCurve_placeWidthChar_eq_one_of_mem_ssPlaces_of_eq_three_of_dvd (solution)
