-- Prove2me | solution 1 for ModularCurve.ncard_setOf_ord_jGeomGen_eq_three_and_eq_six_of_exists_prime_dvd_mod_three_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b75d8919-8efe-5786-8201-58bd5a9027df

import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_card_eq_ssCountFormula_of_ssPlaces_of_lt_five
import Theorems.Thm_ModularCurve_sum_ord_jGeomGen_sub_eq_dedekindPsi
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ncard_setOf_ord_jGeomGen_eq_three_and_eq_six_of_exists_prime_dvd_mod_three_eq_two
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

namespace R3cSSCount

private theorem nuTwo_three : ModularCurve.nuTwo 3 = 0 := by
  unfold ModularCurve.nuTwo
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

private theorem nuThree_three : ModularCurve.nuThree 3 = 1 := by
  unfold ModularCurve.nuThree
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

private theorem nuThree_eq_zero {N : ℕ} (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2) : ModularCurve.nuThree N = 0 := by
  obtain ⟨q, hq, hqN, hq3⟩ := hε
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 := hq.two_le
  unfold ModularCurve.nuThree
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun ⟨x, hx⟩ => ?_⟩
  have hy0 : ZMod.castHom hqN (ZMod q) x ^ 2 + ZMod.castHom hqN (ZMod q) x + 1 = 0 := by
    have h := congrArg (ZMod.castHom hqN (ZMod q)) hx
    rw [map_add, map_add, map_pow, map_one, map_zero] at h
    exact h
  generalize ZMod.castHom hqN (ZMod q) x = y at hy0
  have hy3 : y ^ 3 = 1 := by linear_combination (y - 1) * hy0
  have hy1 : y ≠ 1 := by
    rintro rfl
    have h3 : ((3 : ℕ) : ZMod q) = 0 := by
      push_cast
      linear_combination hy0
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
    omega
  have hyne : y ≠ 0 := by
    rintro rfl
    simp at hy0
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hdvd : orderOf y ∣ q - 1 := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hyne)
  rw [hord] at hdvd
  omega

private theorem solve {ι : Type} (T : Finset ι) (f : ι → ℤ) (hsplit : ∀ w ∈ T, f w = 3 ∨ f w = 6) (ψ ν : ℕ)
    (h1 : (T.card : ℚ) = (ψ : ℚ) / 6 + (ν : ℚ) / 2) (h2 : ∑ w ∈ T, f w = ψ) :
    (((T.filter fun w => f w = 3).card : ℕ) : ℚ) = ν ∧
      (((T.filter fun w => f w = 6).card : ℕ) : ℚ) = (ψ : ℚ) / 6 - (ν : ℚ) / 2 := by
  have hnot : T.filter (fun w => ¬ f w = 3) = T.filter fun w => f w = 6 := by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hw, h3⟩
      exact ⟨hw, (hsplit w hw).resolve_left h3⟩
    · rintro ⟨hw, h6⟩
      exact ⟨hw, by omega⟩
  have hcard : (T.filter fun w => f w = 3).card + (T.filter fun w => f w = 6).card = T.card := by
    rw [← hnot]
    exact Finset.card_filter_add_card_filter_not ..
  have hsum : ∑ w ∈ T, f w =
      ((T.filter fun w => f w = 3).card : ℤ) * 3 + ((T.filter fun w => f w = 6).card : ℤ) * 6 := by
    rw [← Finset.sum_filter_add_sum_filter_not T (fun w => f w = 3), hnot,
      Finset.sum_eq_card_nsmul (b := (3 : ℤ)) (fun w hw => (Finset.mem_filter.mp hw).2),
      Finset.sum_eq_card_nsmul (b := (6 : ℤ)) (fun w hw => (Finset.mem_filter.mp hw).2)]
    simp only [nsmul_eq_mul]
  have e1 : (((T.filter fun w => f w = 3).card : ℕ) : ℚ) + ((T.filter fun w => f w = 6).card : ℕ) =
      (ψ : ℚ) / 6 + (ν : ℚ) / 2 := by
    rw [← h1]
    exact_mod_cast hcard
  have e2 : (((T.filter fun w => f w = 3).card : ℕ) : ℚ) * 3 + (((T.filter fun w => f w = 6).card : ℕ) : ℚ) * 6 =
      ψ := by
    have h := h2
    rw [hsum] at h
    exact_mod_cast h
  constructor <;> linarith

open AlgebraicCurve ModularCurve in

private theorem mem_ssPlaces_iff_ord_pos {F : Type} [Field F] [CharP F 3] [IsAlgClosed F] [DecidableEq F] (N' : ℕ)
    [NeZero N'] (w : Place F (modularFunctionFieldC F N')) :
    w ∈ ssPlaces 3 N' F ↔ 0 < w.ord (jGeomGen F N') := by
  haveI : IsCurveOver F (modularFunctionFieldC F N') := isCurveOver_modularFunctionFieldC_of_perfectField F N'
  have hrat : w.IsRational := by
    haveI : Module.Finite F w.ResidueField := IsCurveOver.finiteResidue w
    haveI : Algebra.IsIntegral F w.ResidueField := Algebra.IsIntegral.of_finite F w.ResidueField
    show Function.Surjective (algebraMap F w.ResidueField)
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  have hj0 : jGeomGen F N' ≠ 0 := by
    intro h
    exact jqModC_ne_zero_def F (congrArg Subtype.val h)
  constructor
  · intro h
    obtain ⟨-, haff, hss⟩ := h
    have hval : w.evalAt (jGeomGen F N') = 0 :=
      eq_zero_of_mem_ssJSet_three _ hss (pow_q_sq_eq_self_of_mem_ssJSet 3 hss)
    have h1 := (Place.evalAt_eq_zero_iff_one_le_ord w hrat hj0 haff.1).mp hval
    omega
  · intro hpos
    have haff : IsAffineGeomPlace F N' w :=
      (isAffineGeomPlace_or_ord_jGeomGen_lt_zero F N' w).resolve_right (by omega)
    have hval : w.evalAt (jGeomGen F N') = 0 :=
      (Place.evalAt_eq_zero_iff_one_le_ord w hrat hj0 haff.1).mpr (by omega)
    show w.IsRational ∧ IsAffineGeomPlace F N' w ∧ w.evalAt (jGeomGen F N') ∈ ssJSet 3 F
    refine ⟨hrat, haff, ?_⟩
    rw [hval]
    exact zero_mem_ssJSet_of_lt_five (by norm_num)

end R3cSSCount

open ModularCurve in
theorem solution
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (F : Type) [Field F] [CharP F 3] [IsAlgClosed F] :
    (Set.ncard {w : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N') |
        w.ord (ModularCurve.jGeomGen F N') = 3} : ℚ) = (ModularCurve.nuTwo N' : ℚ) ∧
      (Set.ncard {w : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N') |
        w.ord (ModularCurve.jGeomGen F N') = 6} : ℚ) =
        (ModularCurve.dedekindPsi N' : ℚ) / 6 - (ModularCurve.nuTwo N' : ℚ) / 2 := by
  classical
  have hN : (N' : F) ≠ 0 := fun h => hpN' ((CharP.cast_eq_zero_iff F 3 N').mp h)
  have hsep := ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero F N' hN
  have hfin : {w : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N') |
      0 < w.ord (ModularCurve.jGeomGen F N')}.Finite := by
    have h := ModularCurve.finite_setOf_ord_jGeomGen_sub_pos F N' hsep 0
    simp only [map_zero, sub_zero] at h
    exact h
  have hT : ∀ w, w ∈ hfin.toFinset ↔ 0 < w.ord (ModularCurve.jGeomGen F N') := fun w => hfin.mem_toFinset
  have h1 : (hfin.toFinset.card : ℚ) = ModularCurve.ssCountFormula N' 3 :=
    ModularCurve.card_eq_ssCountFormula_of_ssPlaces_of_lt_five 3 N' (by norm_num) hpN' F hfin.toFinset
      fun w => (hT w).trans (R3cSSCount.mem_ssPlaces_iff_ord_pos N' w).symm
  have h1' : (hfin.toFinset.card : ℚ) =
      (ModularCurve.dedekindPsi N' : ℚ) / 6 + (ModularCurve.nuTwo N' : ℚ) / 2 := by
    rw [h1]
    unfold ModularCurve.ssCountFormula ModularCurve.eichlerMass
    rw [R3cSSCount.nuTwo_three, R3cSSCount.nuThree_three, R3cSSCount.nuThree_eq_zero hε]
    push_cast
    ring
  have h2 : ∑ w ∈ hfin.toFinset, w.ord (ModularCurve.jGeomGen F N') = ModularCurve.dedekindPsi N' := by
    have h := ModularCurve.sum_ord_jGeomGen_sub_eq_dedekindPsi 3 N' hpN' F hsep 0 hfin.toFinset fun w => by
      simp only [map_zero, sub_zero]
      exact hT w
    simp only [map_zero, sub_zero] at h
    exact h
  have hsplit : ∀ w ∈ hfin.toFinset,
      w.ord (ModularCurve.jGeomGen F N') = 3 ∨ w.ord (ModularCurve.jGeomGen F N') = 6 := fun w hw =>
    ModularCurve.ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed N' hpN' hε F w
      ((hT w).mp hw)
  obtain ⟨e3, e6⟩ := R3cSSCount.solve hfin.toFinset (fun w => w.ord (ModularCurve.jGeomGen F N')) hsplit
    (ModularCurve.dedekindPsi N') (ModularCurve.nuTwo N') h1' h2
  have hA : {w : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N') |
      w.ord (ModularCurve.jGeomGen F N') = 3} =
      ↑(hfin.toFinset.filter fun w => w.ord (ModularCurve.jGeomGen F N') = 3) := by
    ext w
    rw [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, hT]
    constructor
    · intro h
      exact ⟨by omega, h⟩
    · intro h
      exact h.2
  have hB : {w : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N') |
      w.ord (ModularCurve.jGeomGen F N') = 6} =
      ↑(hfin.toFinset.filter fun w => w.ord (ModularCurve.jGeomGen F N') = 6) := by
    ext w
    rw [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, hT]
    constructor
    · intro h
      exact ⟨by omega, h⟩
    · intro h
      exact h.2
  rw [hA, hB, Set.ncard_coe_finset, Set.ncard_coe_finset]
  constructor
  · convert e3 using 3
  · convert e6 using 3

end S_ModularCurve_ncard_setOf_ord_jGeomGen_eq_three_and_eq_six_of_exists_prime_dvd_mod_three_eq_two
end P2MW
export P2MW.S_ModularCurve_ncard_setOf_ord_jGeomGen_eq_three_and_eq_six_of_exists_prime_dvd_mod_three_eq_two (solution)
