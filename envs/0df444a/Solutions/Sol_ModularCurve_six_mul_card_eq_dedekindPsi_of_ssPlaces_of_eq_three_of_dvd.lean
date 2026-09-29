-- Prove2me | solution 1 for ModularCurve.six_mul_card_eq_dedekindPsi_of_ssPlaces_of_eq_three_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5c1a4129-1d09-5f12-9290-3ad360474925

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_EichlerMass
import Theorems.Thm_ModularCurve_card_eq_ssCountFormula_of_ssPlaces_of_lt_five
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_six_mul_card_eq_dedekindPsi_of_ssPlaces_of_eq_three_of_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

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

open AlgebraicCurve ModularCurve

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ]
    (W : Finset (Place κ (modularFunctionFieldC κ M'))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' κ) :
    6 * W.card = dedekindPsi M' := by
  have h := ModularCurve.card_eq_ssCountFormula_of_ssPlaces_of_lt_five q M' (by omega) hqM' κ W hW
  rw [ssCountFormula, eichlerMass, SSCountQ3Rigid.nuTwo_eq_zero_of_dvd M' ℓ hℓ hℓ12 hℓM',
    SSCountQ3Rigid.nuThree_eq_zero_of_dvd M' ℓ hℓ hℓ12 hℓM', hq3] at h
  have h' : ((6 * W.card : ℕ) : ℚ) = (dedekindPsi M' : ℚ) := by
    push_cast
    rw [h]
    ring
  exact_mod_cast h'

end S_ModularCurve_six_mul_card_eq_dedekindPsi_of_ssPlaces_of_eq_three_of_dvd
end P2MW
export P2MW.S_ModularCurve_six_mul_card_eq_dedekindPsi_of_ssPlaces_of_eq_three_of_dvd (solution)
