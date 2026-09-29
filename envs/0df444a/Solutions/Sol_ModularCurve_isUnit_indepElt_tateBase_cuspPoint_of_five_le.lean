-- Prove2me | solution 1 for ModularCurve.isUnit_indepElt_tateBase_cuspPoint_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d33db4b5-9051-5432-ac41-d592ba0dbaff

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_isUnit_indepElt_tateBase_tateToricPoint_nonToricPoint
import Theorems.Thm_ModularCurve_isUnit_indepElt_symm
import Theorems.Thm_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le
import Theorems.Thm_ModularCurve_equation_tateBase_nonToricPoint
import Theorems.Thm_ModularCurve_equation_tateBase_tateToricPoint
import Theorems.Thm_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero_of_five_le
import Theorems.Thm_ModularCurve_eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_of_five_le
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

universe u

p2m_open "ModularCurve P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_of_five_le.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "tateBase indepElt cuspPoint cuspPoint_of_eq_zero cuspPoint_of_ne_zero isUnit_Δ_tateBase isUnit_indepElt_tateBase_tateToricPoint_nonToricPoint isUnit_indepElt_symm isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le equation_tateBase_nonToricPoint equation_tateBase_tateToricPoint eval_prePsi_tateBase_nonToricPoint_eq_zero_of_five_le eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le"
namespace CuspAux
p2m_open "ModularCurve"

variable {R : Type u} [CommRing R] {p : ℕ}

theorem pow_eq_one_of_sum (ζ : R) (hζ : ∑ i ∈ Finset.range p, ζ ^ i = 0) : ζ ^ p = 1 := by
  have h := mul_geom_sum ζ p
  rw [hζ, mul_zero] at h
  exact (sub_eq_zero.mp h.symm)

theorem units_pow_eq_one (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) (n : ℕ) :
    (ζ ^ n) ^ p = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]
  have : ζ ^ p = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]; exact pow_eq_one_of_sum (ζ : R) hζ)
  rw [this, one_pow]

theorem one_sub_dvd_natCast (ζ : R) (hζ : ∑ i ∈ Finset.range p, ζ ^ i = 0) : (1 - ζ) ∣ (p : R) := by
  have h : (p : R) = ∑ i ∈ Finset.range p, (1 - ζ ^ i) := by
    rw [Finset.sum_sub_distrib, hζ, sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [h]
  exact Finset.dvd_sum fun i _ => one_sub_dvd_one_sub_pow ζ i

theorem isUnit_one_sub_pow [Fact p.Prime] (hp : IsUnit (p : R)) (ζ : R)
    (hζ : ∑ i ∈ Finset.range p, ζ ^ i = 0) (a : ZMod p) (ha : a ≠ 0) : IsUnit (1 - ζ ^ a.val) := by
  have hζp : ζ ^ p = 1 := pow_eq_one_of_sum ζ hζ
  have hinv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hmod : (a.val * (a⁻¹).val) % p = 1 := by
    rw [← ZMod.val_mul, hinv, ZMod.val_one]
  have hdiv := Nat.div_add_mod (a.val * (a⁻¹).val) p
  have hpow : (ζ ^ a.val) ^ (a⁻¹).val = ζ := by
    rw [← pow_mul, ← hdiv, hmod, pow_add, pow_one, pow_mul, hζp, one_pow, one_mul]
  have hdvd : (1 - ζ ^ a.val) ∣ (1 - ζ) := by
    conv_rhs => rw [← hpow]
    exact one_sub_dvd_one_sub_pow _ _
  exact isUnit_of_dvd_unit (hdvd.trans (one_sub_dvd_natCast ζ hζ)) hp

theorem isUnit_one_sub_units_pow [Fact p.Prime] (hp : IsUnit (p : R)) (ζ : Rˣ)
    (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) (a : ZMod p) (ha : a ≠ 0) :
    IsUnit (1 - ((ζ ^ a.val : Rˣ) : R)) := by
  rw [Units.val_pow_eq_pow_val]; exact isUnit_one_sub_pow hp (ζ : R) hζ a ha

theorem val_pos_of_ne_zero [NeZero p] {a : ZMod p} (ha : a ≠ 0) : 0 < a.val :=
  Nat.pos_of_ne_zero fun h => ha ((ZMod.val_eq_zero _).mp h)

theorem fst_ne_zero_of_toric {v w : Fin 2 → ZMod p} (hv : v 1 = 0) (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    v 0 ≠ 0 := by
  intro h0; apply hvw; rw [hv, h0]; ring

end ModularCurve.CuspAux

open ModularCurve.CuspAux in
theorem solution {R : Type u} [CommRing R] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (hp : IsUnit (p : R)) (ζ : Rˣ)
    (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) (v w : Fin 2 → ZMod p)
    (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    IsUnit (ModularCurve.indepElt (ModularCurve.tateBase R p) p
      (ModularCurve.cuspPoint R p ζ v).1 (ModularCurve.cuspPoint R p ζ w).1) := by
  have hp2 : p ≠ 2 := by omega
  have hpL : IsUnit ((p : ℕ) : LaurentSeries R) := by
    simpa using hp.map (algebraMap R (LaurentSeries R))
  by_cases hv1 : v 1 = 0
  · have hv0 : v 0 ≠ 0 := fst_ne_zero_of_toric hv1 hvw
    by_cases hw1 : w 1 = 0
    · exfalso; apply hvw; rw [hv1, hw1]; ring
    ·
      rw [cuspPoint_of_eq_zero ζ hv1, cuspPoint_of_ne_zero ζ hw1]
      exact ModularCurve.isUnit_indepElt_tateBase_tateToricPoint_nonToricPoint R p _ _
        (isUnit_one_sub_units_pow hp ζ hζ (v 0) hv0) _ (val_pos_of_ne_zero hw1) (ZMod.val_lt _)
  · by_cases hw1 : w 1 = 0
    ·
      have hwv : w 0 * v 1 - w 1 * v 0 ≠ 0 := by intro h; apply hvw; linear_combination -h
      have hw0 : w 0 ≠ 0 := fst_ne_zero_of_toric hw1 hwv
      rw [cuspPoint_of_ne_zero ζ hv1, cuspPoint_of_eq_zero ζ hw1]
      have h1w := isUnit_one_sub_units_pow hp ζ hζ (w 0) hw0
      have hjv := val_pos_of_ne_zero hv1
      refine ModularCurve.isUnit_indepElt_symm (tateBase R p) p hp2 hpL (isUnit_Δ_tateBase R p)
        (ModularCurve.equation_tateBase_tateToricPoint R p _ h1w)
        (ModularCurve.equation_tateBase_nonToricPoint R p _ _ hjv (ZMod.val_lt _))
        (ModularCurve.eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le R p hp5 _
          (units_pow_eq_one ζ hζ _) h1w)
        (ModularCurve.eval_prePsi_tateBase_nonToricPoint_eq_zero_of_five_le R p hp5 _
          (units_pow_eq_one ζ hζ _) _ hjv (ZMod.val_lt _))
        (ModularCurve.isUnit_indepElt_tateBase_tateToricPoint_nonToricPoint R p _ _ h1w _ hjv (ZMod.val_lt _))
    ·
      exact ModularCurve.isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le hp5 hp ζ hζ v w hv1 hw1 hvw

end S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_of_five_le
end P2MW
export P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_of_five_le (solution)
