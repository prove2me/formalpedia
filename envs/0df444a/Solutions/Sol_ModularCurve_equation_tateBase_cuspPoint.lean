-- Prove2me | solution 1 for ModularCurve.equation_tateBase_cuspPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/bd903fd8-7dd4-514e-9845-4ce82bbe08f6

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_equation_tateBase_nonToricPoint
import Theorems.Thm_ModularCurve_equation_tateBase_tateToricPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_equation_tateBase_cuspPoint
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

universe u

p2m_open "ModularCurve P2MW.S_ModularCurve_equation_tateBase_cuspPoint.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "tateBase cuspPoint cuspPoint_of_eq_zero cuspPoint_of_ne_zero equation_tateBase_nonToricPoint equation_tateBase_tateToricPoint"
namespace CuspEq
p2m_open "ModularCurve"

variable {R : Type u} [CommRing R] {p : ℕ} [hp' : Fact p.Prime]

omit hp' in
theorem pow_eq_one_of_sum (ζ : R) (hζ : ∑ i ∈ Finset.range p, ζ ^ i = 0) : ζ ^ p = 1 := by
  have h := mul_geom_sum ζ p
  rw [hζ, mul_zero] at h
  exact (sub_eq_zero.mp h.symm)

omit hp' in
theorem one_sub_dvd_natCast (ζ : R) (hζ : ∑ i ∈ Finset.range p, ζ ^ i = 0) : (1 - ζ) ∣ (p : R) := by
  have h : (p : R) = ∑ i ∈ Finset.range p, (1 - ζ ^ i) := by
    rw [Finset.sum_sub_distrib, hζ, sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [h]
  exact Finset.dvd_sum fun i _ => one_sub_dvd_one_sub_pow ζ i

theorem isUnit_one_sub_pow (hp : IsUnit (p : R)) (ζ : R) (hζ : ∑ i ∈ Finset.range p, ζ ^ i = 0)
    (a : ZMod p) (ha : a ≠ 0) : IsUnit (1 - ζ ^ a.val) := by
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

theorem main (hp : IsUnit (p : R)) (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0)
    (v : Fin 2 → ZMod p) (hv : v ≠ 0) :
    (tateBase R p).toAffine.Equation (cuspPoint R p ζ v).1 (cuspPoint R p ζ v).2 := by
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      funext i
      fin_cases i
      · exact h0
      · exact h1
    rw [cuspPoint_of_eq_zero ζ h1]
    refine ModularCurve.equation_tateBase_tateToricPoint R p (ζ ^ (v 0).val) ?_
    rw [Units.val_pow_eq_pow_val]
    exact isUnit_one_sub_pow hp (ζ : R) hζ (v 0) h0
  · have hj : 0 < (v 1).val := Nat.pos_of_ne_zero fun h => h1 ((ZMod.val_eq_zero _).mp h)
    rw [cuspPoint_of_ne_zero ζ h1]
    exact ModularCurve.equation_tateBase_nonToricPoint R p _ _ hj (ZMod.val_lt _)

end ModularCurve.CuspEq

theorem solution {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    (hp : IsUnit (p : R)) (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0)
    (v : Fin 2 → ZMod p) (hv : v ≠ 0) :
    (ModularCurve.tateBase R p).toAffine.Equation
      (ModularCurve.cuspPoint R p ζ v).1 (ModularCurve.cuspPoint R p ζ v).2 :=
  ModularCurve.CuspEq.main hp ζ hζ v hv

end S_ModularCurve_equation_tateBase_cuspPoint
end P2MW
export P2MW.S_ModularCurve_equation_tateBase_cuspPoint (solution)
