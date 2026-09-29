-- Prove2me | solution 1 for ModularCurve.coeff_slotSubst_tateUnivX_mul_sub_coeff_mem_span_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/251452df-f963-5e6a-aa29-d2be84b2efe9

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_slotSubst_tateUnivX_mul_sub_coeff_mem_span_sub_one

set_option autoImplicit false

theorem solution
    {K : Type} [CommRing K] (p : ℕ) (c ζ : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) :
    PowerSeries.coeff n (ModularCurve.slotSubst K p (ζ * c) j ModularCurve.tateUnivX) -
        PowerSeries.coeff n (ModularCurve.slotSubst K p c j ModularCurve.tateUnivX) ∈
      Ideal.span {((ζ : K) - 1)} := by
  rw [← Ideal.Quotient.eq]
  set π := Ideal.Quotient.mk (Ideal.span {((ζ : K) - 1)}) with hπ
  have hζ : π (ζ : K) = 1 := by
    rw [← map_one π, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have hζi : π ((ζ⁻¹ : Kˣ) : K) = 1 := by
    have h : π ((ζ⁻¹ : Kˣ) : K) * π (ζ : K) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rwa [hζ, mul_one] at h
  rw [ModularCurve.coeff_slotSubst_tateUnivX p (ζ * c) j hj hjp n,
    ModularCurve.coeff_slotSubst_tateUnivX p c j hj hjp n]
  simp only [map_add, map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, apply_ite π, map_zero,
    Units.val_mul, mul_inv, mul_pow, hζ, hζi, one_pow, one_mul]

#print axioms solution

end S_ModularCurve_coeff_slotSubst_tateUnivX_mul_sub_coeff_mem_span_sub_one
end P2MW
export P2MW.S_ModularCurve_coeff_slotSubst_tateUnivX_mul_sub_coeff_mem_span_sub_one (solution)
