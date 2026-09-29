-- Prove2me | solution 1 for ModularCurve.legendreJ_eq_ofNat_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/3715f064-c67a-5e77-908f-98dbcb4624f9

import Mathlib
import Definitions.Def_ModularCurve_LegendreJ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_legendreJ_eq_ofNat_iff

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "legendreJ"
p2m_open "ModularCurve"

theorem legendreJ_eq_ofNat_iff' {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 1728 ↔ t = -1 ∨ t = 2 ∨ t = 2⁻¹ := by
  have hden : t ^ 2 * (t - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1))
  have h64 : (64 : K) ≠ 0 := by
    rw [show (64 : K) = 2 ^ 6 by norm_num]; exact pow_ne_zero _ h2
  rw [legendreJ, div_eq_iff hden]
  constructor
  · intro h
    have key : (64 : K) * ((t + 1) ^ 2 * ((t - 2) ^ 2 * (2 * t - 1) ^ 2)) = 0 := by
      linear_combination h
    have key' := (mul_eq_zero.mp key).resolve_left h64
    rcases mul_eq_zero.mp key' with h | h
    · exact Or.inl (add_eq_zero_iff_eq_neg.mp ((pow_eq_zero_iff two_ne_zero).mp h))
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)))
    · have h' : 2 * t - 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h
      exact Or.inr (Or.inr (eq_inv_of_mul_eq_one_right (by linear_combination h')))
  · rintro (rfl | rfl | ht)
    · norm_num
    · norm_num
    · have h2t : (2 : K) * t = 1 := by rw [ht, mul_inv_cancel₀ h2]
      linear_combination
        (128 * t ^ 5 - 320 * t ^ 4 - 256 * t ^ 3 + 704 * t ^ 2 + 256 * t - 256) * h2t

end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_legendreJ_eq_ofNat_iff.ModularCurve"

theorem solution {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 1728 ↔ t = -1 ∨ t = 2 ∨ t = 2⁻¹ :=
  ModularCurve.legendreJ_eq_ofNat_iff' h2 ht0 ht1

end S_ModularCurve_legendreJ_eq_ofNat_iff
end P2MW
export P2MW.S_ModularCurve_legendreJ_eq_ofNat_iff (solution)
