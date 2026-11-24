-- Prove2me | solution 2 for GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:28:50.770009+00:00
-- url     : https://prove2.me/submissions/092593f8-b4c5-424b-8421-a77c40b2eb04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Theorems.Thm_GlobalTheory_CloseToUnitNorm_norm_eq_one_of_close
import Theorems.Thm_GlobalTheory_CloseToUnitNorm_norm_pow_sub_one_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CloseToUnitNorm
namespace GlobalTheory.CloseToUnitNorm
theorem _root_.solution {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - (1 : C)‖ < (1 : ℝ)) (i : ℤ) : ‖u ^ i - (1 : C)‖ ≤ ‖u - (1 : C)‖ := by
  have hu : ‖u‖ = 1 := norm_eq_one_of_close u h
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    exact zero_ne_one hu
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · rw [zpow_natCast]
    exact norm_pow_sub_one_le u hu n
  · rw [zpow_neg, zpow_natCast]
    have hn : u ^ n ≠ 0 := pow_ne_zero n hu0
    have e : (u ^ n)⁻¹ - 1 = -((u ^ n)⁻¹ * (u ^ n - 1)) := by
      field_simp
      ring
    rw [e, norm_neg, norm_mul, norm_inv, norm_pow, hu, one_pow, inv_one, one_mul]
    exact norm_pow_sub_one_le u hu n
end GlobalTheory.CloseToUnitNorm
