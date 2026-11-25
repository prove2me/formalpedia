-- Prove2me | solution 1 for GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:33:35.146602+00:00
-- url     : https://prove2.me/submissions/410aa75b-8ecb-4175-a980-1170b8b8a9d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLe
import Theorems.Thm_GlobalTheory_UnitNormPowerSubOne_norm_eq_one
import Theorems.Thm_GlobalTheory_UnitNormPowerSubOne_norm_pow_sub_one_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitNormPowerSubOne
namespace GlobalTheory.UnitNormPowerSubOne
theorem _root_.solution {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) (i : ℤ) : ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
  have hn := norm_eq_one u h
  have hu : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]
    exact norm_pow_sub_one_le u h n
  · have hp : u ^ n ≠ 0 := pow_ne_zero n hu
    have e : u ^ (-(n : ℤ)) - 1 = -((u ^ n)⁻¹ * (u ^ n - 1)) := by
      rw [zpow_neg, zpow_natCast, mul_sub, inv_mul_cancel₀ hp, mul_one, neg_sub]
    rw [e, norm_neg, norm_mul, norm_inv, norm_pow, hn, one_pow, inv_one, one_mul]
    exact norm_pow_sub_one_le u h n
end GlobalTheory.UnitNormPowerSubOne
