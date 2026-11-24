-- Prove2me | solution 1 for GlobalTheory.AdaptedDet.cmUnit_pow_four_idempotent_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:54:12.771799+00:00
-- url     : https://prove2.me/submissions/916ab4dc-f788-4e3d-be17-ba2259ea9deb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmUnitPowFourIdempotentModEight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AdaptedDet
namespace GlobalTheory.AdaptedDet
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 ^ 4 ≠ 0 ∧ ∃ t : 𝓞 E, H.w0 ^ 4 * H.w0 ^ 4 - H.w0 ^ 4 = (8 : ℕ) * t := by
  obtain ⟨k, hk⟩ : ∃ k, H.d = 16 * k + 7 := ⟨H.d / 16, by have := H.d_mod; omega⟩
  have h1 := H.rt_sq
  have h2 := H.two_weight_eq_one_add_root
  rw [hk] at h1
  push_cast at h1
  have hw : H.w0 ^ 2 = H.w0 - (4 * k + 2) := by
    apply mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)
    linear_combination h1 + (2 * H.w0 - 1 + H.rt) * h2
  constructor
  · intro h
    rw [pow_eq_zero_iff (by norm_num)] at h
    rw [h] at hw
    have : ((4 * k + 2 : ℕ) : 𝓞 E) = 0 := by
      push_cast
      linear_combination hw
    rw [Nat.cast_eq_zero] at this
    omega
  · have h4 : H.w0 ^ 4 = (-8 * k - 3) * H.w0 + (16 * k ^ 2 + 12 * k + 2) := by
      linear_combination (H.w0 ^ 2 + H.w0 - (4 * k + 2) + 0) * hw + hw
    refine ⟨(-8 * k - 3) * (4 * k ^ 2 + 2 * k) * H.w0 + (4 * k + 2) * (8 * k ^ 3 - 4 * k - 1), ?_⟩
    rw [h4]
    push_cast
    linear_combination (-8 * k - 3) ^ 2 * hw
end GlobalTheory.AdaptedDet
