-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.charZero_or_charP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:27:36.561838+00:00
-- url     : https://prove2.me/submissions/e2070270-be03-40fb-bd3a-1335e918591e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCharP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] :
    CharZero K ∨ CharP K p := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | hq
  · right
    have hq' : Fact (ringChar K).Prime := ⟨hq⟩
    by_contra hne
    have hpq : p ≠ ringChar K := fun h => hne (h ▸ ringChar.charP K)

    have hpz : ((p : ZMod (ringChar K))) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact hpq ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).1 hdvd).symm
    have hferm := ZMod.pow_card_sub_one_eq_one hpz
    have hK : (p : K) ^ (ringChar K - 1) = 1 := by
      have := congrArg (ZMod.castHom (dvd_refl (ringChar K)) K) hferm
      simpa using this
    have hn := congrArg norm hK
    rw [norm_pow, norm_one] at hn
    have hlt := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
    have hpos : ringChar K - 1 ≠ 0 := by have := hq.two_le; omega
    have : ‖(p : K)‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos).1 hn
    linarith
  · left
    have : CharP K 0 := by rw [← hq]; exact ringChar.charP K
    exact CharP.charP_to_charZero K
end GroundTheory.PAdicHodge.IsPerfectoidField
