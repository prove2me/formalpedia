-- Prove2me | solution 1 for GlobalTheory.padicNorm_prime_mul_sq_ne_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:17.971034+00:00
-- url     : https://prove2.me/submissions/fc281042-f615-4083-a9fc-c1a5b653a10a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SelfDualHermitianLatticeExistsNormOneMod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (s t : ℚ) (ht : t ≠ 0) :
    padicNorm p (s ^ 2) ≠ padicNorm p ((p : ℚ) * t ^ 2) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have hpt : (p : ℚ) * t ^ 2 ≠ 0 := mul_ne_zero hp0 (pow_ne_zero _ ht)
  by_cases hs : s = 0
  · subst hs
    intro h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, padicNorm.zero] at h
    exact padicNorm.nonzero hpt h.symm
  · intro h
    rw [padicNorm.eq_zpow_of_nonzero (pow_ne_zero _ hs), padicNorm.eq_zpow_of_nonzero hpt,
      padicValRat.mul hp0 (pow_ne_zero _ ht), padicValRat.pow s, padicValRat.pow t,
      padicValRat.self hp.out.one_lt] at h
    have := zpow_right_injective₀ (by linarith) hp1.ne' h
    push_cast at this
    omega
end GlobalTheory
