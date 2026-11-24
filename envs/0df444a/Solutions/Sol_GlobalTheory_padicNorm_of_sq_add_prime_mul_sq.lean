-- Prove2me | solution 1 for GlobalTheory.padicNorm_of_sq_add_prime_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:29.881798+00:00
-- url     : https://prove2.me/submissions/ab6fd906-850c-4e57-b82d-aac16a8927bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SelfDualHermitianLatticeExistsNormOneMod
import Theorems.Thm_GlobalTheory_padicNorm_prime_mul_sq_ne_sq

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
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (s t : ℚ)
    (h : padicNorm p (s ^ 2 + (p : ℚ) * t ^ 2) = 1) :
    padicNorm p s ≤ 1 ∧ padicNorm p ((p : ℚ) * t ^ 2) < 1 := by
  have key : padicNorm p (s ^ 2) ≤ 1 ∧ padicNorm p ((p : ℚ) * t ^ 2) < 1 := by
    by_cases ht : t = 0
    · subst ht
      simp at h ⊢
      exact h.le
    · rw [padicNorm.add_eq_max_of_ne (padicNorm_prime_mul_sq_ne_sq p s t ht)] at h
      have h1 := padicNorm_prime_mul_sq_ne_sq p 1 t ht
      rw [one_pow, padicNorm.one] at h1
      exact ⟨h ▸ le_max_left _ _, lt_of_le_of_ne (h ▸ le_max_right _ _) h1.symm⟩
  refine ⟨?_, key.2⟩
  have h1 := key.1
  rw [sq, padicNorm.mul] at h1
  have := padicNorm.nonneg (p := p) s
  nlinarith
end GlobalTheory
