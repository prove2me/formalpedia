-- Prove2me | solution 1 for GlobalTheory.dvrSubring_eq_pow_mul_nonmem_of_not_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:35:59.809023+00:00
-- url     : https://prove2.me/submissions/f9936359-42ff-44dd-a10a-197237463208

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvrSubringEqTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (S : Subring V) (π : V) (hπm : π ∈ IsLocalRing.maximalIdeal V)
    (hdiv : ∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t) :
    ∀ N : ℕ, ∀ s ∈ S, s ∉ (IsLocalRing.maximalIdeal V) ^ N →
      ∃ k : ℕ, ∃ u ∈ S, u ∉ IsLocalRing.maximalIdeal V ∧ s = π ^ k * u := by
  intro N
  induction N with
  | zero => intro s _ hs; simp at hs
  | succ N ih =>
    intro s hs hsN
    by_cases hm : s ∈ IsLocalRing.maximalIdeal V
    · obtain ⟨t, htS, rfl⟩ := hdiv s hs hm
      have htN : t ∉ (IsLocalRing.maximalIdeal V) ^ N := by
        intro ht
        apply hsN
        rw [pow_succ']
        exact Ideal.mul_mem_mul hπm ht
      obtain ⟨k, u, huS, hum, rfl⟩ := ih t htS htN
      exact ⟨k + 1, u, huS, hum, by ring⟩
    · exact ⟨0, s, hs, hm, by simp⟩
end GlobalTheory
