-- Prove2me | solution 1 for GlobalTheory.dvrSubring_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:54:18.329834+00:00
-- url     : https://prove2.me/submissions/9eac0f84-1367-4780-b332-3a888bde0d37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvrSubringEqTop
import Theorems.Thm_GlobalTheory_dvrSubring_factor

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
theorem _root_.solution (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (S : Subring V) (π : V) (hπS : π ∈ S) (hπ0 : π ≠ 0)
    (hπm : π ∈ IsLocalRing.maximalIdeal V)
    (hinv : ∀ s ∈ S, s ∉ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s * t = 1)
    (hdiv : ∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t)
    (hfrac : ∀ v : V, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ v * b = a) : S = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨a, haS, b, hbS, hb0, hvb⟩ := hfrac v
  by_cases ha0 : a = 0
  · subst ha0
    have : v = 0 := (mul_eq_zero.1 hvb).resolve_right hb0
    rw [this]; exact S.zero_mem
  obtain ⟨k, u, huS, hum, rfl⟩ := dvrSubring_factor S π hπm hdiv a haS ha0
  obtain ⟨l, u', hu'S, hu'm, rfl⟩ := dvrSubring_factor S π hπm hdiv b hbS hb0
  obtain ⟨t', ht'S, ht'⟩ := hinv u' hu'S hu'm
  have hπl : π ^ l ≠ 0 := pow_ne_zero _ hπ0
  by_cases hkl : l ≤ k
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
    have h1 : v * u' = π ^ d * u := by
      apply mul_left_cancel₀ hπl
      rw [pow_add] at hvb
      linear_combination hvb
    have h2 : v = π ^ d * u * t' := by
      linear_combination t' * h1 - v * ht'
    rw [h2]
    exact S.mul_mem (S.mul_mem (S.pow_mem hπS _) huS) ht'S
  · push_neg at hkl
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hkl
    subst hd
    have hπk : π ^ k ≠ 0 := pow_ne_zero _ hπ0
    have h1 : v * π ^ (d + 1) * u' = u := by
      apply mul_left_cancel₀ hπk
      rw [show k + d + 1 = k + (d + 1) by ring, pow_add] at hvb
      linear_combination hvb
    apply absurd _ hum
    rw [← h1, pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hπm))
end GlobalTheory
