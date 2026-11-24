-- Prove2me | solution 1 for GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:51.524831+00:00
-- url     : https://prove2.me/submissions/48bf9760-6905-4da0-bdd4-46453e935dbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubDvdChoosePrimePowOfLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (l a c i : ℕ), l.Prime → 1 ≤ i → i < l ^ (c + 1) → l ^ (a - c) ∣ (l ^ a).choose i := by
  intro l a c i hl hi hlt
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : i ≠ 0) l hl.one_lt.ne'
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have hv : v ≤ c := by
    have h1 : l ^ v ≤ l ^ v * m := Nat.le_mul_of_pos_right _ hm0
    have h2 : l ^ v < l ^ (c + 1) := lt_of_le_of_lt h1 hlt
    have := (Nat.pow_lt_pow_iff_right hl.one_lt).1 h2
    omega
  have hpos : 0 < l ^ a := pow_pos hl.pos a
  have key : l ^ a ∣ l ^ v * m * (l ^ a).choose (l ^ v * m) := by
    obtain ⟨n, hn⟩ : ∃ n, l ^ a = n + 1 := ⟨l ^ a - 1, by omega⟩
    obtain ⟨k, hk⟩ : ∃ k, l ^ v * m = k + 1 := ⟨l ^ v * m - 1, by omega⟩
    rw [hn, hk]
    refine ⟨n.choose k, ?_⟩
    rw [mul_comm]
    exact (Nat.add_one_mul_choose_eq n k).symm
  have h2 : l ^ (a - v) ∣ m * (l ^ a).choose (l ^ v * m) := by
    rcases le_or_gt v a with h | h
    · have key' : l ^ v * l ^ (a - v) ∣ l ^ v * (m * (l ^ a).choose (l ^ v * m)) := by
        rw [← pow_add, Nat.add_sub_of_le h, ← mul_assoc]
        exact key
      exact (Nat.mul_dvd_mul_iff_left (pow_pos hl.pos v)).1 key'
    · rw [show a - v = 0 by omega, pow_zero]
      exact one_dvd _
  have hcop : (l ^ (a - v)).Coprime m := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hm)
  have h3 : l ^ (a - v) ∣ (l ^ a).choose (l ^ v * m) := hcop.dvd_of_dvd_mul_left h2
  exact (pow_dvd_pow l (by omega : a - c ≤ a - v)).trans h3
end GlobalTheory
