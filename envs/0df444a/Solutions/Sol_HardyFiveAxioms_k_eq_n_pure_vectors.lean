-- Prove2me | solution 1 for HardyFiveAxioms.k_eq_n_pure_vectors
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:07:52.673871+00:00
-- url     : https://prove2.me/submissions/34c8710f-ee30-4812-ae06-921509848df0

import Mathlib

set_option autoImplicit false

theorem solution (N : ℕ) (p : Fin N → ℝ)
    (hsq : ∑ k, p k ^ 2 = 1) (hbd : ∀ k, 0 ≤ p k ∧ p k ≤ 1) (hnorm : ∑ k, p k = 1) :
    ∃ n : Fin N, p = Pi.single n 1 := by
  have h0 : ∀ k, p k * (1 - p k) = 0 := by
    have hs : ∑ k, p k * (1 - p k) = 0 := by
      have e : ∀ k, p k * (1 - p k) = p k - p k ^ 2 := fun k => by ring
      simp only [e, Finset.sum_sub_distrib, hnorm, hsq, sub_self]
    intro k
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (hbd i).1 (by linarith [(hbd i).2]))).1 hs k (Finset.mem_univ _)
  obtain ⟨n, hn⟩ : ∃ n, p n ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at hnorm
  have hn1 : p n = 1 := by
    rcases mul_eq_zero.1 (h0 n) with h | h
    · exact absurd h hn
    · linarith
  refine ⟨n, ?_⟩
  funext k
  by_cases hk : k = n
  · subst hk
    simp [hn1]
  · have hk0 : (Pi.single n 1 : Fin N → ℝ) k = 0 := by simp [Pi.single_apply, hk]
    rw [hk0]
    have hadd := Finset.add_sum_erase Finset.univ p (Finset.mem_univ n)
    rw [hnorm, hn1] at hadd
    have hz : ∑ x ∈ Finset.univ.erase n, p x = 0 := by linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => (hbd i).1)).1 hz k
      (Finset.mem_erase.2 ⟨hk, Finset.mem_univ _⟩)
