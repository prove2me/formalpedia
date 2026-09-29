-- Prove2me | solution 1 for InertialFB.IFB.lemma7_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:13:16.099336+00:00
-- url     : https://prove2.me/submissions/43661144-c747-4529-8c51-c549139f1d48

import Mathlib

open Filter

theorem solution (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (ω K : ℝ) (hω : ω < 1)
    (h : ∀ᶠ k in atTop, p (k + 1) - ω * p k ≤ K) :
    BddAbove (Set.range p) ∧ BddBelow (Set.range p) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  set c : ℝ := max ω 0 with hcdef
  have hc0 : (0:ℝ) ≤ c := le_max_right _ _
  have hc1 : c < 1 := max_lt hω one_pos
  have h1c : 0 < 1 - c := by linarith
  have hstep : ∀ k, N ≤ k → p (k + 1) ≤ c * p k + K := by
    intro k hk
    have h1 := hN k hk
    have h2 : ω * p k ≤ c * p k := mul_le_mul_of_nonneg_right (le_max_left _ _) (hp k)
    linarith
  set C : ℝ := max (p N) (K / (1 - c)) with hCdef
  have hKC : K ≤ (1 - c) * C := by
    have hle : K / (1 - c) ≤ C := le_max_right _ _
    rw [div_le_iff₀ h1c] at hle
    linarith
  have htail : ∀ k, N ≤ k → p k ≤ C := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_max_left _ _
    | succ n hn ih =>
      have h1 := hstep n hn
      have h2 : c * p n ≤ c * C := mul_le_mul_of_nonneg_left ih hc0
      linarith
  refine ⟨?_, ⟨0, ?_⟩⟩
  · obtain ⟨D, hD⟩ : ∃ D, ∀ k, k ≤ N → p k ≤ D := by
      refine ⟨(Finset.range (N + 1)).sup' ⟨N, by simp⟩ p, ?_⟩
      intro k hk
      exact Finset.le_sup' p (by simp [Nat.lt_succ_iff, hk])
    refine ⟨max C D, ?_⟩
    rintro x ⟨k, rfl⟩
    rcases le_or_gt k N with hk | hk
    · exact le_trans (hD k hk) (le_max_right _ _)
    · exact le_trans (htail k hk.le) (le_max_left _ _)
  · rintro x ⟨k, rfl⟩
    exact hp k
