-- Prove2me | solution 1 for Gilbreath.prime_gap_finite_criterion_conditions
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T00:47:26.260998+00:00
-- url     : https://prove2.me/submissions/2ce43d36-64c3-47d2-b737-950ebe453161
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_gilbreath_triangle
import Theorems.Thm_Gilbreath_prime_gap_positive_normalization
import Theorems.Thm_Gilbreath_halved_prime_gap_conditions

theorem solution :
    ∃ b : ℕ → ℕ,
      (∀ n, Gilbreath.d 1 (n + 1) = 2 * b n) ∧
      ∃ N₀ : ℕ,
        (∀ N, 1 ≤ N → N ≤ N₀ →
          Gilbreath.iterAbsDiff b (N - 1) 0 = 0 ∨
          Gilbreath.iterAbsDiff b (N - 1) 0 = 1) ∧
        (∀ N, N₀ < N →
          ∃ N' M L : ℕ, ∃ R : ℕ → ℕ,
            (1 ≤ N' ∧ N' ≤ N ∧ 1 ≤ M ∧ 1 ≤ L ∧
              1 < R 0 ∧
              (∀ m, m < M → R m < R (m + 1)) ∧
              2 * R M + N' < N ∧
              (∀ m, 1 ≤ m → m ≤ M → 4 * R (m - 1) ≤ R m) ∧
              100 * L * 8 ^ M ≤ R 0) ∧
            (∀ j < N, b j ≤ 2 ^ M) ∧
            (¬ ∃ i j : ℕ,
              i + L ≤ N ∧ j + i + L ≤ N ∧
              ∀ t < L, Gilbreath.iterAbsDiff b i (j + t) = 0) ∧
            (¬ ∃ m d' i k j : ℕ,
              1 ≤ m ∧ m ≤ M ∧
              2 ^ (M - m) < d' ∧ d' ≤ 2 ^ (M - m + 1) ∧
              i ≤ 2 * R (m - 1) ∧
              R m ≤ k + 3 * R (m - 1) ∧
              N' ≤ j + 1 ∧ j + i + k + 1 ≤ N ∧
              ∀ t < k, Gilbreath.iterAbsDiff b i (j + t) = 0 ∨
                Gilbreath.iterAbsDiff b i (j + t) = d')) := by
  obtain ⟨b, hb, -⟩ := Gilbreath.prime_gap_positive_normalization
  exact ⟨b, hb.1, Gilbreath.halved_prime_gap_conditions b hb.1⟩
