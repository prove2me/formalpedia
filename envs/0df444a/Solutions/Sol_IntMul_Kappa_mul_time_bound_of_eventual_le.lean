-- Prove2me | solution 1 for IntMul.Kappa.mul_time_bound_of_eventual_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T19:17:22.020079+00:00
-- url     : https://prove2.me/submissions/55614996-9bd0-4306-be5f-68cb703946f1

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open IntMul

theorem solution
    {g h : ℕ → ℝ}
    (hgh : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n → g n ≤ h n)
    (hg : MulTimeBound g) : MulTimeBound h := by
  rcases hgh with ⟨N, hgh⟩
  rcases hg with ⟨M, hcorrect, c, hc, n₀, hcost⟩
  refine ⟨M, hcorrect, c, hc, max N n₀, ?_⟩
  intro n hn hn1 x y hx hy
  obtain ⟨t, ht, houtput⟩ :=
    hcost n (le_trans (le_max_right N n₀) hn) hn1 x y hx hy
  refine ⟨t, ?_, houtput⟩
  exact le_trans ht
    (mul_le_mul_of_nonneg_left
      (hgh n (le_trans (le_max_left N n₀) hn) hn1) hc.le)
