-- Prove2me | solution 1 for GreshamLaw.newton_guinea_arbitrage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T19:30:07.866539+00:00
-- url     : https://prove2.me/submissions/b57ffa59-d62e-4672-be67-acd33e09d18a

import Mathlib
import Definitions.Def_GreshamLaw_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open GreshamLaw

theorem solution (r m N : ℝ) (hm : 0 < m) (hmr : m < r) (hN : 0 < N) :
    N < arbitrageRound r m N ∧
      Filter.Tendsto (fun n : ℕ => (arbitrageRound r m)^[n] N)
        Filter.atTop Filter.atTop := by
  have hratio : (1 : ℝ) < r / m := (one_lt_div hm).2 hmr
  have hiter : ∀ n : ℕ,
      (arbitrageRound r m)^[n] N = (r / m)^n * N := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      change ((r / m)^n * N) / m * r = (r / m)^(n + 1) * N
      rw [pow_succ]
      field_simp [ne_of_gt hm] <;> ring
  constructor
  · have hineq := mul_lt_mul_of_pos_right hratio hN
    have heq : arbitrageRound r m N = (r / m) * N := by
      unfold arbitrageRound
      ring
    simpa [heq] using hineq
  · have hp := tendsto_pow_atTop_atTop_of_one_lt hratio
    have hdiv : Filter.Tendsto (fun n : ℕ => (r / m)^n * N)
        Filter.atTop Filter.atTop := hp.atTop_mul_const hN
    exact hdiv.congr' (Filter.Eventually.of_forall (fun n => (hiter n).symm))
