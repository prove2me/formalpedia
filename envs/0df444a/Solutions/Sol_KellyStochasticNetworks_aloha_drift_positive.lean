-- Prove2me | solution 1 for KellyStochasticNetworks.aloha_drift_positive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:18:56.368855+00:00
-- url     : https://prove2.me/submissions/fcc11e5d-35c6-4bc7-b5e7-55c87f85c1b4

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

lemma ra_pow_pred (q f : ℝ) (hq : q ≠ 0) (n : ℕ) :
    (n:ℝ) * f * q ^ (n - 1) = f / q * ((n:ℝ) * q ^ n) := by
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [pow_succ]; field_simp

theorem ra_drift (ν f : ℝ) (hν : 0 < ν) (hf : 0 < f) (hf1 : f < 1) :
    (∀ n : ℕ, 1 ≤ n → alohaSuccessProb ν f n
        = Real.exp (-ν) * ((n : ℝ) * f + (1 - f) * ν) * (1 - f) ^ (n - 1))
      ∧ Filter.Tendsto (fun n : ℕ => alohaSuccessProb ν f n) Filter.atTop (nhds 0)
      ∧ ∃ N : ℕ, ∀ n ≥ N, alohaSuccessProb ν f n < ν := by
  have hq0 : 0 < 1 - f := by linarith
  have hq1 : 1 - f < 1 := by linarith
  have h1 : ∀ n : ℕ, 1 ≤ n → alohaSuccessProb ν f n
      = Real.exp (-ν) * ((n : ℝ) * f + (1 - f) * ν) * (1 - f) ^ (n - 1) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [alohaSuccessProb, Nat.add_sub_cancel, pow_succ]
    ring
  have h2 : Filter.Tendsto (fun n : ℕ => alohaSuccessProb ν f n) Filter.atTop (nhds 0) := by
    have ha := (tendsto_self_mul_const_pow_of_abs_lt_one (r := 1 - f)
      (by rw [abs_of_pos hq0]; exact hq1)).const_mul (Real.exp (-ν) * (f / (1 - f)))
    have hb := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul (ν * Real.exp (-ν))
    have := ha.add hb
    simp only [mul_zero, add_zero] at this
    refine this.congr (fun n => ?_)
    simp only [alohaSuccessProb]
    rw [ra_pow_pred (1 - f) f hq0.ne' n]; ring
  refine ⟨h1, h2, ?_⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h2.eventually (gt_mem_nhds hν))
  exact ⟨N, hN⟩

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution (ν f : ℝ) (hν : 0 < ν) (hf : 0 < f) (hf1 : f < 1) :
    (∀ n : ℕ, 1 ≤ n → alohaSuccessProb ν f n
        = Real.exp (-ν) * ((n : ℝ) * f + (1 - f) * ν) * (1 - f) ^ (n - 1))
      ∧ Filter.Tendsto (fun n : ℕ => alohaSuccessProb ν f n) Filter.atTop (nhds 0)
      ∧ ∃ N : ℕ, ∀ n ≥ N, alohaSuccessProb ν f n < ν := by
  exact ra_drift ν f hν hf hf1
