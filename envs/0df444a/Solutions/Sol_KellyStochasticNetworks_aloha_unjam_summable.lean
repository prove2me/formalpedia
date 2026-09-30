-- Prove2me | solution 1 for KellyStochasticNetworks.aloha_unjam_summable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:18:55.869438+00:00
-- url     : https://prove2.me/submissions/2b6aac4a-31ae-48d3-96be-068a1e606b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

lemma ra_pow_pred (q f : ℝ) (hq : q ≠ 0) (n : ℕ) :
    (n:ℝ) * f * q ^ (n - 1) = f / q * ((n:ℝ) * q ^ n) := by
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [pow_succ]; field_simp

theorem ra_unjam (ν f : ℝ) (hν : 0 < ν) (hf : 0 < f) (hf1 : f < 1) :
    Summable (alohaUnjamProb ν f) := by
  set E := Real.exp (-ν) with hE
  set q := 1 - f with hq
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E < 1 := by
    have := Real.exp_lt_exp.mpr (show -ν < 0 by linarith); rwa [Real.exp_zero] at this
  have hq0 : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hnum : ∀ n : ℕ, 0 ≤ E * (1 + ν) * q ^ n + E * (n:ℝ) * f * q ^ (n - 1) :=
    fun n => by positivity
  have hden : ∀ n : ℕ, 1 - E ≤ 1 - E * (1 - q ^ n - (n:ℝ) * f * q ^ (n - 1)) := by
    intro n
    have : 0 ≤ q ^ n + (n:ℝ) * f * q ^ (n - 1) := by positivity
    nlinarith
  have hbound : ∀ n, alohaUnjamProb ν f n ≤
      (E * (1 + ν) * q ^ n + E * (n:ℝ) * f * q ^ (n - 1)) / (1 - E) := by
    intro n
    exact div_le_div_of_nonneg_left (hnum n) (by linarith) (hden n)
  have hnn : ∀ n, 0 ≤ alohaUnjamProb ν f n := by
    intro n
    exact div_nonneg (hnum n) (by linarith [hden n])
  refine Summable.of_nonneg_of_le hnn hbound ?_
  have hs1 : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0.le hq1
  have hs2 : Summable (fun n : ℕ => (n:ℝ) * q ^ n) := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
      (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
    simpa using this
  have hs : Summable (fun n : ℕ => E * (1 + ν) * q ^ n + E * (n:ℝ) * f * q ^ (n - 1)) := by
    refine ((hs1.mul_left (E * (1 + ν))).add (hs2.mul_left (E * (f / q)))).congr (fun n => ?_)
    have := ra_pow_pred q f hq0.ne' n
    rw [show E * (n:ℝ) * f * q ^ (n - 1) = E * ((n:ℝ) * f * q ^ (n - 1)) by ring, this]; ring
  exact hs.div_const (1 - E)

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution (ν f : ℝ) (hν : 0 < ν) (hf : 0 < f) (hf1 : f < 1) :
    Summable (alohaUnjamProb ν f) := by
  exact ra_unjam ν f hν hf hf1
