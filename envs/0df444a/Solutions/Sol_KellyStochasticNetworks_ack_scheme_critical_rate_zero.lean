-- Prove2me | solution 1 for KellyStochasticNetworks.ack_scheme_critical_rate_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:18:57.360864+00:00
-- url     : https://prove2.me/submissions/06910d0f-c844-4539-af7e-1baad8aa61fd

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

lemma ra_rate_nonneg (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x) (t : ℕ) : 0 ≤ ackAttemptRate h t :=
  Finset.sum_nonneg fun r _ => hh r

theorem ra_goal (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x)
    (hgrow : Filter.Tendsto (fun t : ℕ => ackAttemptRate h t / Real.log t)
        Filter.atTop Filter.atTop)
    (ν : ℝ) (hν : 0 < ν) :
    Summable (fun t : ℕ => ackSlotProb h ν (t + 1)) := by
  have hg' := (Filter.tendsto_add_atTop_iff_nat 1).mpr hgrow
  have hsg : Summable (fun t : ℕ => 2 * (1 / ((t:ℝ) + 1) ^ 2)) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine (this.mul_left 2).congr (fun t => ?_)
    push_cast; ring
  refine Summable.of_norm_bounded_eventually_nat hsg ?_
  filter_upwards [hg'.eventually_ge_atTop (4 / ν), Filter.eventually_ge_atTop 1] with t ht ht1
  have hT : (2:ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by
    have : (1:ℝ) ≤ t := by exact_mod_cast ht1
    push_cast; linarith
  set T : ℝ := ((t + 1 : ℕ) : ℝ) with hTdef
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  set a := ackAttemptRate h (t + 1) with ha
  have ha0 : 0 ≤ a := ra_rate_nonneg h hh (t + 1)
  have hya : 4 * Real.log T ≤ ν * a := by
    have := (le_div_iff₀ hL).mp ht
    have e : ν * (4 / ν * Real.log T) = 4 * Real.log T := by field_simp
    nlinarith
  set y := ν * a with hy
  have hy0 : 0 ≤ y := mul_nonneg hν.le ha0
  have hP : ackSlotProb h ν (t + 1) = (1 + y) * Real.exp (-y) := rfl
  have hP0 : 0 ≤ (1 + y) * Real.exp (-y) := by positivity
  rw [Real.norm_eq_abs, hP, abs_of_nonneg hP0]
  -- (1+y) e^{-y} ≤ 2 e^{-y/2}
  have hb1 : (1 + y) * Real.exp (-y) ≤ 2 * Real.exp (-(y / 2)) := by
    have he := Real.add_one_le_exp (y / 2)
    have e : Real.exp (-(y / 2)) = Real.exp (y / 2) * Real.exp (-y) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have := Real.exp_pos (-y)
    nlinarith
  have hb2 : Real.exp (-(y / 2)) ≤ Real.exp (-(2 * Real.log T)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hb3 : Real.exp (-(2 * Real.log T)) = 1 / ((t:ℝ) + 1) ^ 2 := by
    rw [Real.exp_neg, show 2 * Real.log T = Real.log T + Real.log T by ring, Real.exp_add,
      Real.exp_log hT0, hTdef]
    push_cast; ring
  linarith

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x)
    (hgrow : Filter.Tendsto (fun t : ℕ => ackAttemptRate h t / Real.log t)
        Filter.atTop Filter.atTop)
    (ν : ℝ) (hν : 0 < ν) :
    Summable (fun t : ℕ => ackSlotProb h ν (t + 1)) := by
  exact ra_goal h hh hgrow ν hν
