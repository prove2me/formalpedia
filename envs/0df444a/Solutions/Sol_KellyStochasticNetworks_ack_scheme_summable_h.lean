-- Prove2me | solution 1 for KellyStochasticNetworks.ack_scheme_summable_h
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:18:56.846842+00:00
-- url     : https://prove2.me/submissions/eb7e44b6-fdf2-48f3-8aec-210b671b6016

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

lemma ra_rate_nonneg (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x) (t : ℕ) : 0 ≤ ackAttemptRate h t :=
  Finset.sum_nonneg fun r _ => hh r

theorem ra_summable_h (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x) (hsum : Summable h)
    (ν : ℝ) (hν : 0 < ν) : ¬ Summable (fun t : ℕ => ackSlotProb h ν (t + 1)) := by
  intro hs
  set H := ∑' r, h r with hH
  have hle : ∀ t, ackAttemptRate h t ≤ H := fun t =>
    hsum.sum_le_tsum _ (fun i _ => hh i)
  have hlow : ∀ t, Real.exp (-(ν * H)) ≤ ackSlotProb h ν t := by
    intro t
    have ha := ra_rate_nonneg h hh t
    unfold ackSlotProb
    have h1 : Real.exp (-(ν * H)) ≤ Real.exp (-(ν * ackAttemptRate h t)) :=
      Real.exp_le_exp.mpr (by nlinarith [hle t])
    have h2 : 0 ≤ ν * ackAttemptRate h t := mul_nonneg hν.le ha
    have h3 := Real.exp_pos (-(ν * ackAttemptRate h t))
    nlinarith
  have hpos := Real.exp_pos (-(ν * H))
  obtain ⟨t, ht⟩ := (hs.tendsto_atTop_zero.eventually (gt_mem_nhds hpos)).exists
  linarith [hlow (t + 1)]

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x) (hsum : Summable h)
    (ν : ℝ) (hν : 0 < ν) : ¬ Summable (fun t : ℕ => ackSlotProb h ν (t + 1)) := by
  exact ra_summable_h h hh hsum ν hν
