-- Prove2me | solution 1 for KellyStochasticNetworks.ack_slot_prob_antitone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:18:55.310755+00:00
-- url     : https://prove2.me/submissions/43a9dc0d-9d19-4615-8e62-e14ce38f4ae6

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

lemma ra_slot_mono {y₁ y₂ : ℝ} (h0 : 0 ≤ y₁) (h12 : y₁ ≤ y₂) :
    (1 + y₂) * Real.exp (-y₂) ≤ (1 + y₁) * Real.exp (-y₁) := by
  have hd := Real.add_one_le_exp (y₂ - y₁)
  have e : Real.exp (-y₁) = Real.exp (y₂ - y₁) * Real.exp (-y₂) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hpos := Real.exp_pos (-y₂)
  have : 1 + y₂ ≤ (1 + y₁) * Real.exp (y₂ - y₁) := by nlinarith
  nlinarith

lemma ra_rate_nonneg (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x) (t : ℕ) : 0 ≤ ackAttemptRate h t :=
  Finset.sum_nonneg fun r _ => hh r

theorem ra_antitone (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x) (t : ℕ) :
    AntitoneOn (fun ν : ℝ => ackSlotProb h ν t) (Set.Ici 0) := by
  intro ν₁ h₁ ν₂ h₂ hle
  have ha := ra_rate_nonneg h hh t
  exact ra_slot_mono (mul_nonneg h₁ ha) (mul_le_mul_of_nonneg_right hle ha)

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x) (t : ℕ) :
    AntitoneOn (fun ν : ℝ => ackSlotProb h ν t) (Set.Ici 0) := by
  exact ra_antitone h hh t
