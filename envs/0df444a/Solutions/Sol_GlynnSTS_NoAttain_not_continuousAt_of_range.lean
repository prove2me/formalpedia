-- Prove2me | solution 1 for GlynnSTS.NoAttain.not_continuousAt_of_range
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:39:29.006303+00:00
-- url     : https://prove2.me/submissions/11e7d62d-43a8-4b84-abb6-cb472f194dfc

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting

open GlynnSTS.NoAttain in
theorem solution (g : C(unitInterval, ℝ) → ℝ) (x : C(unitInterval, ℝ))
    (α : ℝ) (hα : 0 < α)
    (hrange : ∀ ε : ℝ, 0 < ε → ∀ σ : ℝ, 0 < σ → ∃ y, dist y x < ε ∧ g y = α * σ) :
    x ∈ GlynnSTS.Limit.D g := by
  intro hc
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hδ'⟩ := hc 1 one_pos
  have hσ : 0 < (|g x| + 2) / α := div_pos (by positivity) hα
  obtain ⟨y, hy, hgy⟩ := hrange δ hδ _ hσ
  have h1 := hδ' hy
  rw [hgy, mul_div_cancel₀ _ hα.ne', Real.dist_eq] at h1
  have h2 : |g x| + 2 - g x ≤ |(|g x| + 2 - g x)| := le_abs_self _
  have h3 : g x ≤ |g x| := le_abs_self _
  linarith
