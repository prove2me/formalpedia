-- Prove2me | solution 1 for MarketplaceSharing.Threshold.share_optimal_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:15:08.97557+00:00
-- url     : https://prove2.me/submissions/1a7a9408-1342-472c-9d1c-99917a2c92fb

import Mathlib
import Definitions.Def_MarketplaceSharing_Threshold_Model

open MarketplaceSharing.Threshold in
theorem solution (p : Params) (V : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) :
    p.IsOptimalDecision V n t true ↔ marginal V n t ≤ p.platformMargin := by
  have key : ∀ Δ v : ℝ, p.hamiltonian true Δ v - p.hamiltonian false Δ v =
      p.lamP * ((1 - p.θ) * p.price - Δ) := by
    intro Δ v
    simp only [Params.hamiltonian, if_true, Bool.false_eq_true, if_false]
    ring
  have hl := p.lamP_pos
  have k := key (marginal V n t) (V n t)
  unfold Params.IsOptimalDecision Params.platformMargin
  constructor
  · intro h
    have h0 := h false
    by_contra hc
    push_neg at hc
    have : 0 < p.lamP * (marginal V n t - (1 - p.θ) * p.price) := mul_pos hl (by linarith)
    linarith
  · intro h z'
    cases z'
    · have : 0 ≤ p.lamP * ((1 - p.θ) * p.price - marginal V n t) :=
        mul_nonneg hl.le (by linarith)
      linarith
    · exact le_refl _
