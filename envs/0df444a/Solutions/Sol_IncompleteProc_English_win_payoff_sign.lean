-- Prove2me | solution 1 for IncompleteProc.English.win_payoff_sign
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:56:19.737991+00:00
-- url     : https://prove2.me/submissions/a12cadd0-6af5-477e-a3f5-7dbc0d9f3ba7

import Mathlib
import Definitions.Def_IncompleteProc_English_Model
import Definitions.Def_IncompleteProc_English_Auction

open MeasureTheory

open IncompleteProc.English in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) :
    ∀ c ∈ Set.Icc E.clo E.chi, ∀ x ∈ Set.Icc E.clo E.chi,
      (c ≤ x → 0 ≤ E.winPayoff c x) ∧ (x < c → E.winPayoff c x < 0) := by
  obtain ⟨_, hQ, _, _, _, _, _, _, _, hmono, _⟩ := hS
  intro c hc x hx
  constructor
  · intro hcx
    unfold Env.winPayoff
    have : 0 ≤ ∫ ω, E.Q * max 0 (E.offer ω x - E.k c ω) ∂E.G :=
      integral_nonneg (fun ω => mul_nonneg hQ.le (le_max_left _ _))
    linarith
  · intro hxc
    unfold Env.winPayoff
    have hz : (fun ω => E.Q * max 0 (E.offer ω x - E.k c ω)) = fun _ => (0 : ℝ) := by
      funext ω
      have h1 : E.offer ω x ≤ E.k x ω := min_le_left _ _
      have h2 : E.k x ω < E.k c ω := hmono ω hx hc hxc
      rw [max_eq_left (by linarith)]
      ring
    rw [hz, integral_zero]
    linarith
