-- Prove2me | solution 1 for Kyprianou.Ch01.expNegBarrierBoundForcesUnity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:22:53.455219+00:00
-- url     : https://prove2.me/submissions/dbd3546f-07ff-416e-9f1d-97f319630deb

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
set_option autoImplicit false

/-- Arbitrarily small positive barriers force the Laplace lower bound to one. -/
theorem solution (c z : ℝ) (hc : 0 ≤ c)
    (h : ∀ a : ℝ, 0 < a → Real.exp (-a * c) ≤ z) :
    1 ≤ z := by
  by_contra hnot
  have hz : z < 1 := lt_of_not_ge hnot
  have hc1 : 0 < c + 1 := by linarith
  let a : ℝ := (1 - z) / (c + 1)
  have ha : 0 < a := div_pos (by linarith) hc1
  have hrel : a * (c + 1) = 1 - z := by
    dsimp [a]
    field_simp
  have hsmall : a * c < 1 - z := by
    nlinarith [ha, hrel]
  have hexp : 1 - a * c ≤ Real.exp (-a * c) := by
    nlinarith [Real.add_one_le_exp (-a * c)]
  have hb := h a ha
  linarith
