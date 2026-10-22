-- Prove2me | solution 1 for HumanMachine.Alone.pbar_slope_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:36:55.588465+00:00
-- url     : https://prove2.me/submissions/8f6273b5-e3ec-4d21-86c2-fd9c4e3747e7

import Mathlib
import Definitions.Def_HumanMachine_Alone_model
set_option autoImplicit false

theorem solution :
    (∀ lam : ℝ, 0 < lam →
      let slope := 1 / (1 - Real.exp (-(1 / lam))) +
        1 / (Real.exp (1 / lam) - 1)
      0 < slope ∧ ∀ mu : ℝ, HumanMachine.Alone.pBar lam mu = slope * mu -
        1 / (Real.exp (1 / lam) - 1)) ∧
    (∀ lam : ℝ, 0 < lam →
      HasDerivAt HumanMachine.Alone.muHigh
        (-(1 / lam ^ 2) * Real.exp (1 / lam) / (Real.exp (1 / lam) + 1) ^ 2) lam ∧
      HasDerivAt HumanMachine.Alone.muLow
        ((1 / lam ^ 2) * Real.exp (1 / lam) / (Real.exp (1 / lam) + 1) ^ 2) lam) := by
  constructor
  · intro lam hlam
    have ha : 0 < 1 / lam := by positivity
    have hE : 1 < Real.exp (1 / lam) := by
      have := Real.add_one_lt_exp (ne_of_gt ha)
      linarith
    have hF : Real.exp (-(1 / lam)) < 1 := by
      have h := Real.exp_lt_exp.mpr (show -(1 / lam) < 0 by linarith)
      simpa using h
    dsimp only
    refine ⟨?_, ?_⟩
    · have h1 : 0 < 1 - Real.exp (-(1 / lam)) := by linarith
      have h2 : 0 < Real.exp (1 / lam) - 1 := by linarith
      positivity
    · intro mu
      unfold HumanMachine.Alone.pBar
      ring
  · intro lam hlam
    have hne : lam ≠ 0 := ne_of_gt hlam
    have h1 : HasDerivAt (fun x : ℝ => 1 / x) (-(1 / lam ^ 2)) lam := by
      have := hasDerivAt_inv hne
      simpa [one_div] using this
    have h2 := h1.exp
    have hpos : 0 < Real.exp (1 / lam) + 1 := by positivity
    have h3 := h2.add_const 1
    constructor
    · have h4 := h2.div h3 (ne_of_gt hpos)
      have h5 : HasDerivAt (fun x : ℝ => Real.exp (1 / x) / (Real.exp (1 / x) + 1))
          (-(1 / lam ^ 2) * Real.exp (1 / lam) / (Real.exp (1 / lam) + 1) ^ 2) lam := by
        refine h4.congr_deriv ?_
        field_simp
        ring
      exact h5
    · have h4 := (hasDerivAt_const lam (1 : ℝ)).div h3 (ne_of_gt hpos)
      have h5 : HasDerivAt (fun x : ℝ => 1 / (Real.exp (1 / x) + 1))
          ((1 / lam ^ 2) * Real.exp (1 / lam) / (Real.exp (1 / lam) + 1) ^ 2) lam := by
        refine h4.congr_deriv ?_
        field_simp
        ring
      exact h5
