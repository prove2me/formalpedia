-- Prove2me | solution 1 for HarmonicOscillator1D.schrodingerOperator_parity
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T18:55:05.040743+00:00
-- url     : https://prove2.me/submissions/9724e7fd-232a-4e20-b2de-b9c32c1d139c

import Mathlib
import Definitions.Def_HO1D_basic

open HarmonicOscillator1D HarmonicOscillator1D.HarmonicOscillator

theorem solution (Q : HarmonicOscillator) (ψ : ℝ → ℂ) :
    Q.schrodingerOperator (parityOperator ψ) = parityOperator (Q.schrodingerOperator ψ) := by
  have h1 : deriv (parityOperator ψ) = fun x => -deriv ψ (-x) := by
    funext y; exact deriv_comp_neg ψ y
  have h2 : deriv (deriv (parityOperator ψ)) = fun x => deriv (deriv ψ) (-x) := by
    rw [h1]; funext y
    rw [deriv.fun_neg, deriv_comp_neg (deriv ψ) y, neg_neg]
  funext x
  simp only [HarmonicOscillator.schrodingerOperator, parityOperator, h2]
  push_cast
  ring
