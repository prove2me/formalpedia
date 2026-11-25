-- Prove2me | solution 1 for HarmonicOscillator1D.schrodingerOperator_smul
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T18:55:01.347608+00:00
-- url     : https://prove2.me/submissions/f584156c-eaa0-48b6-9310-bf9f3df015b2

import Mathlib
import Definitions.Def_HO1D_basic

open HarmonicOscillator1D HarmonicOscillator1D.HarmonicOscillator

theorem solution (Q : HarmonicOscillator) (c : ℂ) (ψ : ℝ → ℂ)
    (hψ : Differentiable ℝ ψ) (hψ' : Differentiable ℝ (deriv ψ)) :
    Q.schrodingerOperator (c • ψ) = c • Q.schrodingerOperator ψ := by
  have h1 : deriv (c • ψ) = c • deriv ψ := by
    funext y; exact deriv_const_smul c (hψ y)
  have h2 : deriv (deriv (c • ψ)) = c • deriv (deriv ψ) := by
    rw [h1]; funext y; exact deriv_const_smul c (hψ' y)
  funext x
  simp only [HarmonicOscillator.schrodingerOperator, Pi.smul_apply, smul_eq_mul, h2]
  ring
