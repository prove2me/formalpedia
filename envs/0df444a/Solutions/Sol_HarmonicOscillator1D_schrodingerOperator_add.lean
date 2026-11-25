-- Prove2me | solution 1 for HarmonicOscillator1D.schrodingerOperator_add
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T18:54:57.121929+00:00
-- url     : https://prove2.me/submissions/18cca26d-4ef0-4082-bb51-dd90c0c53138

import Mathlib
import Definitions.Def_HO1D_basic

open HarmonicOscillator1D HarmonicOscillator1D.HarmonicOscillator

theorem solution (Q : HarmonicOscillator) (ψ φ : ℝ → ℂ)
    (hψ : Differentiable ℝ ψ) (hψ' : Differentiable ℝ (deriv ψ))
    (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ)) :
    Q.schrodingerOperator (ψ + φ) = Q.schrodingerOperator ψ + Q.schrodingerOperator φ := by
  have h1 : deriv (ψ + φ) = deriv ψ + deriv φ := by
    funext y; exact deriv_add (hψ y) (hφ y)
  have h2 : deriv (deriv (ψ + φ)) = deriv (deriv ψ) + deriv (deriv φ) := by
    rw [h1]; funext y; exact deriv_add (hψ' y) (hφ' y)
  funext x
  simp only [HarmonicOscillator.schrodingerOperator, Pi.add_apply, h2]
  ring
