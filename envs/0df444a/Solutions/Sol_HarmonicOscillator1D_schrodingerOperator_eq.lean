-- Prove2me | solution 1 for HarmonicOscillator1D.schrodingerOperator_eq
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T18:54:50.545355+00:00
-- url     : https://prove2.me/submissions/79815be0-54d9-4f87-ac40-9918d71b9544

import Mathlib
import Definitions.Def_HO1D_basic

open HarmonicOscillator1D HarmonicOscillator1D.HarmonicOscillator

theorem solution (Q : HarmonicOscillator) (ψ : ℝ → ℂ) :
    Q.schrodingerOperator ψ = (- Q.ℏ ^ 2 / (2 * Q.m)) • (deriv (deriv ψ)) +
      (1/2 * Q.m * Q.ω^2) • ((fun x => Complex.ofReal x ^ 2) * ψ) := by
  funext x
  simp only [HarmonicOscillator.schrodingerOperator, Pi.add_apply, Pi.smul_apply, Pi.mul_apply,
    Complex.real_smul]
  push_cast
  ring
