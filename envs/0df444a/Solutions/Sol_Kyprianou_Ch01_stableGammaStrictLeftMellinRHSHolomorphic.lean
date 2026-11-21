-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftMellinRHSHolomorphic
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T14:23:17.555174+00:00
-- url     : https://prove2.me/submissions/671784ac-63e7-4988-a629-aa0320d821fb

import Mathlib
open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem solution (alpha : ℝ) :
    DifferentiableOn ℂ
      (fun w : ℂ => ((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
        Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-w)))
      {w : ℂ | w.re < 0} := by
  intro w hw
  have hmem : -w ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simpa using hw
  have hlog : DifferentiableAt ℂ (fun w : ℂ => Complex.log (-w)) w := by
    simpa [Function.comp_def] using
      (Complex.differentiableAt_log hmem).comp w
        ((differentiable_neg (𝕜 := ℂ)).differentiableAt (x := w))
  have hlin : DifferentiableAt ℂ
      (fun w : ℂ => ((alpha - 1 : ℝ) : ℂ) * Complex.log (-w)) w :=
    (differentiableAt_const (((alpha - 1 : ℝ) : ℂ))).mul hlog
  exact ((differentiableAt_const (((Real.Gamma (1 - alpha) : ℝ) : ℂ))).mul hlin.cexp).differentiableWithinAt
