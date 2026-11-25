-- Prove2me | solution 1 for HarmonicOscillator1D.schrodingerOperator_eq_xi
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T18:54:53.503797+00:00
-- url     : https://prove2.me/submissions/3d836581-7690-4505-b625-2052f7e34191

import Mathlib
import Definitions.Def_HO1D_basic

open HarmonicOscillator1D HarmonicOscillator1D.HarmonicOscillator

theorem solution (Q : HarmonicOscillator) (ψ : ℝ → ℂ) :
    Q.schrodingerOperator ψ =
      fun x => (Q.ℏ ^ 2 / (2 * Q.m)) * (- (deriv (deriv ψ) x) + (1 / Q.ξ ^ 2) ^ 2 * x ^ 2 * ψ x) := by
  have hξ : Q.ξ ^ 2 = Q.ℏ / (Q.m * Q.ω) := by
    unfold HarmonicOscillator.ξ
    exact Real.sq_sqrt (div_pos Q.hℏ (mul_pos Q.hm Q.hω)).le
  have hξc : ((Q.ξ : ℂ)) ^ 2 = (Q.ℏ : ℂ) / ((Q.m : ℂ) * (Q.ω : ℂ)) := by
    exact_mod_cast hξ
  funext x
  simp only [HarmonicOscillator.schrodingerOperator]
  have hm : (Q.m : ℂ) ≠ 0 := by exact_mod_cast Q.m_ne_zero
  have hω : (Q.ω : ℂ) ≠ 0 := by exact_mod_cast Q.ω_ne_zero
  have hℏ : (Q.ℏ : ℂ) ≠ 0 := by exact_mod_cast Q.ℏ_ne_zero
  rw [hξc]
  field_simp
