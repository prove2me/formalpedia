-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneGammaPhaseAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:31:12.732172+00:00
-- url     : https://prove2.me/submissions/09f10cee-eb28-47f9-85a6-83132fe9dec8

import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneGammaRecurrence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real Complex
set_option autoImplicit false

/-- Gamma recurrence and logarithmic phase combine into the stable Fourier phase. -/
theorem solution (alpha : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2) :
    (Complex.I / (alpha : ℂ)) *
        (((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
          Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-Complex.I))) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((Real.pi * alpha / 2 : ℝ) : ℂ))) := by
  have halphaR : (alpha : ℝ) ≠ 0 := by linarith
  have halpha : (alpha : ℂ) ≠ 0 := by exact_mod_cast halphaR
  have hg := Kyprianou.Ch01.stableAlphaAboveOneGammaRecurrence
    alpha h1 h2
  have hcoef :
      (Complex.I / (alpha : ℂ)) *
        (((Real.Gamma (1 - alpha) : ℝ) : ℂ)) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) * (-Complex.I) := by
    rw [hg]
    push_cast
    field_simp
  have he :
      (-Complex.I) *
        Complex.exp (((alpha - 1 : ℝ) : ℂ) *
          Complex.log (-Complex.I)) =
      Complex.exp ((alpha : ℂ) * Complex.log (-Complex.I)) := by
    calc
      (-Complex.I) *
          Complex.exp (((alpha - 1 : ℝ) : ℂ) *
            Complex.log (-Complex.I)) =
        Complex.exp (Complex.log (-Complex.I)) *
          Complex.exp (((alpha - 1 : ℝ) : ℂ) *
            Complex.log (-Complex.I)) := by
          rw [Complex.exp_log (by simp : (-Complex.I) ≠ 0)]
      _ = Complex.exp
          (Complex.log (-Complex.I) +
            (((alpha - 1 : ℝ) : ℂ) *
              Complex.log (-Complex.I))) := by
            rw [Complex.exp_add]
      _ = Complex.exp ((alpha : ℂ) *
          Complex.log (-Complex.I)) := by
            congr 1
            push_cast
            ring
  have hphase :
      Complex.exp ((alpha : ℂ) * Complex.log (-Complex.I)) =
      Complex.exp (-(Complex.I *
        ((Real.pi * alpha / 2 : ℝ) : ℂ))) := by
    rw [Complex.log_neg_I]
    congr 1
    push_cast
    ring
  calc
    (Complex.I / (alpha : ℂ)) *
        (((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
          Complex.exp (((alpha - 1 : ℝ) : ℂ) *
            Complex.log (-Complex.I))) =
      ((Complex.I / (alpha : ℂ)) *
        (((Real.Gamma (1 - alpha) : ℝ) : ℂ))) *
          Complex.exp (((alpha - 1 : ℝ) : ℂ) *
            Complex.log (-Complex.I)) := by ring
    _ = (((Real.Gamma (-alpha) : ℝ) : ℂ) * (-Complex.I)) *
          Complex.exp (((alpha - 1 : ℝ) : ℂ) *
            Complex.log (-Complex.I)) := by rw [hcoef]
    _ = ((Real.Gamma (-alpha) : ℝ) : ℂ) *
          ((-Complex.I) *
            Complex.exp (((alpha - 1 : ℝ) : ℂ) *
              Complex.log (-Complex.I))) := by ring
    _ = ((Real.Gamma (-alpha) : ℝ) : ℂ) *
          Complex.exp ((alpha : ℂ) *
            Complex.log (-Complex.I)) := by rw [he]
    _ = ((Real.Gamma (-alpha) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I *
            ((Real.pi * alpha / 2 : ℝ) : ℂ))) := by rw [hphase]
