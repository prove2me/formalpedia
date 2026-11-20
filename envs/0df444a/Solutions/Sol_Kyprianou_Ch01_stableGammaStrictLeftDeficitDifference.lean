-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftDeficitDifference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:32:07.359172+00:00
-- url     : https://prove2.me/submissions/b0618fc8-cfc1-4b12-abfd-258488d01277

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueStrictLeft
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (u v : ℂ) (hu : u.re < 0) (hv : v.re < 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (u * (r : ℂ)) -
        Complex.exp (v * (r : ℂ))) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        (Complex.exp ((alpha : ℂ) * Complex.log (-u)) -
          Complex.exp ((alpha : ℂ) * Complex.log (-v))) := by
  have hune : u ≠ 0 := by
    intro hz
    have hzero : u.re = 0 := by rw [hz]; rfl
    linarith
  have hvne : v ≠ 0 := by
    intro hz
    have hzero : v.re = 0 := by rw [hz]; rfl
    linarith
  have hU :=
    Kyprianou.Ch01.stableGammaComplexDeficitIntegrable
      alpha h0 h1 u hune (le_of_lt hu)
  have hV :=
    Kyprianou.Ch01.stableGammaComplexDeficitIntegrable
      alpha h0 h1 v hvne (le_of_lt hv)
  have hUV (r : ℝ) :
      (Complex.exp (u * (r : ℂ)) - Complex.exp (v * (r : ℂ))) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) =
      (Complex.exp (u * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) -
      (Complex.exp (v * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) := by ring
  simp_rw [hUV]
  rw [integral_sub hU hV,
    Kyprianou.Ch01.stableGammaComplexDeficitValueStrictLeft
      alpha h0 h1 u hune hu,
    Kyprianou.Ch01.stableGammaComplexDeficitValueStrictLeft
      alpha h0 h1 v hvne hv]
  ring
