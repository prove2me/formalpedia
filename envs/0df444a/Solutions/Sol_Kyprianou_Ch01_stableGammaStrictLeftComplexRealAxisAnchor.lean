-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftComplexRealAxisAnchor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:37:26.889054+00:00
-- url     : https://prove2.me/submissions/d77ed7e5-5383-485f-a3ce-dbf9858d3acc

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftRealMellinAnchor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set
set_option autoImplicit false

/-- Source-exact complex Mellin identity at each negative-real Laplace rate. -/
theorem solution
    (alpha u : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (hu : 0 < u) :
    (∫ r in Set.Ioi (0 : ℝ),
      Complex.exp (-(u : ℂ) * (r : ℂ)) *
        ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) =
      (((((1 / u) ^ (1 - alpha)) * Real.Gamma (1 - alpha) : ℝ)) : ℂ)
    := by
  have heq (r : ℝ) :
      Complex.exp (-(u : ℂ) * (r : ℂ)) *
        ((r ^ (-alpha) : ℝ) : ℂ) =
      (((Real.exp (-(u * r)) * r ^ (-alpha) : ℝ)) : ℂ) := by
    have he : -(u : ℂ) * (r : ℂ) = ((-(u * r) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, ← Complex.ofReal_exp]
    push_cast
    ring
  calc
    _ = (∫ r in Set.Ioi (0 : ℝ),
      (((Real.exp (-(u * r)) * r ^ (-alpha) : ℝ)) : ℂ)
        ∂volume) := by
        exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => heq r)
    _ = ((∫ r in Set.Ioi (0 : ℝ),
      Real.exp (-(u * r)) * r ^ (-alpha) ∂volume : ℝ) : ℂ) := by
        exact integral_complex_ofReal
    _ = _ := congrArg (fun z : ℝ => (z : ℂ))
      (Kyprianou.Ch01.stableGammaStrictLeftRealMellinAnchor
        alpha u h0 h1 hu)
