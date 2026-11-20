-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaComplexDeficitValueStrictLeft
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:17:09.115697+00:00
-- url     : https://prove2.me/submissions/ef78ca31-c216-41d1-bfbd-5e9d2cecaa5d

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftMellinIntegral
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftIntegrationByParts
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneGammaRecurrence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re < 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) * Complex.log (-w)) := by
  have hα : (alpha : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt h0)
  have hw0 : (-w) ≠ 0 := neg_ne_zero.mpr hw
  have hp :
      Complex.exp ((alpha : ℂ) * Complex.log (-w)) =
        (-w) * Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-w)) := by
    have he :
        (alpha : ℂ) * Complex.log (-w) =
          Complex.log (-w) +
            (((alpha - 1 : ℝ) : ℂ) * Complex.log (-w)) := by
      push_cast
      ring
    rw [he, Complex.exp_add, Complex.exp_log hw0]
  have hm := Kyprianou.Ch01.stableGammaStrictLeftMellinIntegral
    alpha h0 h1 w hwre
  have hi := Kyprianou.Ch01.stableGammaStrictLeftIntegrationByParts
    alpha h0 h1 w hwre
  have hg := Kyprianou.Ch01.stableAlphaBelowOneGammaRecurrence alpha h0 h1
  calc
    _ = (w / (alpha : ℂ)) *
      (∫ r in Set.Ioi (0 : ℝ),
        Complex.exp (w * (r : ℂ)) *
          ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) := hi
    _ = (w / (alpha : ℂ)) *
      (((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
        Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-w))) := by rw [hm]
    _ = ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        ((-w) * Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-w))) := by
      rw [hg]
      push_cast
      field_simp [hα]
    _ = _ := by rw [hp]
