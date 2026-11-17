-- Prove2me | solution 1 for Kyprianou.Ch01.geometricCharFun_closedForm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:53:22.362099+00:00
-- url     : https://prove2.me/submissions/2dcc8d93-786c-4b35-b31c-82bc1226a127

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_discreteLawCharFun_asPGF
import Theorems.Thm_Kyprianou_Ch01_geometricMeasure_complexPGF
import Theorems.Thm_Kyprianou_Ch01_geometricFourierConvergence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem solution (p : unitInterval.Elem) (hp : p ≠ 0) (xi : ℝ) :
    charFun
      ((ProbabilityTheory.geometricMeasure p).map
        (fun k : ℕ => (k : ℝ))) xi =
      ((p : ℝ) : ℂ) /
        (1 - (1 - ((p : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (xi : ℂ))) := by
  rw [Kyprianou.Ch01.discreteLawCharFun_asPGF
    (ProbabilityTheory.geometricMeasure p) xi]
  exact Kyprianou.Ch01.geometricMeasure_complexPGF p hp
    (Complex.exp (Complex.I * (xi : ℂ)))
    (Kyprianou.Ch01.geometricFourierConvergence p hp xi)
