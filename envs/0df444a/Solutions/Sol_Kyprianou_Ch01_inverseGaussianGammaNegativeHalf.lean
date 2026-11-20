-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianGammaNegativeHalf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:29:12.259488+00:00
-- url     : https://prove2.me/submissions/827e8c15-38b1-4740-b636-e37da793fad1

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem solution :
    Real.Gamma (-(1 / 2 : ℝ)) = -2 * Real.sqrt Real.pi := by
  have hrec := Real.Gamma_add_one (s := -(1 / 2 : ℝ)) (by norm_num)
  have h : Real.sqrt Real.pi =
      (-(1 / 2 : ℝ)) * Real.Gamma (-(1 / 2 : ℝ)) := by
    simpa only [show (-(1 / 2 : ℝ)) + 1 = (1 / 2 : ℝ) by ring,
      Real.Gamma_one_half_eq] using hrec
  linarith
