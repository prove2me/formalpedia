-- Prove2me | solution 1 for Kyprianou.Ch01.levyTripletExponentSignBridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:28:56.476624+00:00
-- url     : https://prove2.me/submissions/12d29df6-ddeb-46ea-b2c0-f0f255599645

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Complex
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) (xi : ℝ) :
    -levyTripleExponent T xi =
      -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) +
      (((T.gaussianVariance : ℝ) * xi ^ 2 / 2 : ℝ) : ℂ) -
      (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂T.levyMeasure) := by
  unfold Kyprianou.Ch01.levyTripleExponent
  ring
