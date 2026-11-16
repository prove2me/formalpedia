-- Prove2me | solution 1 for Kyprianou.Ch01.levyTripletExponentSignBridgeReviewed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:21:59.924074+00:00
-- url     : https://prove2.me/submissions/abb5f3a4-170b-46d7-b809-d345cd42a5ae

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
