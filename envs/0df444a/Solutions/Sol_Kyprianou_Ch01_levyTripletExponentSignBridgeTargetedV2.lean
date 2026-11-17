-- Prove2me | solution 1 for Kyprianou.Ch01.levyTripletExponentSignBridgeTargetedV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T19:48:38.712098+00:00
-- url     : https://prove2.me/submissions/fee3b2ae-2ccc-45dc-834c-8c8a0af479b2

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
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
