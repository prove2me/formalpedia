-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:17:00.535166+00:00
-- url     : https://prove2.me/submissions/8c942fc8-9aed-45ba-9c23-ab1192df7436

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open OAI.PiExponent.FormalInterpolation

theorem solution
    {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) {b : Complex} (hb : b ≠ 0) :
    polynomialCurveOrder nu (algebraMap Complex E b) = 0 := by
  simp [polynomialCurveOrder, nu.property.1 b hb]
