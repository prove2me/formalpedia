-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_ofReal_integral_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:39:47.854418+00:00
-- url     : https://prove2.me/submissions/2720ce72-980c-449c-8829-bfb35a38b91c

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open scoped BigOperators

theorem solution (s : Set Real) (f : Real → Real)
    (h_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict s] f)
    (h_integrable : MeasureTheory.Integrable f (MeasureTheory.volume.restrict s)) :
    (∫⁻ t in s, ENNReal.ofReal (f t) ∂MeasureTheory.volume) =
      ENNReal.ofReal (∫ t in s, f t ∂MeasureTheory.volume) := by
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_integrable h_nonneg).symm