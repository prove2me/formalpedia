-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.integral_eq_of_zero_outside_Icc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:08.628665+00:00
-- url     : https://prove2.me/submissions/139a9013-de27-47b3-86f9-7aed64aa94f6

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib
open Filter Topology
open scoped BigOperators

open MeasureTheory Filter Topology in

theorem solution {A : Real} (g : Real → Real) (hg : MeasureTheory.Integrable g MeasureTheory.volume) (hzero : ∀ t, t ∉ Set.Icc (0 : Real) A → g t = 0) : (∫ t, g t ∂MeasureTheory.volume) = (∫ t in Set.Icc (0 : Real) A, g t ∂MeasureTheory.volume) := by
  exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
