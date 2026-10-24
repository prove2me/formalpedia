-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_lintegral_to_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:09:59.034422+00:00
-- url     : https://prove2.me/submissions/4124900a-e13f-4a54-85ae-f2706ab857d8

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib

open MeasureTheory

open MeasureTheory Filter Topology in

theorem solution (n : Nat) :
    ∫⁻ t : Real,
      (if t ∈ Set.Icc (0 : Real) 1 then
        ENNReal.ofReal ((1 - t) ^ n / (n.factorial : Real))
      else 0) ∂MeasureTheory.volume =
    ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n / (n.factorial : Real)) := by
  have : (fun t : Real => if t ∈ Set.Icc (0 : Real) 1 then
        ENNReal.ofReal ((1 - t) ^ n / (n.factorial : Real)) else 0) =
      (Set.Icc (0:Real) 1).indicator (fun t => ENNReal.ofReal ((1 - t) ^ n / (n.factorial : Real))) := by
    ext t; simp [Set.indicator]
  rw [this, lintegral_indicator measurableSet_Icc, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc, ofReal_integral_eq_lintegral_ofReal]
  · exact (Continuous.integrableOn_Icc (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have : 0 ≤ 1 - t := by linarith [ht.2]
    simp only [Pi.zero_apply]; positivity
