-- Prove2me | solution 2 for OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_power_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:18.247009+00:00
-- url     : https://prove2.me/submissions/b40b4513-a301-4b0b-a17c-2072c281215a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib

open MeasureTheory

section
open MeasureTheory Filter Topology
theorem O3ii (n : Nat) :
    ∫ t in (0 : Real)..1, (1 - t) ^ n / (n.factorial : Real) =
    1 / ((n + 1).factorial : Real) := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun t => t ^ n)]
  simp [integral_pow, Nat.factorial_succ]
  field_simp

end

open MeasureTheory Filter Topology in

theorem solution (n : Nat) :
    ∫⁻ t : Real,
      (if t ∈ Set.Icc (0 : Real) 1 then
        ENNReal.ofReal ((1 - t) ^ n / (n.factorial : Real))
      else 0) ∂MeasureTheory.volume =
    ENNReal.ofReal (1 / ((n + 1).factorial : Real)) := by
  have : (fun t : Real => if t ∈ Set.Icc (0 : Real) 1 then
        ENNReal.ofReal ((1 - t) ^ n / (n.factorial : Real)) else 0) =
      (Set.Icc (0:Real) 1).indicator (fun t => ENNReal.ofReal ((1 - t) ^ n / (n.factorial : Real))) := by
    ext t; simp [Set.indicator]
  rw [this, lintegral_indicator measurableSet_Icc, ← O3ii, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc, ofReal_integral_eq_lintegral_ofReal]
  · exact (Continuous.integrableOn_Icc (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have : 0 ≤ 1 - t := by linarith [ht.2]
    simp only [Pi.zero_apply]; positivity
