-- Prove2me | solution 1 for Kyprianou.Ch01.realHarmonicIntegralFormulaV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:51:09.691174+00:00
-- url     : https://prove2.me/submissions/de3ae578-a49e-4a09-b46b-90c051ee83a7

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Positivity
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Kyprianou.Ch01 Set Real
open scoped NNReal ENNReal Interval
set_option autoImplicit false

/-- Integrate the positive harmonic kernel using the shifted reciprocal. -/
theorem solution (s : ℝ≥0) :
    (∫ r in Set.Ioc (0 : ℝ) (s : ℝ),
      ((1 : ℝ) / (1 + r)) ∂volume) =
        Real.log (1 + (s : ℝ)) := by
  have h0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
  have hbound : (1 : ℝ) ≤ 1 + (s : ℝ) := by
    linarith [NNReal.coe_nonneg s]
  have hn : (0 : ℝ) ∉ [[(1 : ℝ), 1 + (s : ℝ)]] := by
    rw [Set.uIcc_of_le hbound]
    simp
  have hshift :=
    intervalIntegral.integral_comp_add_left
      (f := fun r : ℝ => 1 / r)
      (a := (0 : ℝ)) (b := (s : ℝ)) (1 : ℝ)
  rw [← intervalIntegral.integral_of_le h0]
  calc
    (∫ r in (0 : ℝ)..(s : ℝ), 1 / (1 + r)) =
      ∫ r in (1 : ℝ)..(1 + (s : ℝ)), 1 / r := by
        simpa only [add_zero, zero_add] using hshift
    _ = Real.log ((1 + (s : ℝ)) / 1) := integral_one_div hn
    _ = Real.log (1 + (s : ℝ)) := by simp
