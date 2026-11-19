-- Prove2me | solution 1 for LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:05:55.307195+00:00
-- url     : https://prove2.me/submissions/239c7f71-f00c-428a-a6fb-a8bd1273a4aa

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : Integrable (fun ω => |f ω|) P)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) {V : ℝ} (hV : ∫ ω, f ω ^ 2 ∂P ≤ V) :
    ∫ ω, |f ω| ∂P ≤ Real.sqrt V := by
  set c : ℝ := ∫ ω, |f ω| ∂P
  have h_nonneg : 0 ≤ ∫ ω, (|f ω| - c) ^ 2 ∂P :=
    integral_nonneg fun ω => sq_nonneg _
  have h_eq : (fun ω => (|f ω| - c) ^ 2) =
      (fun ω => f ω ^ 2 + (- (2 * c) * |f ω| + c ^ 2)) := by
    ext ω
    rw [sub_sq, sq_abs]
    ring
  have h_int2 : Integrable (fun ω => -(2 * c) * |f ω| + c ^ 2) P :=
    (hf.const_mul (-(2 * c))).add (integrable_const _)
  rw [h_eq, integral_add hf2 h_int2,
      integral_add (hf.const_mul (-(2 * c))) (integrable_const _),
      integral_const_mul, integral_const, smul_eq_mul, measureReal_def, measure_univ,
      ENNReal.toReal_one, one_mul] at h_nonneg
  have h_sq : c ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by
    change 0 ≤ (∫ ω, f ω ^ 2 ∂P) + (-(2 * c) * c + c ^ 2) at h_nonneg
    linarith
  exact Real.le_sqrt_of_sq_le (h_sq.trans hV)
