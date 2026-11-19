-- Prove2me | solution 1 for LevyStochCalc.Probability.integral_mul_setIntegral_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:53:46.152178+00:00
-- url     : https://prove2.me/submissions/c88f169d-e4df-4aff-ac20-acae6973c16c

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pairing an integrable weight against a time integral

For an integrable weight and a bounded jointly measurable process on a bounded time interval, the
expectation of the weight against the time integral of the process is the time integral of the
expectations.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]



theorem _root_.solution {a t : ℝ} {Z : Ω → ℂ} (hZm : Measurable Z)
    (hZ : Integrable Z P) {Φ : Ω → ℝ → ℂ} (hΦ : Measurable (Function.uncurry Φ))
    {C : ℝ} (hC : ∀ ω u, ‖Φ ω u‖ ≤ C) :
    ∫ ω, Z ω * (∫ u in Set.Ioc a t, Φ ω u) ∂P
      = ∫ u in Set.Ioc a t, (∫ ω, Z ω * Φ ω u ∂P) := by
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc a t)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hint : Integrable (Function.uncurry fun ω u => Z ω * Φ ω u)
      (P.prod ((volume : Measure ℝ).restrict (Set.Ioc a t))) := by
    refine Integrable.mono' ((hZ.norm.mul_const C).comp_fst _) ?_ ?_
    · exact ((hZm.comp measurable_fst).mul hΦ).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      show ‖Z p.1 * Φ p.1 p.2‖ ≤ ‖Z p.1‖ * C
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _ _) (norm_nonneg _)
  simp_rw [← integral_const_mul]
  exact integral_integral_swap hint
