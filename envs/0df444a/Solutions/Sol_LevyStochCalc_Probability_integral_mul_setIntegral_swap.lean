-- Prove2me | solution 1 for LevyStochCalc.Probability.integral_mul_setIntegral_swap
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:54:20.033626+00:00
-- url     : https://prove2.me/submissions/0f2b008a-78d5-436e-8fce-918b762ac30c

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

section Swap

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]



theorem _root_.solution {S : Set Y} (hSfin : μ S ≠ ⊤)
    {Z : Ω → ℝ} (hZ1 : Integrable Z P) {V : Ω → ℝ} (hVm : AEStronglyMeasurable V P)
    {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, |V ω| ≤ Mv)
    {F : Ω → Y → ℝ} (hFm : Measurable (Function.uncurry F))
    {MF : ℝ} (hFb : ∀ ω y, |F ω y| ≤ MF) :
    ∫ ω, Z ω * V ω * (∫ y in S, F ω y ∂μ) ∂P
      = ∫ y in S, ∫ ω, Z ω * V ω * F ω y ∂P ∂μ := by
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hSfin
  have hint : Integrable (Function.uncurry fun ω y => Z ω * V ω * F ω y)
      (P.prod (μ.restrict S)) := by
    refine Integrable.mono' (((hZ1.norm.mul_const Mv).mul_const MF).comp_fst _) ?_ ?_
    · exact ((hZ1.1.comp_fst.mul hVm.comp_fst).mul hFm.aestronglyMeasurable)
    · refine Filter.Eventually.of_forall fun p => ?_
      show ‖Z p.1 * V p.1 * F p.1 p.2‖ ≤ ‖Z p.1‖ * Mv * MF
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      have h0 : 0 ≤ |Z p.1| := abs_nonneg _
      have h1 := hVb p.1
      have h2 := hFb p.1 p.2
      have h3 : 0 ≤ |V p.1| := abs_nonneg _
      gcongr
  simp_rw [← integral_const_mul]
  exact integral_integral_swap hint
