-- Prove2me | solution 1 for LevyStochCalc.abs_setIntegral_Ioc_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:08:42.223807+00:00
-- url     : https://prove2.me/submissions/afa59ca3-61a3-40ac-a962-8d0425dfac23

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/DriftIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open MeasureTheory
/-- A bounded measurable function is integrable on any set of finite measure. -/
theorem LevyStochCalc.integrableOn_of_bounded_of_measurable {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    MeasureTheory.IntegrableOn f s volume := by
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := B) hs hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hB u
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc in
/-- The integral of a function bounded by `B` over `(a, b]` is at most `B·(b − a)` in size. -/
theorem solution {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (hab : a ≤ b) :
    |∫ s in Set.Ioc a b, f s ∂volume| ≤ B * (b - a) := by
  have hB0 : (0 : ℝ) ≤ B := (abs_nonneg (f a)).trans (hB a)
  have hint : MeasureTheory.IntegrableOn f (Set.Ioc a b) volume :=
    LevyStochCalc.integrableOn_of_bounded_of_measurable hf hB (by simp)
  have habs : |∫ s in Set.Ioc a b, f s ∂volume| ≤ ∫ s in Set.Ioc a b, |f s| ∂volume := by
    simpa [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc a b)) f
  refine habs.trans ?_
  have hle : ∫ s in Set.Ioc a b, |f s| ∂volume ≤ ∫ _s in Set.Ioc a b, B ∂volume := by
    refine MeasureTheory.setIntegral_mono_on hint.abs
      (MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc
      fun u _ => hB u
  refine hle.trans ?_
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  exact le_of_eq (mul_comm _ _)
