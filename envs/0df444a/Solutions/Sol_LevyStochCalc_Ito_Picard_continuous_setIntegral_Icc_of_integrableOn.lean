-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.continuous_setIntegral_Icc_of_integrableOn
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T04:01:20.04281+00:00
-- url     : https://prove2.me/submissions/c281965e-1bc9-4d41-8921-360b8b07bc86

import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Càdlàg modifications of the Picard step

The `L²` stochastic integral is defined separately at each time, so the Picard step as first
written has no path regularity. Replacing each Brownian component by a càdlàg adapted
modification, and the drift by its almost surely continuous version, produces a process
indistinguishable from the step at every fixed time and càdlàg along almost every path; the
Bielecki norm is unchanged, and the result is a genuine self-map of the space of bounded
adapted càdlàg processes.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]


omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in

theorem _root_.solution {f : ℝ → ℝ}
    (h_int : ∀ b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) b) volume) :
    Continuous fun t => ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume := by
  let g : ℝ → ℝ := (Set.Ici 0).indicator f
  have hI (a b : ℝ) : IntervalIntegrable g volume a b := by
    rw [intervalIntegrable_iff]
    have hB : Integrable ((Set.Icc (0 : ℝ) (max a b)).indicator f) volume :=
      (integrable_indicator_iff measurableSet_Icc).2 (h_int _)
    refine (hB.integrableOn (s := Set.uIoc a b)).congr_fun ?_ measurableSet_uIoc
    intro x hx
    have hx' : x ≤ max a b := hx.2
    by_cases h : 0 ≤ x <;> simp [g, Set.indicator_apply, h, hx']
  have hc := intervalIntegral.continuous_primitive hI (0 : ℝ)
  convert hc using 1
  funext t
  rcases le_or_gt 0 t with ht | ht
  · rw [intervalIntegral.integral_of_le ht, integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simp [g, Set.indicator_apply, hx.1.le]
  · rw [Set.Icc_eq_empty (not_le.mpr ht), setIntegral_empty, intervalIntegral.integral_of_ge ht.le,
      integral_Ioc_eq_integral_Ioo]
    have hzero : Set.EqOn g (fun _ => 0) (Set.Ioo t (0 : ℝ)) := by
      intro x hx
      simp [g, Set.indicator_apply, not_le.mpr hx.2]
    rw [setIntegral_congr_fun measurableSet_Ioo hzero]
    simp
