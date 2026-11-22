-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_add
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:27:29.003701+00:00
-- url     : https://prove2.me/submissions/105187b3-9f8a-4681-be0a-e85beac7c244

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The range of the compensated Poisson integral on a horizon

A marked integrand supported in `[0, T]`, jointly and progressively measurable and of finite
energy, is admissible for the compensated integral up to `T`. Such integrands are closed under
sums and scalar multiples, and the integral is additive and homogeneous on them, so their
integrals form a submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence
of integrands to an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Poisson.Compensated

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Progressive

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}



theorem _root_.solution {φ₁ φ₂ : Ω → ℝ → E → ℝ}
    (h₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (h₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => φ₁ ω s e + φ₂ ω s e := by
  intro t
  have he : (fun p : Ω × ℝ × E => (Set.Iic t).indicator
      (fun s => φ₁ p.1 s p.2.2 + φ₂ p.1 s p.2.2) p.2.1) =
      (fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => φ₁ p.1 s p.2.2) p.2.1 +
        (Set.Iic t).indicator (fun s => φ₂ p.1 s p.2.2) p.2.1) := by
    funext p
    by_cases hp : p.2.1 ≤ t <;> simp [Set.indicator_apply, hp]
  rw [he]
  exact (h₁ t).add (h₂ t)
