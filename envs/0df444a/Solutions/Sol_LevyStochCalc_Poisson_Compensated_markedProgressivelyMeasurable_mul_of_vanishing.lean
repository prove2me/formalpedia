-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_mul_of_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:36:13.726358+00:00
-- url     : https://prove2.me/submissions/ebeb57d6-cc16-4e8a-b4ce-d535e1d45790

import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pulling a past weight inside a compensated integral

A bounded weight measurable at time `a` times the compensated integral of a marked integrand
vanishing up to `a` is the compensated integral of the weighted integrand. The identity is proved
in `L²`: the squared distance between the two sides expands, through the Itô–Lévy isometry and
the quadratic-variation martingale started at `a`, into a combination of weighted compensators
that cancels.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Vanishing

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ < ⊤)

end Vanishing

section Weighted



theorem _root_.solution {φ : Ω → ℝ → E → ℝ}
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ) {a : ℝ}
    (hφa : ∀ ω s e, s ≤ a → φ ω s e = 0) {V : Ω → ℝ} (hVm : StronglyMeasurable[ℱ a] V) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => V ω * φ ω s e := by
  intro t
  by_cases hat : a ≤ t
  · have hv : StronglyMeasurable[ℱ t] V := hVm.mono (ℱ.mono hat)
    have h := (hv.comp_measurable measurable_fst).mul (hp t)
    convert h using 1
    funext p
    by_cases ht : p.2.1 ≤ t <;> simp [Set.indicator_apply, ht]
  · have hz : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => V p.1 * φ p.1 s p.2.2) p.2.1) = 0 := by
      funext p
      by_cases ht : p.2.1 ≤ t
      · simp [Set.indicator_apply, ht, hφa _ _ _ (ht.trans (le_of_lt (lt_of_not_ge hat)))]
      · simp [Set.indicator_apply, ht]
    rw [hz]
    exact stronglyMeasurable_const
