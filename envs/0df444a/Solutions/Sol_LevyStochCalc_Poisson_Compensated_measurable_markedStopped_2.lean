-- Prove2me | solution 2 for LevyStochCalc.Poisson.Compensated.measurable_markedStopped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:42:19.356979+00:00
-- url     : https://prove2.me/submissions/1095c469-1a46-4e4d-b178-10e30545b188

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityCutoff_F000
import Theorems.Thm_LevyStochCalc_Probability_measurableSet_stoppedSet

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The marked integrand cut off at a stopping time

The marked process `markedStopped τ φ`, which agrees with `φ` at the times a stopping time `τ`
has not passed and vanishes afterwards, is dominated pointwise by `φ` and inherits from it joint
measurability, marked progressive measurability and finite energy; those three admissibility
properties transport along an equality of marked integrands and are stable under differences.

## Main definitions

* `markedStopped τ φ` — the marked process `φ` cut off at the stopping time `τ`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section MarkedStopped

variable (τ : Ω → WithTop ℝ) (φ : Ω → ℝ → E → ℝ)

variable {τ φ}


theorem _root_.solution (hτ : IsStoppingTime ℱ τ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) :
    Measurable fun p : Ω × ℝ × E => markedStopped τ φ p.1 p.2.1 p.2.2 := by
  set S : Set (Ω × ℝ × E) := {p | (p.1, p.2.1) ∈ LevyStochCalc.Probability.stoppedSet τ}
    with hS
  have hfun : (fun p : Ω × ℝ × E => markedStopped τ φ p.1 p.2.1 p.2.2)
      = S.indicator fun p => φ p.1 p.2.1 p.2.2 := by
    funext p
    by_cases hp : ((p.2.1 : ℝ) : WithTop ℝ) ≤ τ p.1
    · rw [Set.indicator_of_mem (show p ∈ S from hp)]
      exact if_pos hp
    · rw [Set.indicator_of_notMem (show p ∉ S from hp)]
      exact if_neg hp
  rw [hfun]
  have hS_meas : MeasurableSet S :=
    (LevyStochCalc.Probability.measurableSet_stoppedSet hτ).preimage
      (measurable_fst.prodMk measurable_snd.fst)
  exact hm.indicator hS_meas
end MarkedStopped

section Transport

variable {φ ψ : Ω → ℝ → E → ℝ}

end Transport

end LevyStochCalc.Poisson.Compensated
