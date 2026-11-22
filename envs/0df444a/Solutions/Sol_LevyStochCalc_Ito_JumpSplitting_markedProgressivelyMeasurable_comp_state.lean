-- Prove2me | solution 1 for LevyStochCalc.Ito.JumpSplitting.markedProgressivelyMeasurable_comp_state
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:36:23.074802+00:00
-- url     : https://prove2.me/submissions/a7579b16-1b68-48ca-b252-fa94047ad0f6

import Definitions.Def_LevyStochCalc_Ito_LeftLimIntegrandRegularity_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Regularity of a jump coefficient read at the left limits of a path

A path having left limits everywhere meets, at each time, the limit along the dyadic grid points
below that time. The left limits are therefore a countable limit of evaluations of the path, so
they are jointly measurable when the path is, and predictable — hence progressively measurable —
when the path is adapted. Composing with a jointly measurable jump coefficient carries these to
the left-limit jump integrand. Its energy on a horizon is that of the integrand along the path
itself, because a càdlàg path meets its left limits at all but countably many positive times.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.measurable_uncurry_leftLimPathAt`,
  `LevyStochCalc.Ito.JumpSplitting.progressivelyMeasurable_leftLimPathAt` — joint measurability
  and progressive measurability of the left limits of a path.
* `LevyStochCalc.Ito.JumpSplitting.markedProgressivelyMeasurable_comp_state` — a jointly
  measurable function of the time, a progressively measurable state and the mark is marked
  progressively measurable.
* `LevyStochCalc.Ito.JumpSplitting.measurable_jumpCoeff_leftLimPathAt`,
  `LevyStochCalc.Ito.JumpSplitting.markedProgressivelyMeasurable_jumpCoeff_leftLimPathAt`,
  `LevyStochCalc.Ito.JumpSplitting.lintegral_sq_jumpCoeff_leftLimPathAt_eq` — the three
  admissibility data of the left-limit jump integrand.

## References

* Protter, *Stochastic Integration and Differential Equations*, 2005, §III.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Probability

end LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {n : ℕ}

section Measurability

variable {Xp : ℝ → Ω → Fin n → ℝ}

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}



theorem _root_.solution {Λ : ℝ → Ω → Fin n → ℝ}
    (hΛ : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => Λ s ω i)
    {F : ℝ → (Fin n → ℝ) → E → ℝ}
    (hF : Measurable fun q : ℝ × (Fin n → ℝ) × E => F q.1 q.2.1 q.2.2) :
    MarkedProgressivelyMeasurable ℱ fun ω s e => F s (Λ s ω) e := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hstate : Measurable (fun q : Ω × ℝ × E => fun i => (Set.Iic t).indicator
      (fun s => Λ s q.1 i) q.2.1) := by
    apply measurable_pi_lambda
    intro i
    exact (hΛ i t).measurable.comp (measurable_fst.prodMk measurable_snd.fst)
  have h := (hF.comp (measurable_snd.fst.prodMk (hstate.prodMk measurable_snd.snd))).stronglyMeasurable
  have hs : MeasurableSet (Prod.fst ∘ Prod.snd ⁻¹' Set.Iic t : Set (Ω × ℝ × E)) :=
    measurable_snd.fst measurableSet_Iic
  convert h.indicator hs using 1
  funext q
  by_cases hq : q.2.1 ≤ t
  · simp [Set.indicator_apply, Function.comp_def, hq]
  · simp [Set.indicator_apply, Function.comp_def, hq]
