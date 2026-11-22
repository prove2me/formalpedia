-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_comp_state
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:36:23.118586+00:00
-- url     : https://prove2.me/submissions/5309a4ed-783c-4d53-a8eb-b0203223b5e6

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Square integrability of the Picard integrands along a state process

Linear growth of the coefficients, read off the Lipschitz hypothesis by comparison with the
state `0`, turns the bounds at that single state recorded by `IsRegular` into bounds along a
state process: whenever the state has finite energy over every horizon, the drift, diffusion
and jump integrands evaluated along it are square integrable at every horizon, and a member of
the process space frozen at `T` has that energy. Composing a jointly measurable coefficient
with a measurable, respectively progressively measurable, state process supplies the matching
measurability of the integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]



theorem _root_.solution {n : ℕ}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {X : ℝ → Ω → (Fin n → ℝ)}
    (hX : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ (fun ω s => X s ω i))
    {g : ℝ → (Fin n → ℝ) → E → ℝ}
    (hg : Measurable fun p : ℝ × (Fin n → ℝ) × E => g p.1 p.2.1 p.2.2) :
    Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => g s (X s ω) e) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hstate : Measurable (fun q : Ω × ℝ × E => fun i => (Set.Iic t).indicator
      (fun s => X s q.1 i) q.2.1) := by
    apply measurable_pi_lambda
    intro i
    exact (hX i t).measurable.comp (measurable_fst.prodMk measurable_snd.fst)
  have h := (hg.comp (measurable_snd.fst.prodMk (hstate.prodMk measurable_snd.snd))).stronglyMeasurable
  have hs : MeasurableSet (Prod.fst ∘ Prod.snd ⁻¹' Set.Iic t : Set (Ω × ℝ × E)) :=
    measurable_snd.fst measurableSet_Iic
  convert h.indicator hs using 1
  funext q
  by_cases hq : q.2.1 ≤ t
  · simp [Set.indicator_apply, Function.comp_def, hq]
  · simp [Set.indicator_apply, Function.comp_def, hq]
