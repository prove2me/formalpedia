-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.progressivelyMeasurable_globalPatch
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:39:02.90009+00:00
-- url     : https://prove2.me/submissions/8d412f69-42b8-4bb5-9fe4-431e25198535

import Definitions.Def_LevyStochCalc_Ito_PicardGlobal_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From window solutions to a solution on `[0, ∞)`

The Bielecki contraction produces a solution on each finite window. Uniqueness on the shorter of
two windows makes the family consistent, and right-continuity upgrades that to an almost-sure
agreement of whole paths, so the windows can be glued along `⌈t⌉₊` into a single path map that
restricts to a window solution on every `[0, T]`.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### Right-continuity upgrades per-time equality to path equality -/

/-! ### The glued path map -/


omit [MeasurableSpace E] [IsProbabilityMeasure P] in

theorem _root_.solution
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hY : ∀ k, ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y k s ω i)
    (i : Fin n) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => globalPatch Y s ω i := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  let g (k : ℕ) (p : Ω × ℝ) := (Set.Iic t).indicator (fun s => Y k s p.1 i) p.2
  have hg : Measurable fun q : ℕ × (Ω × ℝ) => g q.1 q.2 :=
    measurable_from_prod_countable_right fun k => (hY k i t).measurable
  have hm := (hg.comp (measurable_snd.nat_ceil.prodMk measurable_id)).stronglyMeasurable
  convert hm using 1
  funext q
  by_cases hq : q.2 ≤ t <;> simp [g, globalPatch, Set.indicator_apply, hq]
