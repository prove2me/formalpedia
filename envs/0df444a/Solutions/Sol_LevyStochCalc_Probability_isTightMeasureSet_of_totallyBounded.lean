-- Prove2me | solution 1 for LevyStochCalc.Probability.isTightMeasureSet_of_totallyBounded
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:58:07.106494+00:00
-- url     : https://prove2.me/submissions/f93c0fc0-9b76-466a-96c4-370a10c3c895

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Completeness of the Lévy–Prokhorov metric

On a proper metric space `Ω` (for instance `ℝ` or `ℝⁿ`) with its Borel σ-algebra, the
Lévy–Prokhorov metric on probability measures is complete.

A totally bounded set of probability measures is tight: take a finite `ε/2`-net, a compact set `K`
carrying all but `ε/2` of the mass of each net point, and the closed `ε/2`-thickening of `K`, which
is compact because `Ω` is proper; the Lévy–Prokhorov thickening inequality transfers the mass bound
from each net point to every measure near it. By Prokhorov's theorem a tight set has compact
closure, so the range of a Cauchy sequence is relatively compact and the sequence converges.

## Main statements

* `LevyStochCalc.Probability.isTightMeasureSet_of_totallyBounded` — a totally bounded set of
  probability measures is tight.
* `LevyStochCalc.Probability.isCompact_closure_of_isTightMeasureSet_levyProkhorov` — Prokhorov's
  theorem in the Lévy–Prokhorov metric: a tight set has compact closure.
* `LevyStochCalc.Probability.instCompleteSpaceLevyProkhorovProbabilityMeasure` — the
  Lévy–Prokhorov metric space of probability measures is complete.
-/

open MeasureTheory Filter Set Topology TopologicalSpace
open scoped ENNReal

namespace LevyStochCalc.Probability

variable {Ω : Type*} [MetricSpace Ω] [ProperSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]

theorem _root_.solution
    (S : Set (LevyProkhorov (ProbabilityMeasure Ω))) (hS : TotallyBounded S) :
    IsTightMeasureSet {(μ.toMeasure.toMeasure : Measure Ω) | μ ∈ S} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact ⟨∅, isCompact_empty, fun _ _ => le_top⟩
  set δ : ℝ := ε.toReal / 2 with hδ
  have hδ0 : 0 < δ := by
    have := ENNReal.toReal_pos hε.ne' hεt
    positivity
  obtain ⟨t, -, htfin, hcov⟩ := Metric.finite_approx_of_totallyBounded hS δ hδ0
  have hK : ∀ y : LevyProkhorov (ProbabilityMeasure Ω), ∃ K : Set Ω, IsCompact K ∧
      (y.toMeasure.toMeasure : Measure Ω) Kᶜ ≤ ENNReal.ofReal δ := by
    intro y
    have h1 : IsTightMeasureSet {(y.toMeasure.toMeasure : Measure Ω)} := isTightMeasureSet_singleton
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at h1
    obtain ⟨K, hKc, hKm⟩ := h1 _ (ENNReal.ofReal_pos.2 hδ0)
    exact ⟨K, hKc, hKm _ rfl⟩
  choose K hKc hKm using hK
  refine ⟨Metric.cthickening δ (⋃ y ∈ t, K y),
    (htfin.isCompact_biUnion fun y _ => hKc y).cthickening, ?_⟩
  rintro _ ⟨μ, hμS, rfl⟩
  obtain ⟨y, hyt, hμy⟩ := mem_iUnion₂.1 (hcov hμS)
  have hdist : levyProkhorovDist (μ.toMeasure.toMeasure : Measure Ω) (y.toMeasure.toMeasure) < δ :=
    Metric.mem_ball.1 hμy
  have hd : levyProkhorovEDist (μ.toMeasure.toMeasure : Measure Ω) (y.toMeasure.toMeasure)
      < ENNReal.ofReal δ :=
    (ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _)).2 hdist
  have hmeas : MeasurableSet (Metric.cthickening δ (⋃ y ∈ t, K y))ᶜ :=
    Metric.isClosed_cthickening.isOpen_compl.measurableSet
  have h1 := left_measure_le_of_levyProkhorovEDist_lt hd hmeas
  rw [ENNReal.toReal_ofReal hδ0.le] at h1
  have hsub : Metric.thickening δ (Metric.cthickening δ (⋃ y ∈ t, K y))ᶜ ⊆ (K y)ᶜ := by
    intro x hx hxK
    obtain ⟨z, hz, hxz⟩ := Metric.mem_thickening_iff.1 hx
    apply hz
    refine Metric.mem_cthickening_of_dist_le z x δ _ (mem_iUnion₂.2 ⟨y, hyt, hxK⟩) ?_
    rw [dist_comm]; exact hxz.le
  calc (μ.toMeasure.toMeasure : Measure Ω) (Metric.cthickening δ (⋃ y ∈ t, K y))ᶜ
      ≤ (y.toMeasure.toMeasure : Measure Ω) (K y)ᶜ + ENNReal.ofReal δ :=
        h1.trans (by gcongr)
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := by gcongr; exact hKm y
    _ = ε := by
        rw [← ENNReal.ofReal_add hδ0.le hδ0.le, hδ, add_halves, ENNReal.ofReal_toReal hεt]

end LevyStochCalc.Probability
