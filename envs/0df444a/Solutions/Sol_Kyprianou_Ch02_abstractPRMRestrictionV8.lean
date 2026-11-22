-- Prove2me | solution 1 for Kyprianou.Ch02.abstractPRMRestrictionV8
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:56:08.191804+00:00
-- url     : https://prove2.me/submissions/ae953fb8-e4fa-41c8-8da6-a1f0d9af1b61

import Mathlib
import Definitions.Def_Kyprianou_Ch02_AbstractPoissonRandomMeasureV8
open MeasureTheory ProbabilityTheory Kyprianou.Ch02
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (N : Ω → Measure E)
    (hN : Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P m N) :
    ∀ (B : Set E), MeasurableSet B →
      Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P
        (m.restrict B) (fun ω => (N ω).restrict B) := by
  classical
  rcases hN with ⟨⟨hmeas, hfinite, hlaw, hinfinite, hind⟩, hcount⟩
  intro B hB
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro A hA
      simpa only [Measure.restrict_apply hA] using hmeas (A ∩ B) (hA.inter hB)
    · intro A hA hfin
      have hAB : m (A ∩ B) < ⊤ := by
        simpa only [Measure.restrict_apply hA] using hfin
      filter_upwards [hfinite (A ∩ B) (hA.inter hB) hAB] with ω hω
      simpa only [Measure.restrict_apply hA] using hω
    · intro A hA hfin
      have hAB : m (A ∩ B) < ⊤ := by
        simpa only [Measure.restrict_apply hA] using hfin
      simpa only [Measure.restrict_apply hA] using
        hlaw (A ∩ B) (hA.inter hB) hAB
    · intro A hA hinf
      have hAB : m (A ∩ B) = ⊤ := by
        simpa only [Measure.restrict_apply hA] using hinf
      filter_upwards [hinfinite (A ∩ B) (hA.inter hB) hAB] with ω hω
      simpa only [Measure.restrict_apply hA] using hω
    · intro ι inst A hA hdisj
      have hAB : ∀ i, MeasurableSet (A i ∩ B) :=
        fun i => (hA i).inter hB
      have hdAB : Pairwise (fun i j => Disjoint (A i ∩ B) (A j ∩ B)) := by
        intro i j hij
        exact (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
      simpa only [Measure.restrict_apply (hA _)] using
        hind (fun i => A i ∩ B) hAB hdAB
  · filter_upwards [hcount] with ω hω
    intro A hA
    simpa only [Measure.restrict_apply hA] using
      hω (A ∩ B) (hA.inter hB)
