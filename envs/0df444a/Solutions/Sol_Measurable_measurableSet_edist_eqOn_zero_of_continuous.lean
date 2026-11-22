-- Prove2me | solution 1 for Measurable.measurableSet_edist_eqOn_zero_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T04:01:00.855875+00:00
-- url     : https://prove2.me/submissions/68b27d49-7600-4c24-bc9f-cc02d91e5c78

import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsov_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E]


theorem _root_.solution [SecondCountableTopology T]
    {f g : T → Ω → E} (hU : IsOpen U)
    (hf : ∀ ω, ContinuousOn (f · ω) U) (hg : ∀ ω, ContinuousOn (g · ω) U)
    (h_meas : ∀ t, Measurable (fun ω ↦ edist (f t ω) (g t ω))) :
    MeasurableSet {ω | ∀ t ∈ U, edist (f t ω) (g t ω) = 0} := by
  classical
  by_cases h : Nonempty U
  · letI : Nonempty U := h
    let d : ℕ → U := TopologicalSpace.denseSeq U
    have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq U
    have he : {ω | ∀ t ∈ U, edist (f t ω) (g t ω) = 0} =
        ⋂ k : ℕ, {ω | edist (f (d k) ω) (g (d k) ω) = 0} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hω k
        exact hω (d k) (d k).property
      · intro hω t ht
        have hf' : Continuous (fun p : U => f p ω) :=
          continuousOn_iff_continuous_restrict.mp (hf ω)
        have hg' : Continuous (fun p : U => g p ω) :=
          continuousOn_iff_continuous_restrict.mp (hg ω)
        have hc : IsClosed {p : U | edist (f p ω) (g p ω) = 0} :=
          isClosed_eq (hf'.edist hg') continuous_const
        have hsub : Set.range d ⊆ {p : U | edist (f p ω) (g p ω) = 0} := by
          rintro _ ⟨k,rfl⟩
          exact hω k
        exact hc.closure_subset_iff.mpr hsub (hd ⟨t,ht⟩)
    rw [he]
    exact MeasurableSet.iInter (fun k => (h_meas (d k)) (measurableSet_singleton 0))
  · have he : U = ∅ := by
      ext t
      simp only [Set.mem_empty_iff_false, iff_false]
      intro ht
      exact h ⟨⟨t,ht⟩⟩
    simp [he]
