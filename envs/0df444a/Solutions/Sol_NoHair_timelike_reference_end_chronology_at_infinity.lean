-- Prove2me | solution 1 for NoHair.timelike_reference_end_chronology_at_infinity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:41:07.907164+00:00
-- url     : https://prove2.me/submissions/1a43cde5-54ae-47e1-8780-5ae8d07fde8e

import Theorems.Thm_NoHair_timelike_reference_end_two_way_access
import Theorems.Thm_NoHair_chronoFuture_transitive

open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ) (hg : IsLorentzian g) (hs : IsSmoothBilinField g)
    (T : VecField M) (hT : IsTimeOrientation g T) (hφ : IsSymmetryFlow g F φ)
    (hK : ∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0) :
    let A := fun R => E.ψ '' exteriorRegion R
    chronoPastAtInfinity g T A E.R = chronoPastSet g T E.region ∧
    chronoFutureAtInfinity g T A E.R = chronoFutureSet g T E.region ∧
    domainOfOuterCommunicationsAtInfinity g T A E.R = domainOfOuterCommunications g T E.region ∧
    futureEventHorizonAtInfinity g T A E.R = futureEventHorizon g T E.region := by
  let A := fun R : ℝ => E.ψ '' exteriorRegion R
  have access := timelike_reference_end_two_way_access E hg hs T hT hφ hK
  have hPast : chronoPastAtInfinity g T A E.R = chronoPastSet g T (A E.R) := by
    ext x
    constructor
    · exact fun hx => hx E.R le_rfl
    · intro hx R h₀
      obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp hx
      obtain ⟨z,hz,hyz⟩ := mem_iUnion₂.mp ((access hy).2 R h₀)
      exact mem_iUnion₂.mpr ⟨z,hz,chronoFuture_transitive g T hg hs hT hxy hyz⟩
  have hFuture : chronoFutureAtInfinity g T A E.R = chronoFutureSet g T (A E.R) := by
    ext x
    constructor
    · exact fun hx => hx E.R le_rfl
    · intro hx R h₀
      obtain ⟨y,hy,hyx⟩ := mem_iUnion₂.mp hx
      obtain ⟨z,hz,hzy⟩ := mem_iUnion₂.mp ((access hy).1 R h₀)
      exact mem_iUnion₂.mpr ⟨z,hz,chronoFuture_transitive g T hg hs hT hzy hyx⟩
  have hp := hPast
  have hf := hFuture
  refine ⟨hp,hf,?_,?_⟩
  · change chronoFutureAtInfinity g T A E.R ∩ chronoPastAtInfinity g T A E.R =
      chronoFutureSet g T (A E.R) ∩ chronoPastSet g T (A E.R)
    rw [hp,hf]
  · exact congrArg frontier hp
