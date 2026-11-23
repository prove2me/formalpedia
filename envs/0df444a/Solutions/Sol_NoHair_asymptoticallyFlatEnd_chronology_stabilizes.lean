-- Prove2me | solution 1 for NoHair.asymptoticallyFlatEnd_chronology_stabilizes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:22:41.832982+00:00
-- url     : https://prove2.me/submissions/0db0d5d6-b97e-496c-b220-3bee45334a24
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_asymptoticallyFlatEnd_timelike_access_at_infinity
import Theorems.Thm_NoHair_chronoFuture_transitive
import Theorems.Thm_NoHair_chronology_at_infinity_cofinal

open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ)
    (hg : IsLorentzian g) (hs : IsSmoothBilinField g) (T : VecField M) (hT : IsTimeOrientation g T)
    (R₀ : ℝ) (hR : E.R ≤ R₀) (hC : 16 * |E.C| ≤ R₀) :
    let A := fun R : ℝ => E.ψ '' exteriorRegion R
    chronoPastAtInfinity g T A E.R = chronoPastSet g T (A R₀) ∧
    chronoFutureAtInfinity g T A E.R = chronoFutureSet g T (A R₀) ∧
    domainOfOuterCommunicationsAtInfinity g T A E.R = domainOfOuterCommunications g T (A R₀) ∧
    futureEventHorizonAtInfinity g T A E.R = futureEventHorizon g T (A R₀) := by
  let A := fun R : ℝ => E.ψ '' exteriorRegion R
  have hmono : Antitone A := by
    intro r s hrs
    exact image_mono (fun y hy => lt_of_le_of_lt hrs hy)
  have hcofinal (r : ℝ) : ∃ s, A s ⊆ A r := ⟨r,Subset.rfl⟩
  obtain ⟨hP₀,hF₀,_,_,_⟩ := chronology_at_infinity_cofinal g T A A E.R R₀ hmono hmono hcofinal hcofinal
  have access := asymptoticallyFlatEnd_timelike_access_at_infinity E hg T hT R₀ hR hC
  have hPast : chronoPastAtInfinity g T A R₀ = chronoPastSet g T (A R₀) := by
    ext x
    constructor
    · exact fun hx => hx R₀ le_rfl
    · intro hx R h₀
      obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp hx
      obtain ⟨z,hz,hyz⟩ := mem_iUnion₂.mp ((access hy).2 R h₀)
      exact mem_iUnion₂.mpr ⟨z,hz,chronoFuture_transitive g T hg hs hT hxy hyz⟩
  have hFuture : chronoFutureAtInfinity g T A R₀ = chronoFutureSet g T (A R₀) := by
    ext x
    constructor
    · exact fun hx => hx R₀ le_rfl
    · intro hx R h₀
      obtain ⟨y,hy,hyx⟩ := mem_iUnion₂.mp hx
      obtain ⟨z,hz,hzy⟩ := mem_iUnion₂.mp ((access hy).1 R h₀)
      exact mem_iUnion₂.mpr ⟨z,hz,chronoFuture_transitive g T hg hs hT hzy hyx⟩
  have hp := hP₀.trans hPast
  have hf := hF₀.trans hFuture
  refine ⟨hp,hf,?_,?_⟩
  · change chronoFutureAtInfinity g T A E.R ∩ chronoPastAtInfinity g T A E.R =
      chronoFutureSet g T (A R₀) ∩ chronoPastSet g T (A R₀)
    rw [hp,hf]
  · exact congrArg frontier hp
