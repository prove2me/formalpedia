-- Prove2me | solution 1 for NoHair.chronology_at_infinity_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T08:34:52.757038+00:00
-- url     : https://prove2.me/submissions/91c1d23b-5502-451a-9e00-f05b0e6362d7

import Definitions.Def_NoHair_chronologyAtInfinity

open NoHair Set
open scoped ContDiff Manifold

private theorem compare_tails {M : Type*} (f : Set M → Set M) (hf : Monotone f)
    (A B : ℝ → Set M) (a b : ℝ) (hA : Antitone A)
    (hBA : ∀ S, ∃ R, A R ⊆ B S) {x : M}
    (hx : ∀ R, a ≤ R → x ∈ f (A R)) : ∀ S, b ≤ S → x ∈ f (B S) := by
  intro S _
  obtain ⟨R,hR⟩ := hBA S
  have hsub : A (max a R) ⊆ B S := (hA (le_max_right a R)).trans hR
  exact hf hsub (hx (max a R) (le_max_left a R))

private theorem all_tails_eq {M : Type*} (f : Set M → Set M) (hf : Monotone f)
    (A B : ℝ → Set M) (a b : ℝ) (hA : Antitone A) (hB : Antitone B)
    (hAB : ∀ R, ∃ S, B S ⊆ A R) (hBA : ∀ S, ∃ R, A R ⊆ B S) :
    {x | ∀ R, a ≤ R → x ∈ f (A R)} = {x | ∀ S, b ≤ S → x ∈ f (B S)} := by
  ext x
  exact ⟨compare_tails f hf A B a b hA hBA, compare_tails f hf B A b a hB hAB⟩


theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (T : VecField M)
    (A B : ℝ → Set M) (a b : ℝ) (hA : Antitone A) (hB : Antitone B)
    (hAB : ∀ R, ∃ S, B S ⊆ A R) (hBA : ∀ S, ∃ R, A R ⊆ B S) :
    chronoPastAtInfinity g T A a = chronoPastAtInfinity g T B b ∧
    chronoFutureAtInfinity g T A a = chronoFutureAtInfinity g T B b ∧
    domainOfOuterCommunicationsAtInfinity g T A a = domainOfOuterCommunicationsAtInfinity g T B b ∧
    futureEventHorizonAtInfinity g T A a = futureEventHorizonAtInfinity g T B b ∧
    domainOfOuterCommunicationsAtInfinity g T A a ⊆ domainOfOuterCommunications g T (A a) := by
  have hPastMono : Monotone (chronoPastSet g T) := by
    intro S S' hSS' x hx
    obtain ⟨z,hz,hxz⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨z,hSS' hz,hxz⟩
  have hFutureMono : Monotone (chronoFutureSet g T) := by
    intro S S' hSS' x hx
    obtain ⟨z,hz,hzx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨z,hSS' hz,hzx⟩
  have hP : chronoPastAtInfinity g T A a = chronoPastAtInfinity g T B b :=
    all_tails_eq _ hPastMono A B a b hA hB hAB hBA
  have hF : chronoFutureAtInfinity g T A a = chronoFutureAtInfinity g T B b :=
    all_tails_eq _ hFutureMono A B a b hA hB hAB hBA
  refine ⟨hP,hF,?_,?_,?_⟩
  · rw [domainOfOuterCommunicationsAtInfinity, domainOfOuterCommunicationsAtInfinity, hP, hF]
  · exact congrArg frontier hP
  · intro x hx
    exact ⟨hx.1 a le_rfl, hx.2 a le_rfl⟩
