-- Prove2me | solution 1 for Kyprianou.markedCompoundPoissonRandomMeasureCh02V4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:33:46.495585+00:00
-- url     : https://prove2.me/submissions/74ca73b1-88d0-4b30-8f65-89a58f4f6b9d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_ch02MarkedPoissonFiniteRegionLaw
import Theorems.Thm_Kyprianou_ch02MarkedPoissonIndependentDisjointCounts
import Theorems.Thm_Kyprianou_ch02MarkedPoissonCountEqualsN
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFzero : F {0} = 0)
    (N : ℝ≥0 → Ω → ℕ)
    (T : ℕ → Ω → ℝ≥0)
    (ξ : ℕ → Ω → ℝ)
    (hNlevy : ProbabilityTheory.IsLevyProcess
       (fun t ω => (N t ω : ℝ)) P)
    (hNlaw : ∀ t : ℝ≥0,
       P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (harrival : ∀ᵐ ω ∂P,
       ∀ (n : ℕ), 0 < n →
         ∀ (t : ℝ≥0), (n ≤ N t ω ↔ T n ω ≤ t))
    (hmarklaw : ∀ k : ℕ, P.map (ξ k) = F)
    (hIID : ProbabilityTheory.iIndepFun ξ P)
    (hcross : ProbabilityTheory.Indep
      (⨆ k : ℕ, MeasurableSpace.comap (ξ k) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (N t) inferInstance) P) :
    let μ : Ω → Measure (ℝ × ℝ) := fun ω =>
      Measure.sum (fun n : ℕ =>
        Measure.dirac ((T (n + 1) ω : ℝ), ξ (n + 1) ω))
    let intensity : Measure (ℝ × ℝ) :=
      (volume.restrict (Set.Ici (0 : ℝ))).prod ((rate : ENNReal) • F)
    (∀ (A : Set (ℝ × ℝ)), MeasurableSet A →
       intensity A < ⊤ →
       P.map (fun ω => μ ω A) =
         (ProbabilityTheory.poissonMeasure (intensity A).toNNReal).map
           (Nat.cast : ℕ → ENNReal)) ∧
    (∀ {ι : Type} [Countable ι] (A : ι → Set (ℝ × ℝ)),
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       ProbabilityTheory.iIndepFun
         (fun i (ω : Ω) => μ ω (A i)) P) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
       μ ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ) = (N t ω : ENNReal)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Kyprianou.ch02MarkedPoissonFiniteRegionLaw
      P rate hrate F hFzero N T ξ hNlevy hNlaw harrival hmarklaw hIID hcross
  · exact Kyprianou.ch02MarkedPoissonIndependentDisjointCounts
      P rate hrate F hFzero N T ξ hNlevy hNlaw harrival hmarklaw hIID hcross
  · exact Kyprianou.ch02MarkedPoissonCountEqualsN
      P rate hrate F hFzero N T ξ hNlevy hNlaw harrival hmarklaw hIID hcross

