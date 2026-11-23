-- Prove2me | solution 1 for Kyprianou.markedCompoundPoissonRandomMeasureCh02V5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:43:38.642019+00:00
-- url     : https://prove2.me/submissions/5e9c121c-7051-4e6d-ba08-fa7f9b881636

import Mathlib
import Theorems.Thm_Kyprianou_markedCompoundPoissonRandomMeasureCh02V6
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFzero : F {0} = 0)
    (N : ℝ≥0 → Ω → ℕ)
    (T : ℕ → Ω → ℝ≥0)
    (ξ : ℕ → Ω → ℝ)
    (hTmeas : ∀ n : ℕ, Measurable (T n))
    (hξmeas : ∀ k : ℕ, Measurable (ξ k))
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
    (∀ (A : Set (ℝ × ℝ)), MeasurableSet A →
       intensity A = ⊤ →
       ∀ᵐ ω ∂P, μ ω A = ⊤) ∧
    (∀ {ι : Type} [Countable ι] (A : ι → Set (ℝ × ℝ)),
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       ProbabilityTheory.iIndepFun
         (fun i (ω : Ω) => μ ω (A i)) P) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
       μ ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ) = (N t ω : ENNReal)) := by
  exact Kyprianou.markedCompoundPoissonRandomMeasureCh02V6
    P rate hrate F hFzero N T ξ (fun n _ => hTmeas n)
    hξmeas hNlevy hNlaw harrival hmarklaw hIID hcross
