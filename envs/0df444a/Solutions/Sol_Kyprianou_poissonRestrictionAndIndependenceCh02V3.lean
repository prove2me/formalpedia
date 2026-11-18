-- Prove2me | solution 1 for Kyprianou.poissonRestrictionAndIndependenceCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:48:40.63207+00:00
-- url     : https://prove2.me/submissions/7d51eb1d-8080-4195-95f6-bed16ed97413

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_ch02PoissonRestrictionLaw
import Theorems.Thm_Kyprianou_ch02PoissonRestrictionIndependentCounts
import Theorems.Thm_Kyprianou_ch02PoissonDisjointRegionSigmaIndep
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν) :
    (∀ (A B : Set (ℝ × ℝ)), MeasurableSet A → MeasurableSet B →
       LevyStochCalc.Poisson.referenceIntensity ν (A ∩ B) < ⊤ →
       P.map (fun ω => N.N ω (A ∩ B)) =
         LevyStochCalc.Poisson.poissonMeasureENN
           (LevyStochCalc.Poisson.referenceIntensity ν (A ∩ B)).toNNReal) ∧
    (∀ {ι : Type} [Countable ι]
       (A : ι → Set (ℝ × ℝ)) (B : Set (ℝ × ℝ)),
       MeasurableSet B →
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       (∀ i, A i ⊆ B) →
       ProbabilityTheory.iIndepFun
          (fun i (ω : Ω) => (N.N ω).restrict B (A i)) P) ∧
    (∀ (A B : Set (ℝ × ℝ)), MeasurableSet A →
      MeasurableSet B → Disjoint A B →
      ProbabilityTheory.Indep
        (⨆ C ∈ {C : Set (ℝ × ℝ) |
             C ⊆ A ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)
        (⨆ D ∈ {D : Set (ℝ × ℝ) |
             D ⊆ B ∧ MeasurableSet D},
          MeasurableSpace.comap (fun ω => N.N ω D) inferInstance)
        P) := by
  exact ⟨
    Kyprianou.ch02PoissonRestrictionLaw P ν N,
    Kyprianou.ch02PoissonRestrictionIndependentCounts P ν N,
    Kyprianou.ch02PoissonDisjointRegionSigmaIndep P ν N ⟩

