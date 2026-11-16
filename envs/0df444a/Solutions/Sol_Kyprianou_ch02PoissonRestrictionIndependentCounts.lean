-- Prove2me | solution 1 for Kyprianou.ch02PoissonRestrictionIndependentCounts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:50:56.781419+00:00
-- url     : https://prove2.me/submissions/4343a058-c489-48c0-a6f2-8d778b04f0ac

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν) :
    (∀ {ι : Type} [Countable ι]
       (A : ι → Set (ℝ × ℝ)) (B : Set (ℝ × ℝ)),
       MeasurableSet B →
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       (∀ i, A i ⊆ B) →
       ProbabilityTheory.iIndepFun
          (fun i (ω : Ω) => (N.N ω).restrict B (A i)) P) := by
  intro ι inst A B hB hA hdisj hsubset
  have heq :
      (fun i (ω : Ω) => (N.N ω).restrict B (A i)) =
      (fun i (ω : Ω) => N.N ω (A i)) := by
    funext i ω
    rw [Measure.restrict_apply (hA i)]
    rw [Set.inter_eq_self_of_subset_left (hsubset i)]
  rw [heq]
  exact N.independent_disjoint A hA hdisj

