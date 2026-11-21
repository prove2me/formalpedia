-- Prove2me | solution 1 for LevyStochCalc.Poisson.count_singleton_ne_zero_of_restrict_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:20:43.261178+00:00
-- url     : https://prove2.me/submissions/0dee1189-a172-4140-a027-af7b600d9fff

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F002
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Singleton

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end Singleton

section IntegerValued

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end IntegerValued

section Positivity

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end Positivity

section AtomTimes

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end AtomTimes

section Chain

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end Chain

section AtomFinset

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end AtomFinset

section AtomPoint

variable [MeasurableSingletonClass E]
variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)




theorem _root_.solution {T : ℝ} {ω : Ω} {p : ℝ × E}
    (hp : ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} ≠ 0) :
    (0 < p.1 ∧ p.1 ≤ T) ∧ N.N ω (({p.1} : Set ℝ) ×ˢ A) ≠ 0 := by
  rw [Measure.restrict_apply (MeasurableSet.singleton p)] at hp
  have hm : p ∈ Set.Ioc (0 : ℝ) T ×ˢ A := by
    by_contra hn
    have he : ({p} : Set (ℝ × E)) ∩ (Set.Ioc (0 : ℝ) T ×ˢ A) = ∅ := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl, h⟩
      exact hn h
    exact hp (by rw [he, measure_empty])
  refine ⟨hm.1, ?_⟩
  have hsub : ({p} : Set (ℝ × E)) ∩ (Set.Ioc (0 : ℝ) T ×ˢ A) ⊆
      ({p.1} : Set ℝ) ×ˢ A := by
    rintro q ⟨hq, hmem⟩
    rcases Set.mem_singleton_iff.mp hq with rfl
    exact ⟨rfl, hmem.2⟩
  intro hz
  exact hp (le_antisymm ((measure_mono hsub).trans_eq hz) bot_le)
