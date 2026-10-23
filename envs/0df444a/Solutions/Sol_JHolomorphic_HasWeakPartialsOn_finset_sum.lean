-- Prove2me | solution 1 for JHolomorphic.HasWeakPartialsOn.finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T11:44:07.346745+00:00
-- url     : https://prove2.me/submissions/af452cf3-52e7-41db-a8d1-4d5c43c2dad2

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_add



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- Weak partials of a finite sum. -/
theorem HasWeakPartialsOn.finset_sum_aux {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℂ} (s : Finset ι) {u us ut : ι → ℂ → E}
    (h : ∀ i ∈ s, HasWeakPartialsOn U (u i) (us i) (ut i))
    (hint : ∀ i ∈ s, ∀ K ⊆ U, IsCompact K →
      IntegrableOn (u i) K ∧ IntegrableOn (us i) K ∧ IntegrableOn (ut i) K) :
    HasWeakPartialsOn U (fun z => ∑ i ∈ s, u i z) (fun z => ∑ i ∈ s, us i z)
      (fun z => ∑ i ∈ s, ut i z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro φ _ _ _
    simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    refine HasWeakPartialsOn.add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
        (fun i hi => hint i (Finset.mem_insert_of_mem hi)))
      (hint a (Finset.mem_insert_self a s)) ?_
    intro K hK hKc
    refine ⟨integrable_finset_sum _ fun i hi => ?_, integrable_finset_sum _ fun i hi => ?_,
      integrable_finset_sum _ fun i hi => ?_⟩
    · exact (hint i (Finset.mem_insert_of_mem hi) K hK hKc).1
    · exact (hint i (Finset.mem_insert_of_mem hi) K hK hKc).2.1
    · exact (hint i (Finset.mem_insert_of_mem hi) K hK hKc).2.2

end JHolomorphic

open JHolomorphic JHolomorphic.HasWeakPartialsOn

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

theorem solution {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℂ} (s : Finset ι) {u us ut : ι → ℂ → E}
    (h : ∀ i ∈ s, HasWeakPartialsOn U (u i) (us i) (ut i))
    (hint : ∀ i ∈ s, ∀ K ⊆ U, IsCompact K →
      IntegrableOn (u i) K ∧ IntegrableOn (us i) K ∧ IntegrableOn (ut i) K) :
    HasWeakPartialsOn U (fun z => ∑ i ∈ s, u i z) (fun z => ∑ i ∈ s, us i z)
      (fun z => ∑ i ∈ s, ut i z) :=
  HasWeakPartialsOn.finset_sum_aux s h hint
