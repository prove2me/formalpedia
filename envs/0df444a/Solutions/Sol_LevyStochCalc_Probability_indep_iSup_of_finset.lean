-- Prove2me | solution 1 for LevyStochCalc.Probability.indep_iSup_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:45:09.768241+00:00
-- url     : https://prove2.me/submissions/471df4b8-f6eb-4c06-ae32-ba1f825f83a3

import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

theorem solution {ι : Type*} {m : ι → MeasurableSpace Ω} {m' : MeasurableSpace Ω}
    (h_le : ∀ i, m i ≤ mΩ) (h_le' : m' ≤ mΩ)
    (h : ∀ S : Finset ι, Indep (⨆ i ∈ S, m i) m' P) :
    Indep (⨆ i, m i) m' P := by
  classical
  have hd : Directed (· ≤ ·) (fun S : Finset ι => ⨆ i ∈ S, m i) := by
    intro S T
    exact ⟨S ∪ T, iSup₂_le fun i hi => le_iSup₂_of_le (f := fun j (_ : j ∈ S ∪ T) => m j) i
        (Finset.mem_union_left _ hi) le_rfl,
      iSup₂_le fun i hi => le_iSup₂_of_le (f := fun j (_ : j ∈ S ∪ T) => m j) i
        (Finset.mem_union_right _ hi) le_rfl⟩
  have heq : (⨆ S : Finset ι, ⨆ i ∈ S, m i) = ⨆ i, m i :=
    le_antisymm (iSup_le fun S => iSup₂_le fun i _ => le_iSup m i)
      (iSup_le fun i => le_iSup_of_le ({i} : Finset ι)
        (le_iSup₂_of_le (f := fun j (_ : j ∈ ({i} : Finset ι)) => m j) i
          (Finset.mem_singleton_self i) le_rfl))
  rw [← heq]
  exact indep_iSup_of_directed_le h (fun S => iSup₂_le fun i _ => h_le i) h_le' hd
