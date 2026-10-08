-- Prove2me | solution 1 for HallReps.CDR.theorem2_distinct_classes
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:24:51.619367+00:00
-- url     : https://prove2.me/submissions/e40db342-c8d5-494a-b494-d9787cffbd7a

import Mathlib
import Definitions.Def_HallReps_CDR_System
import Theorems.Thm_HallReps_CDR_theorem1_hall

set_option autoImplicit false

open HallReps.CDR

theorem solution {ι α κ : Type*} [Finite ι] (T : ι → Set α)
    (cls : α → κ)
    (h : ∀ s : Finset ι, (s.card : ℕ∞) ≤ (cls '' ⋃ i ∈ s, T i).encard) :
    ∃ a : ι → α, Function.Injective (cls ∘ a) ∧ ∀ i, a i ∈ T i := by
  -- apply Theorem 1 to the system of class sets `cls '' T i`
  have hH : HallCondition (fun i => cls '' T i) := by
    intro s
    have : (⋃ i ∈ s, cls '' T i) = cls '' ⋃ i ∈ s, T i := by
      simp [Set.image_iUnion]
    rw [this]
    exact h s
  obtain ⟨b, hbinj, hbmem⟩ := HallReps.CDR.theorem1_hall (fun i => cls '' T i) hH
  choose a ha hab using hbmem
  refine ⟨a, ?_, ha⟩
  have : cls ∘ a = b := funext hab
  rw [this]
  exact hbinj

#print axioms solution
