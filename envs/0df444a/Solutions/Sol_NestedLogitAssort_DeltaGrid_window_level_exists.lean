-- Prove2me | solution 1 for NestedLogitAssort.DeltaGrid.window_level_exists
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:54:39.762746+00:00
-- url     : https://prove2.me/submissions/0b33636c-e88c-4a20-8cdc-2bc612508acb

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_Window
import Definitions.Def_NestedLogitAssort_DeltaGrid_InLevelRange

open NestedLogitAssort.DeltaGrid in
theorem solution {M : Type*} {n : ℕ} (I : Instance M n) (i : M)
    (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j) (δ : ℝ) (hδ : 1 < δ)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hpos : 0 < V I i S) :
    ∃ l : ℤ, InLevelRange I δ i l ∧ Window I δ i l S := by
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ioc_zpow hpos hδ
  have e : m + 1 - 1 = m := by ring
  obtain ⟨j, hj⟩ := hS
  have hjS : I.w0 i + I.v i j ≤ V I i S := by
    unfold V
    have := Finset.single_le_sum (f := fun j => I.v i j) (fun j _ => hv j) hj
    linarith
  have hSU : V I i S ≤ I.w0 i + ∑ j, I.v i j := by
    unfold V
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => I.v i j)
      (Finset.subset_univ S) (fun j _ _ => hv j)
    linarith
  refine ⟨m + 1, ⟨⟨j, le_trans hjS hm2⟩, ?_⟩, ?_, hm2⟩
  · rw [e]; linarith
  · rw [e]; exact hm1.le
