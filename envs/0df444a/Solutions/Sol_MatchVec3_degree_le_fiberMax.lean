-- Prove2me | solution 1 for MatchVec3.degree_le_fiberMax
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:41:44.929199+00:00
-- url     : https://prove2.me/submissions/fe67aa1d-b6e1-4a3c-af4d-2943a3402aea

import Mathlib
import Definitions.Def_MatchVec3_fiberMax
import Definitions.Def_MatchVec3_maxDegree

open MatchVec3 in
theorem solution {m n K L : ℕ} (hL : 1 ≤ L) (U : Fin K → Fin n → ZMod m)
    (x : Fin n → ZMod m) :
    maxDegree (fiber U L x) ≤ fiberMax U (L - 1) := by
  unfold maxDegree
  apply Finset.sup_le
  intro i _
  by_cases hne : ((fiber U L x).filter (fun A => i ∈ A)).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp
  obtain ⟨A0, hA0⟩ := hne
  rw [Finset.mem_filter] at hA0
  obtain ⟨hA0f, hiA0⟩ := hA0
  unfold fiber at hA0f
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hA0f
  obtain ⟨⟨_, hcard⟩, hsum⟩ := hA0f
  have hB0card : (A0.erase i).card = L - 1 := by rw [Finset.card_erase_of_mem hiA0, hcard]
  have hB0sum : ∑ j ∈ A0.erase i, U j = x - U i := by
    rw [← hsum, ← Finset.sum_erase_add _ _ hiA0, add_sub_cancel_right]
  have hB0mem : A0.erase i ∈ Finset.powersetCard (L - 1) (Finset.univ : Finset (Fin K)) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hB0card⟩
  calc ((fiber U L x).filter (fun A => i ∈ A)).card
      ≤ (fiber U (L - 1) (x - U i)).card := by
        apply Finset.card_le_card_of_injOn (fun A => A.erase i)
        · intro A hA
          rw [Finset.mem_coe, Finset.mem_filter] at hA
          obtain ⟨hAf, hiA⟩ := hA
          unfold fiber at hAf
          rw [Finset.mem_filter, Finset.mem_powersetCard] at hAf
          obtain ⟨⟨_, hc⟩, hs⟩ := hAf
          rw [Finset.mem_coe]
          unfold fiber
          rw [Finset.mem_filter, Finset.mem_powersetCard]
          refine ⟨⟨Finset.subset_univ _, by rw [Finset.card_erase_of_mem hiA, hc]⟩, ?_⟩
          rw [← hs, ← Finset.sum_erase_add _ _ hiA, add_sub_cancel_right]
        · intro A hA B hB hAB
          rw [Finset.mem_coe, Finset.mem_filter] at hA hB
          simp only at hAB
          rw [← Finset.insert_erase hA.2, ← Finset.insert_erase hB.2, hAB]
    _ = (fiber U (L - 1) (∑ j ∈ A0.erase i, U j)).card := by rw [hB0sum]
    _ ≤ fiberMax U (L - 1) := by
        unfold fiberMax
        exact Finset.le_sup (f := fun A => (fiber U (L - 1) (∑ i ∈ A, U i)).card) hB0mem
