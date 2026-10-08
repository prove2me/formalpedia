-- Prove2me | solution 1 for KingmanSubadditive.Ulam.num_ascending_ge_choose
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:01:04.730778+00:00
-- url     : https://prove2.me/submissions/d3351f8e-b934-44b2-881b-5b7e2e8fb146

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations



namespace KingmanSubadditive.Ulam

lemma isAscendingOn_subset {n : ℕ} (σ : Equiv.Perm (Fin n)) {s t : Finset (Fin n)}
    (h : IsAscendingOn σ s) (hts : t ⊆ s) : IsAscendingOn σ t :=
  fun i hi j hj hij => h i (hts hi) j (hts hj) hij

lemma exists_ascending_card_eq_lis {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∃ s : Finset (Fin n), IsAscendingOn σ s ∧ s.card = lis σ := by
  classical
  have hne : ((Finset.univ : Finset (Finset (Fin n))).filter (fun s => IsAscendingOn σ s)).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i hi => absurd hi (Finset.notMem_empty _)⟩⟩
  obtain ⟨s, hs, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  refine ⟨s, (Finset.mem_filter.1 hs).2, ?_⟩
  unfold lis; exact hcard.symm

theorem num_ascending_ge_choose_core {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) (_hk : k ≤ lis σ) :
    (lis σ).choose k ≤ numAscending k σ := by
  classical
  obtain ⟨s, hs, hcard⟩ := exists_ascending_card_eq_lis σ
  unfold numAscending
  rw [← hcard, ← Finset.card_powersetCard]
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_powersetCard] at ht
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨⟨Finset.subset_univ _, ht.2⟩, isAscendingOn_subset σ hs ht.1⟩

end KingmanSubadditive.Ulam

open KingmanSubadditive.Ulam


theorem solution {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ lis σ) :
    (lis σ).choose k ≤ numAscending k σ := by
  exact num_ascending_ge_choose_core σ k hk
