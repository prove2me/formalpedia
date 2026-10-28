-- Prove2me | solution 1 for HyperMatchDelay.Batching.batch_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:00:26.853484+00:00
-- url     : https://prove2.me/submissions/244a2a4c-a0ba-4f51-9d96-3c923e6d68fa

import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace Aux_HyperMatchDelay_batch_decomposition
open HyperMatchDelay.Batching

theorem mem_window {n d z : ℕ} {i : ℤ} {v : ℕ} :
    v ∈ window n d z i ↔ v ∈ Finset.Icc 1 n ∧
      ((z : ℤ) + i * d ≤ (v : ℤ) ∧ (v : ℤ) ≤ (z : ℤ) + (i + 1) * d - 1) := by
  unfold window; exact Finset.mem_filter

theorem win_unique {n d z : ℕ} (hd : 1 ≤ d) {v : ℕ} {i j : ℤ}
    (hi : v ∈ window n d z i) (hj : v ∈ window n d z j) : i = j := by
  obtain ⟨-, hi1, hi2⟩ := mem_window.mp hi
  obtain ⟨-, hj1, hj2⟩ := mem_window.mp hj
  have hd0 : (0 : ℤ) < d := by exact_mod_cast hd
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : (i + 1) * (d : ℤ) ≤ j * d := mul_le_mul_of_nonneg_right (by omega) hd0.le
    linarith
  · have : (j + 1) * (d : ℤ) ≤ i * d := mul_le_mul_of_nonneg_right (by omega) hd0.le
    linarith

theorem foldl_greedy (l : List (Finset ℕ)) (M0 : Finset (Finset ℕ))
    (h0 : (M0 : Set (Finset ℕ)).PairwiseDisjoint id) :
    ((l.foldl greedyStep M0 : Finset (Finset ℕ)) : Set (Finset ℕ)).PairwiseDisjoint id ∧
      l.foldl greedyStep M0 ⊆ M0 ∪ l.toFinset := by
  induction l generalizing M0 with
  | nil => simpa using h0
  | cons a l ih =>
    simp only [List.foldl_cons]
    have hstep : ((greedyStep M0 a : Finset (Finset ℕ)) : Set (Finset ℕ)).PairwiseDisjoint id ∧
        greedyStep M0 a ⊆ insert a M0 := by
      unfold greedyStep
      split_ifs with h
      · refine ⟨?_, le_rfl⟩
        rw [Finset.coe_insert]
        exact h0.insert fun f hf _ => h f hf
      · exact ⟨h0, Finset.subset_insert _ _⟩
    obtain ⟨ih1, ih2⟩ := ih (greedyStep M0 a) hstep.1
    refine ⟨ih1, ih2.trans ?_⟩
    intro e he
    rcases Finset.mem_union.mp he with h | h
    · rcases Finset.mem_insert.mp (hstep.2 h) with h' | h'
      · subst h'; simp
      · exact Finset.mem_union_left _ h'
    · exact Finset.mem_union_right _ (by simp [List.mem_toFinset.mp h])

theorem greedy_spec (w : Finset ℕ → ℝ) (σ : Finset (Finset ℕ) → List (Finset ℕ))
    (hσ : IsSortedOrder w σ) (S : Finset (Finset ℕ)) :
    ((greedy σ S : Finset (Finset ℕ)) : Set (Finset ℕ)).PairwiseDisjoint id ∧ greedy σ S ⊆ S := by
  unfold greedy
  obtain ⟨h1, h2⟩ := foldl_greedy (σ S) ∅ (by simp)
  refine ⟨h1, h2.trans ?_⟩
  rw [Finset.empty_union, (hσ S).2.1]

theorem dkg_spec (w : Finset ℕ → ℝ) (σ : Finset (Finset ℕ) → List (Finset ℕ))
    (hσ : IsSortedOrder w σ) (k : ℕ) (B : Finset ℕ) (EB : Finset (Finset ℕ)) :
    ((depthKGreedy σ w k B EB : Finset (Finset ℕ)) : Set (Finset ℕ)).PairwiseDisjoint id ∧
      depthKGreedy σ w k B EB ⊆ EB := by
  classical
  set M := depthKChoice σ w k B EB with hM
  have hMmem : M ∈ restrictedMatchings EB (firstK B k) (lastK B k) := by
    rw [hM]; unfold depthKChoice
    exact (Classical.choose_spec (Finset.exists_max_image
      (restrictedMatchings EB (firstK B k) (lastK B k))
      (fun M => weight w (M ∪ greedyAvoiding σ EB M))
      ⟨∅, empty_mem_restrictedMatchings EB _ _⟩)).1
  unfold restrictedMatchings at hMmem
  obtain ⟨-, ⟨hMsub, hMdisj⟩, -⟩ := Finset.mem_filter.mp hMmem
  obtain ⟨hGdisj, hGsub⟩ := greedy_spec w σ hσ (EB.filter (fun e => Disjoint e (vertices M)))
  unfold depthKGreedy greedyAvoiding
  rw [← hM]
  refine ⟨?_, Finset.union_subset hMsub (hGsub.trans (Finset.filter_subset _ _))⟩
  rw [Finset.coe_union, Set.pairwiseDisjoint_union]
  refine ⟨hMdisj, hGdisj, fun e he f hf _ => ?_⟩
  have hf' := (Finset.mem_filter.mp (hGsub hf)).2
  have hev : e ⊆ vertices M := by
    unfold vertices; exact Finset.subset_biUnion_of_mem id he
  exact (hf'.mono_right hev).symm

end Aux_HyperMatchDelay_batch_decomposition

open HyperMatchDelay.Batching Aux_HyperMatchDelay_batch_decomposition in
theorem solution (n d k : ℕ) (hd : 1 ≤ d) (E : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ) (hE : IsShareability n d k E w)
    (σ : Finset (Finset ℕ) → List (Finset ℕ)) (hσ : IsSortedOrder w σ) (z : ℕ) (hz : z < d) :
    (∀ v ∈ Finset.Icc 1 n, ∃! i, i ∈ batchIndices n d ∧ v ∈ window n d z i) ∧
    ((batchIndices n d : Set ℤ).PairwiseDisjoint (fun i => batchEdges E n d z i)) ∧
    IsMatching E (randomizedBatching σ w n d k E z) ∧
    (∀ e ∈ randomizedBatching σ w n d k E z,
      ∃ i ∈ batchIndices n d, e ⊆ window n d z i) ∧
    weight w (randomizedBatching σ w n d k E z) =
      ∑ i ∈ batchIndices n d,
        weight w (depthKGreedy σ w k (window n d z i) (batchEdges E n d z i)) := by
  classical
  have hd0 : (0 : ℤ) < d := by exact_mod_cast hd
  -- (a)
  have hA : ∀ v ∈ Finset.Icc 1 n, ∃! i, i ∈ batchIndices n d ∧ v ∈ window n d z i := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := Finset.mem_Icc.mp hv
    set a : ℤ := (v : ℤ) - z with ha
    have hdm := Int.mul_ediv_add_emod a d
    have hm0 := Int.emod_nonneg a hd0.ne'
    have hmd := Int.emod_lt_of_pos a hd0
    have hvz : (1 : ℤ) - z ≤ a := by rw [ha]; push_cast; omega
    have hzd : (z : ℤ) < d := by exact_mod_cast hz
    have hvn : a ≤ n := by rw [ha]; push_cast; omega
    refine ⟨a / d, ⟨?_, ?_⟩, ?_⟩
    · unfold batchIndices
      rw [Finset.mem_Icc]
      constructor
      · by_contra h
        push_neg at h
        have : a / d ≤ -2 := by omega
        have : (a / d) * (d : ℤ) ≤ -2 * d := mul_le_mul_of_nonneg_right this hd0.le
        nlinarith
      · exact Int.ediv_le_ediv hd0 hvn
    · rw [mem_window]
      refine ⟨hv, ?_, ?_⟩
      · nlinarith
      · nlinarith
    · rintro j ⟨-, hj⟩
      have hi : v ∈ window n d z (a / d) := by
        rw [mem_window]
        refine ⟨hv, ?_, ?_⟩
        · nlinarith
        · nlinarith
      exact win_unique hd hj hi
  -- (b)
  have hB : (batchIndices n d : Set ℤ).PairwiseDisjoint (fun i => batchEdges E n d z i) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro e he1 he2
    unfold batchEdges at he1 he2
    obtain ⟨heE, hei⟩ := Finset.mem_filter.mp he1
    obtain ⟨-, hej⟩ := Finset.mem_filter.mp he2
    obtain ⟨v, hv⟩ := (hE e heE).2.1
    exact hij (win_unique hd (hei hv) (hej hv))
  set DG : ℤ → Finset (Finset ℕ) := fun i =>
    depthKGreedy σ w k (window n d z i) (batchEdges E n d z i) with hDG
  have hDGsub : ∀ i, DG i ⊆ batchEdges E n d z i := fun i => (dkg_spec w σ hσ k _ _).2
  have hDGdisj : ∀ i, ((DG i : Finset (Finset ℕ)) : Set (Finset ℕ)).PairwiseDisjoint id :=
    fun i => (dkg_spec w σ hσ k _ _).1
  have hRB : randomizedBatching σ w n d k E z = (batchIndices n d).biUnion DG := rfl
  have hwin : ∀ i, ∀ e ∈ DG i, e ⊆ window n d z i := fun i e he =>
    (Finset.mem_filter.mp (hDGsub i he)).2
  have hEmem : ∀ i, ∀ e ∈ DG i, e ∈ E := fun i e he =>
    (Finset.mem_filter.mp (hDGsub i he)).1
  have hDGpd : (batchIndices n d : Set ℤ).PairwiseDisjoint DG := by
    intro i hi j hj hij
    exact (hB hi hj hij).mono (hDGsub i) (hDGsub j)
  refine ⟨hA, hB, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro e he
    rw [hRB] at he
    obtain ⟨i, -, hei⟩ := Finset.mem_biUnion.mp he
    exact hEmem i e hei
  · rw [hRB]
    intro e he f hf hne
    obtain ⟨i, -, hei⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp he)
    obtain ⟨j, -, hfj⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hf)
    by_cases hij : i = j
    · subst hij
      exact hDGdisj i (Finset.mem_coe.mpr hei) (Finset.mem_coe.mpr hfj) hne
    · rw [Function.onFun, id, id, Finset.disjoint_left]
      intro v hve hvf
      exact hij (win_unique hd (hwin i e hei hve) (hwin j f hfj hvf))
  · intro e he
    rw [hRB] at he
    obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
    exact ⟨i, hi, hwin i e hei⟩
  · rw [hRB]
    unfold weight
    rw [Finset.sum_biUnion hDGpd]
