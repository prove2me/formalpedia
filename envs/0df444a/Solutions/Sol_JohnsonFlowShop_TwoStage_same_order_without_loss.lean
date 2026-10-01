-- Prove2me | solution 1 for JohnsonFlowShop.TwoStage.same_order_without_loss
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:06:04.779272+00:00
-- url     : https://prove2.me/submissions/8d80b6cc-2576-44c1-8dae-3ad0f9852768

import Definitions.Def_JohnsonFlowShop_Shared_makespan
import Definitions.Def_JohnsonFlowShop_TwoStage_IsFeasible
import Definitions.Def_JohnsonFlowShop_TwoStage_FollowsOrder
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart1
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart2
import Definitions.Def_JohnsonFlowShop_TwoStage_F
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.FinRange
section

open JohnsonFlowShop Shared TwoStage Finset
namespace CJohnson

theorem prefix_split {n : ℕ} (t : Fin n → ℝ) (k : Fin n) :
    (∑ i ∈ Finset.Iic k,t i) = (∑ i ∈ Finset.Iio k,t i)+t k := by
  have he : Finset.Iic k=insert k (Finset.Iio k) := by ext i; simp
  rw [he,Finset.sum_insert (by simp)]
  ring

theorem prefix_succ {n : ℕ} (t : Fin n → ℝ) (j : ℕ) (hj : j+1 < n) :
    (∑ i ∈ Finset.Iio (⟨j+1,hj⟩ : Fin n),t i) = ∑ i ∈ Finset.Iic (⟨j,by omega⟩ : Fin n),t i := by
  congr 1
  ext i
  simp only [Finset.mem_Iio,Finset.mem_Iic,Fin.lt_def,Fin.le_iff_val_le_val]
  omega

theorem C2_mono {n : ℕ} (A B : Fin n → ℝ) (hB : ∀ i,0 ≤ B i) (σ : Equiv.Perm (Fin n)) :
    Monotone (asapC2 A B σ) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [asapC2]
  split_ifs with hk
  · exact (le_max_right _ _).trans (le_add_of_nonneg_right (hB _))
  · exact le_rfl

theorem C2_nonneg {n : ℕ} (A B : Fin n → ℝ) (hB : ∀ i,0 ≤ B i) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    0 ≤ asapC2 A B σ k := (C2_mono A B hB σ (Nat.zero_le k))

theorem first_finish {n : ℕ} (A : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    asapStart1 A σ (σ k)+A (σ k) = ∑ i ∈ Finset.Iic k,A (σ i) := by
  simpa [asapStart1] using (prefix_split (fun i=>A (σ i)) k).symm

theorem second_finish {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    asapStart2 A B σ (σ k)+B (σ k)=asapC2 A B σ (k.val+1) := by
  simp [asapStart2,asapC2,k.isLt]

theorem asap_order {n : ℕ} (A B : Fin n → ℝ) (hA : ∀ i,0 ≤ A i) (hB : ∀ i,0 ≤ B i)
    (σ : Equiv.Perm (Fin n)) : FollowsOrder A B (asapStart1 A σ) (asapStart2 A B σ) σ := by
  intro k l hkl
  constructor
  · rw [first_finish]
    simp only [asapStart1,Equiv.symm_apply_apply]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      exact Finset.mem_Iio.mpr (lt_of_le_of_lt (Finset.mem_Iic.mp hi) hkl)
    · intro i _ _
      exact hA _
  · rw [second_finish]
    exact (C2_mono A B hB σ (by change k.val+1 ≤ l.val; omega)).trans
      (by simp only [asapStart2,Equiv.symm_apply_apply]; exact le_max_right _ _)

theorem asap_feasible {n : ℕ} (A B : Fin n → ℝ) (hA : ∀ i,0 ≤ A i) (hB : ∀ i,0 ≤ B i)
    (σ : Equiv.Perm (Fin n)) : IsFeasible A B (asapStart1 A σ) (asapStart2 A B σ) := by
  have ho := asap_order A B hA hB σ
  refine ⟨fun i => Finset.sum_nonneg (fun k _ => hA _),?_,?_,?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne (show σ.symm i ≠ σ.symm j from fun h=>hij (σ.symm.injective h)) with h|h
    · exact Or.inl (by simpa using (ho _ _ h).1)
    · exact Or.inr (by simpa using (ho _ _ h).1)
  · intro i j hij
    rcases lt_or_gt_of_ne (show σ.symm i ≠ σ.symm j from fun h=>hij (σ.symm.injective h)) with h|h
    · exact Or.inl (by simpa using (ho _ _ h).2)
    · exact Or.inr (by simpa using (ho _ _ h).2)
  · intro i
    have h := first_finish A σ (σ.symm i)
    simp only [Equiv.apply_symm_apply] at h
    rw [h]
    exact le_max_left _ _

theorem ordered_prefix_bound {n : ℕ} (t s : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (hs : ∀ i,0 ≤ s i) (ho : ∀ k l : Fin n,k < l → s (σ k)+t (σ k) ≤ s (σ l))
    (j : ℕ) (hj : j < n) :
    (∑ i ∈ Finset.Iic (⟨j,hj⟩ : Fin n),t (σ i)) ≤ s (σ ⟨j,hj⟩)+t (σ ⟨j,hj⟩) := by
  induction j with
  | zero =>
    have he : Finset.Iic (⟨0,hj⟩ : Fin n)={⟨0,hj⟩} := by
      ext i
      simp only [Finset.mem_Iic,Finset.mem_singleton,Fin.ext_iff,Fin.le_iff_val_le_val]
      omega
    rw [he,Finset.sum_singleton]
    linarith [hs (σ ⟨0,hj⟩)]
  | succ j ih =>
    rw [prefix_split, prefix_succ (fun i=>t (σ i)) j hj]
    exact add_le_add ((ih (by omega)).trans (ho ⟨j,by omega⟩ ⟨j+1,hj⟩ (by simp))) le_rfl

theorem C2_before_bound {n : ℕ} (A B : Fin n → ℝ) (hA : ∀ i,0 ≤ A i)
    (σ : Equiv.Perm (Fin n)) (s1 s2 : Fin n → ℝ) (hs : IsFeasible A B s1 s2)
    (ho : FollowsOrder A B s1 s2 σ) (j : ℕ) (hj : j < n) : asapC2 A B σ j ≤ s2 (σ ⟨j,hj⟩) := by
  have hs2 : ∀ i,0 ≤ s2 i := fun i => (add_nonneg (hs.1 i) (hA i)).trans (hs.2.2.2 i)
  induction j with
  | zero => exact hs2 _
  | succ j ih =>
    rw [asapC2, dif_pos (by omega)]
    apply le_trans _ (ho ⟨j,by omega⟩ ⟨j+1,hj⟩ (by simp)).2
    apply add_le_add _ le_rfl
    apply max_le
    · exact (ordered_prefix_bound A s1 σ hs.1 (fun k l h => (ho k l h).1) j (by omega)).trans (hs.2.2.2 _)
    · exact ih (by omega)

theorem asap_start2_le {n : ℕ} (A B : Fin n → ℝ) (hA : ∀ i,0 ≤ A i)
    (σ : Equiv.Perm (Fin n)) (s1 s2 : Fin n → ℝ) (hs : IsFeasible A B s1 s2)
    (ho : FollowsOrder A B s1 s2 σ) : ∀ i,asapStart2 A B σ i ≤ s2 i := by
  intro i
  unfold asapStart2
  apply max_le
  · simpa using (ordered_prefix_bound A s1 σ hs.1 (fun k l h => (ho k l h).1)
      (σ.symm i).val (σ.symm i).isLt).trans (hs.2.2.2 (σ (σ.symm i)))
  · simpa using C2_before_bound A B hA σ s1 s2 hs ho (σ.symm i).val (σ.symm i).isLt

theorem makespan_mono {n : ℕ} (B s t : Fin n → ℝ) (h : ∀ i,s i ≤ t i) : makespan B s ≤ makespan B t := by
  apply (Finset.fold_max_le _).mpr
  constructor
  · exact (Finset.le_fold_max _).mpr (Or.inl le_rfl)
  · intro i hi
    exact (Finset.le_fold_max _).mpr (Or.inr ⟨i,hi,add_le_add (h i) le_rfl⟩)

theorem asap_optimal {n : ℕ} (A B : Fin n → ℝ) (hA : ∀ i,0 < A i) (hB : ∀ i,0 < B i)
    (σ : Equiv.Perm (Fin n)) :
    IsFeasible A B (asapStart1 A σ) (asapStart2 A B σ) ∧
      FollowsOrder A B (asapStart1 A σ) (asapStart2 A B σ) σ ∧
      ∀ s1 s2 : Fin n → ℝ,IsFeasible A B s1 s2 → FollowsOrder A B s1 s2 σ →
        makespan B (asapStart2 A B σ) ≤ makespan B s2 := by
  refine ⟨asap_feasible A B (fun i=>(hA i).le) (fun i=>(hB i).le) σ,
    asap_order A B (fun i=>(hA i).le) (fun i=>(hB i).le) σ,?_⟩
  intro s1 s2 hs ho
  exact makespan_mono B _ _ (asap_start2_le A B (fun i=>(hA i).le) σ s1 s2 hs ho)

end CJohnson
end

section

open JohnsonFlowShop Shared TwoStage Finset
namespace CJohnson

theorem sorted_perm {n : ℕ} (s : Fin n → ℝ) : ∃ σ : Equiv.Perm (Fin n),Monotone (s ∘ σ) := by
  classical
  let l := (List.finRange n).mergeSort (fun i j=>decide (s i ≤ s j))
  have hp : l.Perm (List.finRange n) := List.mergeSort_perm _ _
  have hlen : l.length=n := by simpa using hp.length_eq
  have hnd : l.Nodup := hp.nodup_iff.mpr (List.nodup_finRange n)
  have hmem : ∀ j : Fin n,j∈l := fun j=>hp.mem_iff.mpr (List.mem_finRange j)
  have hsort : l.Pairwise (fun i j=>s i ≤ s j) := by apply List.pairwise_mergeSort'
  let σ : Fin n ≃ Fin n := (finCongr hlen.symm).trans (hnd.getEquivOfForallMemList l hmem)
  refine ⟨σ,?_⟩
  intro i j hij
  rcases eq_or_lt_of_le hij with he|he
  · subst j;exact le_rfl
  · exact hsort.rel_get_of_lt he

theorem packing_bound {ι : Type*} [DecidableEq ι] (t s : ι → ℝ)
    (ht : ∀ i,0 < t i) (hs : ∀ i,0 ≤ s i)
    (hsep : ∀ i j,i≠j → s i+t i ≤ s j ∨ s j+t j ≤ s i)
    (K : Finset ι) (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ i∈K,s i+t i ≤ c) :
    (∑ i∈K,t i) ≤ c := by
  classical
  induction K using Finset.strongInductionOn generalizing c with
  | _ K ih =>
    by_cases hne : K.Nonempty
    · obtain ⟨j,hj,hmax⟩ := Finset.exists_mem_eq_sup' hne s
      have hsj : ∀ i∈K,s i ≤ s j := by
        intro i hi
        rw [←hmax]
        exact Finset.le_sup' _ hi
      have hsum := ih (K.erase j) (Finset.erase_ssubset hj) (s j) (hs j) (by
        intro i hi
        rcases hsep i j (Finset.ne_of_mem_erase hi) with h|h
        · exact h
        · have hh := hsj i (Finset.mem_of_mem_erase hi)
          linarith [ht j])
      rw [←Finset.add_sum_erase K t hj]
      linarith [hbound j hj]
    · have he : K=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simpa [he] using hc

theorem asap_le_of_prefix {n : ℕ} (A B s : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (hs : ∀ i,0 ≤ s i) (ho : ∀ k l : Fin n,k < l → s (σ k)+B (σ k) ≤ s (σ l))
    (hprefix : ∀ k : Fin n,(∑ i∈Finset.Iic k,A (σ i)) ≤ s (σ k)) :
    ∀ i,asapStart2 A B σ i ≤ s i := by
  have hbefore (j : ℕ) (hj : j < n) : asapC2 A B σ j ≤ s (σ ⟨j,hj⟩) := by
    induction j with
    | zero => exact hs _
    | succ j ih =>
      rw [asapC2,dif_pos (by omega)]
      exact (add_le_add (max_le (hprefix ⟨j,by omega⟩) (ih (by omega))) le_rfl).trans
        (ho ⟨j,by omega⟩ ⟨j+1,hj⟩ (by simp))
  intro i
  unfold asapStart2
  apply max_le
  · simpa using hprefix (σ.symm i)
  · simpa using hbefore (σ.symm i).val (σ.symm i).isLt

theorem same_order {n : ℕ} (A B : Fin n → ℝ) (hA : ∀ i,0 < A i) (hB : ∀ i,0 < B i)
    (s1 s2 : Fin n → ℝ) (hf : IsFeasible A B s1 s2) :
    ∃ (σ : Equiv.Perm (Fin n)) (t1 t2 : Fin n → ℝ),IsFeasible A B t1 t2 ∧
      FollowsOrder A B t1 t2 σ ∧ makespan B t2 ≤ makespan B s2 := by
  obtain ⟨σ,hσ⟩ := sorted_perm s2
  have hnon : ∀ i,0 ≤ s2 i := fun i=>(add_nonneg (hf.1 i) (hA i).le).trans (hf.2.2.2 i)
  have ho : ∀ k l : Fin n,k < l → s2 (σ k)+B (σ k) ≤ s2 (σ l) := by
    intro k l hkl
    have hne : σ k ≠ σ l := fun h => (ne_of_lt hkl) (σ.injective h)
    rcases hf.2.2.1 _ _ hne with h|h
    · exact h
    · have hh := hσ hkl.le
      dsimp only [Function.comp_apply] at hh
      linarith [hB (σ l)]
  have hpre : ∀ k : Fin n,(∑ i∈Finset.Iic k,A (σ i)) ≤ s2 (σ k) := by
    intro k
    refine packing_bound (fun i=>A (σ i)) (fun i=>s1 (σ i)) (fun i=>hA _) (fun i=>hf.1 _)
      (fun i j hij => hf.2.1 _ _ (fun h => hij (σ.injective h))) (Finset.Iic k) _ (hnon _) ?_
    intro i hi
    exact (hf.2.2.2 _).trans (hσ (Finset.mem_Iic.mp hi))
  refine ⟨σ,asapStart1 A σ,asapStart2 A B σ,asap_feasible A B (fun i=>(hA i).le)
    (fun i=>(hB i).le) σ,asap_order A B (fun i=>(hA i).le) (fun i=>(hB i).le) σ,?_⟩
  exact makespan_mono B _ _ (asap_le_of_prefix A B s2 σ hnon ho hpre)

end CJohnson
end

open JohnsonFlowShop TwoStage


/-- Lemma 1 (Johnson 1954, p. 61): every feasible two-machine schedule can be replaced, without
increasing the total elapsed time, by a feasible schedule that processes the items in one
common order `σ` on both machines. -/
theorem solution {n : ℕ} (A B : Fin n → ℝ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i)
    (s₁ s₂ : Fin n → ℝ) (hs : IsFeasible A B s₁ s₂) :
    ∃ (σ : Equiv.Perm (Fin n)) (t₁ t₂ : Fin n → ℝ),
      IsFeasible A B t₁ t₂ ∧ FollowsOrder A B t₁ t₂ σ ∧ Shared.makespan B t₂ ≤ Shared.makespan B s₂ := by
  exact CJohnson.same_order A B hA hB s₁ s₂ hs


