-- Prove2me | solution 1 for JohnsonFlowShop.TwoStage.makespan_asap_eq
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:04:26.316143+00:00
-- url     : https://prove2.me/submissions/ab8a088f-86db-41e2-baf2-815fee4864e1

import Definitions.Def_JohnsonFlowShop_Shared_makespan
import Definitions.Def_JohnsonFlowShop_TwoStage_IsFeasible
import Definitions.Def_JohnsonFlowShop_TwoStage_FollowsOrder
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart1
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart2
import Definitions.Def_JohnsonFlowShop_TwoStage_F
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

theorem Iic_succ {n : ℕ} (j : ℕ) (hj : j+1 < n) :
    Finset.Iic (⟨j+1,hj⟩ : Fin n) = insert ⟨j+1,hj⟩ (Finset.Iic ⟨j,by omega⟩) := by
  ext i
  simp only [Finset.mem_Iic,Finset.mem_insert,Fin.ext_iff,Fin.le_iff_val_le_val]
  omega

theorem C2_formula {n : ℕ} (A B : Fin n → ℝ) (hA : ∀ i,0 ≤ A i) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j < n) :
    asapC2 A B σ (j+1) = (∑ i ∈ Finset.Iic (⟨j,hj⟩ : Fin n),B (σ i))+
      (Finset.Iic (⟨j,hj⟩ : Fin n)).sup' Finset.nonempty_Iic (K A B σ) := by
  induction j with
  | zero =>
    have he : Finset.Iic (⟨0,hj⟩ : Fin n)={⟨0,hj⟩} := by
      ext i
      simp only [Finset.mem_Iic,Finset.mem_singleton,Fin.ext_iff,Fin.le_iff_val_le_val]
      omega
    have he' : Finset.Iio (⟨0,hj⟩ : Fin n)=∅ := by
      ext i
      simp only [Finset.mem_Iio,Finset.notMem_empty,iff_false,Fin.lt_def]
      omega
    simp only [asapC2,dif_pos hj,he,Finset.sum_singleton,Finset.sup'_singleton,K,he',Finset.sum_empty,sub_zero]
    rw [max_eq_left (hA _)]
    ring
  | succ j ih =>
    rw [asapC2,dif_pos hj,ih (by omega)]
    have hsup : (Finset.Iic (⟨j+1,hj⟩ : Fin n)).sup' Finset.nonempty_Iic (K A B σ) =
        max (K A B σ ⟨j+1,hj⟩) ((Finset.Iic (⟨j,by omega⟩ : Fin n)).sup' Finset.nonempty_Iic (K A B σ)) := by
      simp only [Iic_succ j hj,Finset.sup'_insert Finset.nonempty_Iic]
    rw [hsup,prefix_split (fun i=>B (σ i)) ⟨j+1,hj⟩,prefix_succ (fun i=>B (σ i)) j hj]
    have hk : K A B σ ⟨j+1,hj⟩ = (∑ i ∈ Finset.Iic (⟨j+1,hj⟩ : Fin n),A (σ i))-
        ∑ i ∈ Finset.Iic (⟨j,by omega⟩ : Fin n),B (σ i) := by
      unfold K
      rw [prefix_succ (fun i=>B (σ i)) j hj]
    rw [hk]
    simp only [max_def]
    split_ifs <;> linarith

theorem makespan_eq_C2 {n : ℕ} [NeZero n] (A B : Fin n → ℝ) (hB : ∀ i,0 ≤ B i)
    (σ : Equiv.Perm (Fin n)) : makespan B (asapStart2 A B σ)=asapC2 A B σ n := by
  apply le_antisymm
  · apply (Finset.fold_max_le _).mpr
    refine ⟨C2_nonneg A B hB σ n,?_⟩
    intro i hi
    have hh := second_finish A B σ (σ.symm i)
    simp only [Equiv.apply_symm_apply] at hh
    rw [hh]
    exact C2_mono A B hB σ (by have := (σ.symm i).isLt; omega)
  · have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    let k : Fin n := ⟨n-1,by omega⟩
    have hh := second_finish A B σ k
    have hk : k.val+1=n := by dsimp [k]; omega
    rw [hk] at hh
    apply (Finset.le_fold_max _).mpr
    exact Or.inr ⟨σ k,Finset.mem_univ _,hh.ge⟩

theorem makespan_formula {n : ℕ} [NeZero n] (A B : Fin n → ℝ) (hA : ∀ i,0 < A i)
    (hB : ∀ i,0 < B i) (σ : Equiv.Perm (Fin n)) :
    makespan B (asapStart2 A B σ) = ∑ i,B i+F A B σ := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let k : Fin n := ⟨n-1,by omega⟩
  have hk : k.val+1=n := by dsimp [k]; omega
  have he : Finset.Iic k=Finset.univ := by
    ext i
    simp only [Finset.mem_Iic,Finset.mem_univ,iff_true]
    change i.val ≤ n-1
    have := i.isLt
    omega
  have hh := C2_formula A B (fun i=>(hA i).le) σ k.val k.isLt
  rw [hk] at hh
  change asapC2 A B σ n = (∑ i ∈ Finset.Iic k,B (σ i))+(Finset.Iic k).sup' Finset.nonempty_Iic (K A B σ) at hh
  simp only [he] at hh
  rw [Equiv.sum_comp σ B] at hh
  rw [makespan_eq_C2 A B (fun i=>(hB i).le) σ]
  exact hh

end CJohnson
end

open JohnsonFlowShop TwoStage


/-- p. 62, display "In general": for the as-soon-as-possible schedule of the order `σ`, the total
idle time of machine 2 is `max_u K_u`; equivalently the total elapsed time is
`∑_i B_i + max_u K_u = ∑_i B_i + F(σ)`. -/
theorem solution {n : ℕ} [NeZero n] (A B : Fin n → ℝ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (σ : Equiv.Perm (Fin n)) :
    Shared.makespan B (asapStart2 A B σ) = ∑ i, B i + F A B σ := by
  exact CJohnson.makespan_formula A B hA hB σ


