-- Prove2me | solution 1 for JohnsonFlowShop.ThreeStage.makespan_asap_eq
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:23:43.831975+00:00
-- url     : https://prove2.me/submissions/7dbfd696-e565-4e94-a270-2b539d7ee1c2

import Definitions.Def_JohnsonFlowShop_Shared_makespan
import Definitions.Def_JohnsonFlowShop_TwoStage_IsFeasible
import Definitions.Def_JohnsonFlowShop_TwoStage_FollowsOrder
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart1
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart2
import Definitions.Def_JohnsonFlowShop_TwoStage_F
import Definitions.Def_JohnsonFlowShop_ThreeStage_asapSchedule
import Definitions.Def_JohnsonFlowShop_ThreeStage_IsFeasible
import Definitions.Def_JohnsonFlowShop_ThreeStage_H
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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

section

open JohnsonFlowShop Shared Finset
namespace CJohnson
open ThreeStage

theorem done1_at {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (j : ℕ) (hj : j < n) :
    (asapDone A B C σ j).1 = ∑ i ∈ Finset.Iio (⟨j,hj⟩ : Fin n),A (σ i) := by
  induction j with
  | zero =>
    have he : Finset.Iio (⟨0,hj⟩ : Fin n)=∅ := by ext i; simp [Fin.lt_def]
    simp [asapDone,he]
  | succ j ih =>
    rw [asapDone,dif_pos (by omega)]
    change (asapDone A B C σ j).1+A (σ ⟨j,by omega⟩) = _
    rw [ih (by omega),prefix_succ (fun i=>A (σ i)) j hj,prefix_split]

theorem done2_eq {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (j : ℕ) :
    (asapDone A B C σ j).2.1 = TwoStage.asapC2 A B σ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [asapDone,TwoStage.asapC2]
    split_ifs with hj
    · change max (asapDone A B C σ j).2.1 ((asapDone A B C σ j).1+A (σ ⟨j,hj⟩))+B (σ ⟨j,hj⟩) = _
      rw [ih,done1_at A B C σ j hj,← prefix_split,max_comm]
    · exact ih

theorem start1_eq {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    asapStart1 A B C σ=TwoStage.asapStart1 A σ := by
  funext i
  exact done1_at A B C σ (σ.symm i).val (σ.symm i).isLt

theorem start2_eq {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    asapStart2 A B C σ=TwoStage.asapStart2 A B σ := by
  funext i
  simp only [asapStart2,start1_eq,done2_eq]
  have h:=first_finish A σ (σ.symm i)
  simp only [Equiv.apply_symm_apply] at h
  rw [h,max_comm]
  rfl

theorem done3_succ {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (j : ℕ) (hj : j < n) :
    (asapDone A B C σ (j+1)).2.2 = max (asapDone A B C σ j).2.2 (TwoStage.asapC2 A B σ (j+1))+C (σ ⟨j,hj⟩) := by
  have h:=done2_eq A B C σ (j+1)
  simp only [asapDone,dif_pos hj] at h ⊢
  rw [h]

theorem done3_mono {n : ℕ} (A B C : Fin n → ℝ) (hC : ∀ i,0 ≤ C i) (σ : Equiv.Perm (Fin n)) :
    Monotone (fun j=>(asapDone A B C σ j).2.2) := by
  apply monotone_nat_of_le_succ
  intro j
  by_cases hj : j < n
  · rw [done3_succ A B C σ j hj]
    exact (le_max_left _ _).trans (le_add_of_nonneg_right (hC _))
  · simp [asapDone,hj]

theorem third_finish {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    asapStart3 A B C σ (σ k)+C (σ k)=(asapDone A B C σ (k.val+1)).2.2 := by
  rw [done3_succ A B C σ k.val k.isLt]
  simp only [asapStart3,Equiv.symm_apply_apply,start2_eq,second_finish]

theorem three_feasible {n : ℕ} (A B C : Fin n → ℝ) (hA : ∀ i,0 ≤ A i)
    (hB : ∀ i,0 ≤ B i) (hC : ∀ i,0 ≤ C i) (σ : Equiv.Perm (Fin n)) :
    IsFeasible A B C (asapStart1 A B C σ) (asapStart2 A B C σ) (asapStart3 A B C σ) := by
  have hf:=asap_feasible A B hA hB σ
  rw [← start1_eq A B C σ,← start2_eq A B C σ] at hf
  refine ⟨hf.1,hf.2.1,hf.2.2.1,?_,hf.2.2.2,fun i=>le_max_right _ _⟩
  have ho : ∀ k l : Fin n,k < l → asapStart3 A B C σ (σ k)+C (σ k) ≤ asapStart3 A B C σ (σ l) := by
    intro k l hkl
    rw [third_finish]
    exact (done3_mono A B C hC σ (by change k.val+1 ≤ l.val; omega)).trans
      (by simp only [asapStart3,Equiv.symm_apply_apply]; exact le_max_left _ _)
  intro i j hij
  rcases lt_or_gt_of_ne (show σ.symm i ≠ σ.symm j from fun h=>hij (σ.symm.injective h)) with h|h
  · exact Or.inl (by simpa using ho _ _ h)
  · exact Or.inr (by simpa using ho _ _ h)

theorem makespan_eq_done3 {n : ℕ} [NeZero n] (A B C : Fin n → ℝ) (hC : ∀ i,0 ≤ C i)
    (σ : Equiv.Perm (Fin n)) : makespan C (asapStart3 A B C σ)=(asapDone A B C σ n).2.2 := by
  apply le_antisymm
  · apply (Finset.fold_max_le _).mpr
    refine ⟨done3_mono A B C hC σ (Nat.zero_le n),?_⟩
    intro i hi
    have h:=third_finish A B C σ (σ.symm i)
    simp only [Equiv.apply_symm_apply] at h
    rw [h]
    exact done3_mono A B C hC σ (by have := (σ.symm i).isLt; omega)
  · have hn : 0 < n:=Nat.pos_of_ne_zero (NeZero.ne n)
    let k : Fin n:=⟨n-1,by omega⟩
    have hk : k.val+1=n:=by dsimp [k]; omega
    have h:=third_finish A B C σ k
    rw [hk] at h
    exact (Finset.le_fold_max _).mpr (Or.inr ⟨σ k,Finset.mem_univ _,h.ge⟩)

end CJohnson
end

section

open JohnsonFlowShop Shared TwoStage Finset
namespace CJohnson

theorem sum_swap {ι : Type*} [DecidableEq ι] (f : ι → ℝ) (s : Finset ι) (a b : ι) (hab : a ≠ b) :
    (∑ x ∈ s, f (Equiv.swap a b x)) = (∑ x ∈ s, f x) +
      (if a ∈ s then f b-f a else 0) + (if b ∈ s then f a-f b else 0) := by
  have he (x : ι) : f (Equiv.swap a b x) = f x + (if x=a then f b-f a else 0) +
      (if x=b then f a-f b else 0) := by
    by_cases ha : x=a
    · subst x; simp [hab]
    · by_cases hb : x=b
      · subst x; simp [Ne.symm hab]
      · simp [Equiv.swap_apply_of_ne_of_ne ha hb,ha,hb]
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp

theorem K_swap_formula {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (a b u : Fin n) (hab : a ≠ b) :
    K A B (σ * Equiv.swap a b) u = K A B σ u +
      (if a ≤ u then A (σ b)-A (σ a) else 0) + (if b ≤ u then A (σ a)-A (σ b) else 0) -
      (if a < u then B (σ b)-B (σ a) else 0) - (if b < u then B (σ a)-B (σ b) else 0) := by
  unfold K
  simp only [Equiv.Perm.mul_apply]
  rw [sum_swap (fun x => A (σ x)) _ a b hab, sum_swap (fun x => B (σ x)) _ a b hab]
  simp only [Finset.mem_Iic,Finset.mem_Iio,Function.comp_apply]
  ring

theorem K_next {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j+1 < n) :
    K A B σ ⟨j+1,hj⟩ = K A B σ ⟨j,by omega⟩ + A (σ ⟨j+1,hj⟩)-B (σ ⟨j,by omega⟩) := by
  have he1 : Finset.Iic (⟨j+1,hj⟩ : Fin n) = insert ⟨j+1,hj⟩ (Finset.Iic ⟨j,by omega⟩) := by
    ext x
    simp only [Finset.mem_Iic,Finset.mem_insert,Fin.ext_iff,Fin.le_iff_val_le_val]
    omega
  have he2 : Finset.Iio (⟨j+1,hj⟩ : Fin n) = insert ⟨j,by omega⟩ (Finset.Iio ⟨j,by omega⟩) := by
    ext x
    simp only [Finset.mem_Iio,Finset.mem_insert,Fin.ext_iff,Fin.lt_iff_val_lt_val]
    omega
  unfold K
  rw [he1,he2,Finset.sum_insert (by simp),Finset.sum_insert (by simp)]
  ring

theorem K_swap_other {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j+1 < n) (u : Fin n) (hua : u ≠ ⟨j,by omega⟩) (hub : u ≠ ⟨j+1,hj⟩) :
    K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) u = K A B σ u := by
  rw [K_swap_formula A B σ _ _ u (by intro h; have := congrArg Fin.val h; simp at this)]
  have hja : u.val ≠ j := by intro he; apply hua; exact Fin.ext he
  have hjb : u.val ≠ j+1 := by intro he; apply hub; exact Fin.ext he
  by_cases h : u.val < j
  · have ha : ¬ (⟨j,by omega⟩ : Fin n) ≤ u := by change ¬j ≤ u.val; omega
    have hb : ¬ (⟨j+1,hj⟩ : Fin n) ≤ u := by change ¬j+1 ≤ u.val; omega
    have ha' : ¬ (⟨j,by omega⟩ : Fin n) < u := by change ¬j < u.val; omega
    have hb' : ¬ (⟨j+1,hj⟩ : Fin n) < u := by change ¬j+1 < u.val; omega
    simp [ha,hb,ha',hb']
  · have ha : (⟨j,by omega⟩ : Fin n) ≤ u := by change j ≤ u.val; omega
    have hb : (⟨j+1,hj⟩ : Fin n) ≤ u := by change j+1 ≤ u.val; omega
    have ha' : (⟨j,by omega⟩ : Fin n) < u := by change j < u.val; omega
    have hb' : (⟨j+1,hj⟩ : Fin n) < u := by change j+1 < u.val; omega
    simp only [ha,hb,ha',hb',if_pos]
    ring

theorem adjacent_max {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j+1 < n) :
    max (K A B σ ⟨j,by omega⟩) (K A B σ ⟨j+1,hj⟩) =
      K A B σ ⟨j,by omega⟩ + A (σ ⟨j+1,hj⟩)-min (A (σ ⟨j+1,hj⟩)) (B (σ ⟨j,by omega⟩)) ∧
    max (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j,by omega⟩)
        (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j+1,hj⟩) =
      K A B σ ⟨j,by omega⟩ + A (σ ⟨j+1,hj⟩)-min (A (σ ⟨j,by omega⟩)) (B (σ ⟨j+1,hj⟩)) := by
  have hab : (⟨j,by omega⟩ : Fin n) ≠ ⟨j+1,hj⟩ := by intro h; have := congrArg Fin.val h; simp at this
  have ha : (⟨j,by omega⟩ : Fin n) < ⟨j+1,hj⟩ := by simp
  constructor
  · rw [K_next A B σ j hj]
    simp only [max_def,min_def]
    split_ifs <;> linarith
  · rw [K_swap_formula A B σ _ _ _ hab,K_swap_formula A B σ _ _ _ hab]
    simp only [le_refl,ha.le,ha,not_le.mpr ha,not_lt_of_ge ha.le,lt_irrefl,if_pos,if_false]
    rw [K_next A B σ j hj]
    simp only [max_def,min_def]
    split_ifs <;> linarith

theorem interchange_iff {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j+1 < n) :
    (∀ u : Fin n, u ≠ ⟨j,by omega⟩ → u ≠ ⟨j+1,hj⟩ →
      K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) u = K A B σ u) ∧
    (max (K A B σ ⟨j,by omega⟩) (K A B σ ⟨j+1,hj⟩) <
      max (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j,by omega⟩)
        (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j+1,hj⟩) ↔
      min (A (σ ⟨j,by omega⟩)) (B (σ ⟨j+1,hj⟩)) < min (A (σ ⟨j+1,hj⟩)) (B (σ ⟨j,by omega⟩))) := by
  refine ⟨K_swap_other A B σ j hj,?_⟩
  rw [(adjacent_max A B σ j hj).1,(adjacent_max A B σ j hj).2]
  exact sub_lt_sub_iff_left _

theorem interchange_F_le {n : ℕ} [NeZero n] (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j+1 < n)
    (hII : min (A (σ ⟨j,by omega⟩)) (B (σ ⟨j+1,hj⟩)) ≤ min (A (σ ⟨j+1,hj⟩)) (B (σ ⟨j,by omega⟩))) :
    F A B σ ≤ F A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) := by
  have hm : max (K A B σ ⟨j,by omega⟩) (K A B σ ⟨j+1,hj⟩) ≤
      max (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j,by omega⟩)
        (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j+1,hj⟩) := by
    rw [(adjacent_max A B σ j hj).1,(adjacent_max A B σ j hj).2]
    linarith
  have hbound : max (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j,by omega⟩)
        (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j+1,hj⟩) ≤ F A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) :=
    max_le (Finset.le_sup' _ (Finset.mem_univ _)) (Finset.le_sup' _ (Finset.mem_univ _))
  apply Finset.sup'_le
  intro u hu
  by_cases ha : u=⟨j,by omega⟩
  · subst u; exact (le_max_left _ _).trans (hm.trans hbound)
  by_cases hb : u=⟨j+1,hj⟩
  · subst u; exact (le_max_right _ _).trans (hm.trans hbound)
  rw [← K_swap_other A B σ j hj u ha hb]
  exact Finset.le_sup' _ (Finset.mem_univ _)

end CJohnson
end

section

open JohnsonFlowShop Shared
namespace CJohnson

theorem HK_eq {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    ThreeStage.H B C σ v+K A B σ v = K (fun i => A i+B i) (fun i => B i+C i) σ v := by
  unfold ThreeStage.H K
  simp only [Finset.sum_add_distrib]
  ring

theorem three_interchange {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j k : Fin n) (hjk : k.val=j.val+1) :
    let σ' := σ * Equiv.swap j k
    (∀ v : Fin n, v ≠ j → v ≠ k → ThreeStage.H B C σ' v=ThreeStage.H B C σ v ∧ K A B σ' v=K A B σ v) ∧
    (max (ThreeStage.H B C σ k+K A B σ k) (ThreeStage.H B C σ j+K A B σ j) <
      max (ThreeStage.H B C σ' k+K A B σ' k) (ThreeStage.H B C σ' j+K A B σ' j) ↔
      min (A (σ j)+B (σ j)) (C (σ k)+B (σ k)) < min (A (σ k)+B (σ k)) (C (σ j)+B (σ j))) := by
  have hj : j.val+1 < n := hjk ▸ k.isLt
  have hk : k=⟨j.val+1,hj⟩ := Fin.ext hjk
  subst k
  dsimp only
  constructor
  · intro v hvj hvk
    exact ⟨K_swap_other B C σ j.val hj v hvj hvk,K_swap_other A B σ j.val hj v hvj hvk⟩
  · simp_rw [HK_eq]
    rw [max_comm (K _ _ σ _),max_comm (K _ _ (σ * Equiv.swap _ _) _)]
    simpa only [add_comm] using (interchange_iff (fun i => A i+B i) (fun i => B i+C i) σ j.val hj).2

end CJohnson
end

section

open JohnsonFlowShop Shared ThreeStage Finset
namespace CJohnson

theorem sup_add {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (c : ℝ) :
    s.sup' hs (fun i=>f i+c)=s.sup' hs f+c := by
  symm
  exact Finset.apply_sup'_eq_sup'_comp hs (fun x : ℝ=>x+c) (fun x y=>(max_add_add_right x y c).symm)

theorem done3_formula {n : ℕ} (A B C : Fin n → ℝ) (hB : ∀ i,0 ≤ B i)
    (σ : Equiv.Perm (Fin n)) (j : ℕ) (hj : j < n) :
    (asapDone A B C σ (j+1)).2.2 = (∑ i ∈ Finset.Iic (⟨j,hj⟩ : Fin n),C (σ i))+
      (Finset.Iic (⟨j,hj⟩ : Fin n)).sup' Finset.nonempty_Iic
        (fun v=>TwoStage.asapC2 A B σ (v.val+1)-∑ i ∈ Finset.Iio v,C (σ i)) := by
  induction j with
  | zero =>
    have he : Finset.Iic (⟨0,hj⟩ : Fin n)={⟨0,hj⟩} := by
      ext i
      simp only [Finset.mem_Iic,Finset.mem_singleton,Fin.ext_iff,Fin.le_iff_val_le_val]
      omega
    have he' : Finset.Iio (⟨0,hj⟩ : Fin n)=∅ := by ext i; simp [Fin.lt_def]
    rw [done3_succ A B C σ 0 hj]
    simp only [he,Finset.sum_singleton,Finset.sup'_singleton,he',Finset.sum_empty,sub_zero,asapDone]
    rw [max_eq_right (C2_nonneg A B hB σ 1)]
    ring
  | succ j ih =>
    rw [done3_succ A B C σ (j+1) hj,ih (by omega)]
    have hsup : (Finset.Iic (⟨j+1,hj⟩ : Fin n)).sup' Finset.nonempty_Iic
        (fun v=>TwoStage.asapC2 A B σ (v.val+1)-∑ i ∈ Finset.Iio v,C (σ i)) =
        max (TwoStage.asapC2 A B σ (j+1+1)-∑ i ∈ Finset.Iio (⟨j+1,hj⟩ : Fin n),C (σ i))
          ((Finset.Iic (⟨j,by omega⟩ : Fin n)).sup' Finset.nonempty_Iic
            (fun v=>TwoStage.asapC2 A B σ (v.val+1)-∑ i ∈ Finset.Iio v,C (σ i))) := by
      simp only [Iic_succ j hj,Finset.sup'_insert Finset.nonempty_Iic]
    rw [hsup,prefix_split (fun i=>C (σ i)) ⟨j+1,hj⟩,prefix_succ (fun i=>C (σ i)) j hj]
    simp only [max_def]
    split_ifs <;> linarith

theorem three_release_formula {n : ℕ} [NeZero n] (A B C : Fin n → ℝ)
    (hB : ∀ i,0 ≤ B i) (hC : ∀ i,0 ≤ C i) (σ : Equiv.Perm (Fin n)) :
    makespan C (asapStart3 A B C σ)=∑ i,C i+Finset.univ.sup' Finset.univ_nonempty
      (fun v=>TwoStage.asapC2 A B σ (v.val+1)-∑ i ∈ Finset.Iio v,C (σ i)) := by
  have hn : 0 < n:=Nat.pos_of_ne_zero (NeZero.ne n)
  let k : Fin n:=⟨n-1,by omega⟩
  have hk : k.val+1=n:=by dsimp [k]; omega
  have he : Finset.Iic k=Finset.univ := by
    ext i
    simp only [Finset.mem_Iic,Finset.mem_univ,iff_true]
    change i.val ≤ n-1
    have :=i.isLt
    omega
  have hh:=done3_formula A B C hB σ k.val k.isLt
  rw [hk] at hh
  change (asapDone A B C σ n).2.2=(∑ i ∈ Finset.Iic k,C (σ i))+
    (Finset.Iic k).sup' Finset.nonempty_Iic _ at hh
  simp only [he] at hh
  rw [Equiv.sum_comp σ C] at hh
  rw [makespan_eq_done3 A B C hC σ]
  exact hh

theorem three_makespan_formula {n : ℕ} [NeZero n] (A B C : Fin n → ℝ)
    (hA : ∀ i,0 < A i) (hB : ∀ i,0 < B i) (hC : ∀ i,0 < C i) (σ : Equiv.Perm (Fin n)) :
    makespan C (asapStart3 A B C σ)=∑ i,C i+Finset.univ.sup' Finset.univ_nonempty
      (fun v=>(Finset.Iic v).sup' Finset.nonempty_Iic (fun u=>K A B σ u+H B C σ v)) := by
  rw [three_release_formula A B C (fun i=>(hB i).le) (fun i=>(hC i).le) σ]
  congr 1
  apply Finset.sup'_congr _ rfl
  intro v hv
  rw [C2_formula A B (fun i=>(hA i).le) σ v.val v.isLt,sup_add]
  unfold H
  ring

theorem K_mono {n : ℕ} (A B : Fin n → ℝ) (hAB : ∀ i j,B j ≤ A i) (σ : Equiv.Perm (Fin n)) :
    Monotone (K A B σ) := by
  cases n with
  | zero => exact fun i=>Fin.elim0 i
  | succ n =>
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    have h:=K_next A B σ k.val (by omega)
    change K A B σ ⟨k.val,by omega⟩ ≤ K A B σ ⟨k.val+1,by omega⟩
    rw [h]
    linarith [hAB (σ ⟨k.val+1,by omega⟩) (σ ⟨k.val,by omega⟩)]

theorem supK_eq {n : ℕ} (A B : Fin n → ℝ) (hAB : ∀ i j,B j ≤ A i)
    (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (Finset.Iic v).sup' Finset.nonempty_Iic (K A B σ)=K A B σ v := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro u hu
    exact K_mono A B hAB σ (Finset.mem_Iic.mp hu)
  · exact Finset.le_sup' _ (Finset.mem_Iic.mpr le_rfl)

theorem special_formula {n : ℕ} [NeZero n] (A B C : Fin n → ℝ)
    (hA : ∀ i,0 < A i) (hB : ∀ i,0 < B i) (hC : ∀ i,0 < C i)
    (hAB : ∀ i j,B j ≤ A i) (σ : Equiv.Perm (Fin n)) :
    (∀ v : Fin n,(Finset.Iic v).sup' Finset.nonempty_Iic (K A B σ)=K A B σ v) ∧
    makespan C (asapStart3 A B C σ)=∑ i,C i+Finset.univ.sup' Finset.univ_nonempty
      (fun v=>H B C σ v+K A B σ v) := by
  refine ⟨supK_eq A B hAB σ,?_⟩
  rw [three_makespan_formula A B C hA hB hC σ]
  congr 1
  apply Finset.sup'_congr _ rfl
  intro v hv
  rw [sup_add,supK_eq A B hAB σ]
  ring

end CJohnson

end

section
open JohnsonFlowShop Shared ThreeStage
theorem solution {n : ℕ} [NeZero n] (A B C : Fin n → ℝ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (σ : Equiv.Perm (Fin n)) :
    Shared.makespan C (asapStart3 A B C σ) =
      ∑ i, C i + Finset.univ.sup' Finset.univ_nonempty (fun v : Fin n =>
        (Finset.Iic v).sup' Finset.nonempty_Iic (fun u => Shared.K A B σ u + H B C σ v)) := by
  exact CJohnson.three_makespan_formula A B C hA hB hC σ

end
