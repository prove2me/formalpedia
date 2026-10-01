-- Prove2me | solution 1 for JohnsonFlowShop.TwoStage.johnson_rule_optimal
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:11:26.411074+00:00
-- url     : https://prove2.me/submissions/4e211d2d-ba07-4ef6-9a34-5264c48021f5

import Definitions.Def_JohnsonFlowShop_TwoStage_F
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_JohnsonFlowShop_Shared_makespan
import Definitions.Def_JohnsonFlowShop_TwoStage_IsFeasible
import Definitions.Def_JohnsonFlowShop_TwoStage_FollowsOrder
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart1
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart2
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.FinRange
import Definitions.Def_JohnsonFlowShop_TwoStage_JohnsonOrdered
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Field.Basic
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

section

open JohnsonFlowShop Shared TwoStage Finset
namespace CJohnson

theorem weighted_swap {ι : Type*} [Fintype ι] [DecidableEq ι] (w r : ι → ℝ) (a b : ι) (hab : a≠b) :
    (∑ k,w k*r (Equiv.swap a b k)) = (∑ k,w k*r k)+(w a-w b)*(r b-r a) := by
  have he (k : ι) : w k*r (Equiv.swap a b k) = w k*r k +
      (if k=a then w a*(r b-r a) else 0)+(if k=b then w b*(r a-r b) else 0) := by
    by_cases ha : k=a
    · subst k; simp [hab];ring
    · by_cases hb : k=b
      · subst k; simp [Ne.symm hab];ring
      · simp [Equiv.swap_apply_of_ne_of_ne ha hb,ha,hb]
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp
  ring

noncomputable def score {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ k,(k.val:ℝ)*((σ.symm (τ k)).val:ℝ)

theorem score_swap {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (j : ℕ) (hj : j+1 < n) :
    score σ (τ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) = score σ τ+
      (((σ.symm (τ ⟨j,by omega⟩)).val:ℝ)-((σ.symm (τ ⟨j+1,hj⟩)).val:ℝ)) := by
  unfold score
  simp only [Equiv.Perm.mul_apply]
  rw [weighted_swap (fun k : Fin n => (k.val:ℝ)) (fun k=>((σ.symm (τ k)).val:ℝ)) _ _ (by
    intro h;have := congrArg Fin.val h;simp at this)]
  simp only [Nat.cast_add,Nat.cast_one]
  ring

theorem cost_min_of_swaps {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ) (σ : Equiv.Perm (Fin n))
    (hswap : ∀ (τ : Equiv.Perm (Fin n)) (j : ℕ) (hj : j+1 < n),
      σ.symm (τ ⟨j+1,hj⟩) < σ.symm (τ ⟨j,by omega⟩) →
      f (τ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ≤ f τ) : ∀ τ,f σ ≤ f τ := by
  classical
  obtain ⟨τ0,hτ0,hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  let Q : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter (fun τ=>f τ=f τ0)
  have hQ : Q.Nonempty := ⟨τ0,by simp [Q]⟩
  obtain ⟨τ,hτ,hmax⟩ := Finset.exists_max_image Q (score σ) hQ
  have hτmin : ∀ ρ,f τ ≤ f ρ := by
    have he := (Finset.mem_filter.mp hτ).2
    intro ρ
    rw [he]
    exact hmin ρ (Finset.mem_univ _)
  have hadj (j : ℕ) (hj : j+1 < n) : σ.symm (τ ⟨j,by omega⟩) ≤ σ.symm (τ ⟨j+1,hj⟩) := by
    by_contra hn
    have hlt := lt_of_not_ge hn
    let υ := τ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩
    have he : f υ=f τ := le_antisymm (hswap τ j hj hlt) (hτmin υ)
    have hυ : υ∈Q := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,he.trans ((Finset.mem_filter.mp hτ).2)⟩
    have hh := hmax υ hυ
    dsimp [υ] at hh
    rw [score_swap σ τ j hj] at hh
    have hr : ((σ.symm (τ ⟨j+1,hj⟩)).val:ℝ) < ((σ.symm (τ ⟨j,by omega⟩)).val:ℝ) := by exact_mod_cast hlt
    linarith
  have hmono : Monotone (σ.symm * τ : Equiv.Perm (Fin n)) := by
    cases n with
    | zero => intro i;exact Fin.elim0 i
    | succ m =>
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      exact hadj i.val (by have := i.isLt;omega)
  have he : σ.symm * τ=Equiv.refl _ := (Equiv.Perm.monotone_iff _).mp hmono
  have hτσ : τ=σ := by
    apply Equiv.ext
    intro i
    have hi := congrArg (fun e : Equiv.Perm (Fin n)=>σ (e i)) he
    simpa using hi
  subst τ
  exact hτmin

noncomputable def johnsonKey {n : ℕ} (A B : Fin n → ℝ) (i : Fin n) : ℝ :=
  if A i ≤ B i then -(1/(A i+1)) else 1/(B i+1)

theorem key_preference {n : ℕ} (A B : Fin n → ℝ) (hA : ∀ i,0 < A i) (hB : ∀ i,0 < B i)
    (i j : Fin n) (h : johnsonKey A B i ≤ johnsonKey A B j) : min (A i) (B j) ≤ min (A j) (B i) := by
  unfold johnsonKey at h
  by_cases hi : A i ≤ B i
  · by_cases hj : A j ≤ B j
    · rw [if_pos hi,if_pos hj] at h
      have hh := (one_div_le_one_div (by linarith [hA j]) (by linarith [hA i])).mp (neg_le_neg_iff.mp h)
      have ha : A i ≤ A j := by linarith
      exact le_min ((min_le_left _ _).trans ha) ((min_le_left _ _).trans hi)
    · exact le_min ((min_le_right _ _).trans (le_of_not_ge hj)) ((min_le_left _ _).trans hi)
  · by_cases hj : A j ≤ B j
    · rw [if_neg hi,if_pos hj] at h
      have hp : 0 < (1:ℝ)/(B i+1) := div_pos zero_lt_one (by linarith [hB i])
      have hp' : 0 < (1:ℝ)/(A j+1) := div_pos zero_lt_one (by linarith [hA j])
      linarith
    · rw [if_neg hi,if_neg hj] at h
      have hh := (one_div_le_one_div (by linarith [hB i]) (by linarith [hB j])).mp h
      have hb : B j ≤ B i := by linarith
      exact le_min ((min_le_right _ _).trans (le_of_not_ge hj)) ((min_le_right _ _).trans hb)

theorem ordered_exists {n : ℕ} (A B : Fin n → ℝ) (hA : ∀ i,0 < A i) (hB : ∀ i,0 < B i) :
    ∃ σ : Equiv.Perm (Fin n),JohnsonOrdered A B σ := by
  refine ⟨Tuple.sort (johnsonKey A B),?_⟩
  intro k l hkl
  apply key_preference A B hA hB
  exact Tuple.monotone_sort (johnsonKey A B) hkl.le

theorem ordered_F_min {n : ℕ} [NeZero n] (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (hσ : JohnsonOrdered A B σ) : ∀ τ,F A B σ ≤ F A B τ := by
  apply cost_min_of_swaps (F A B) σ
  intro τ j hj hlt
  let a : Fin n := ⟨j,by omega⟩
  let b : Fin n := ⟨j+1,hj⟩
  have hab : a≠b := by intro h;have := congrArg Fin.val h;dsimp [a,b] at this;omega
  have hII : min (A (τ b)) (B (τ a)) ≤ min (A (τ a)) (B (τ b)) := by
    simpa using hσ (σ.symm (τ b)) (σ.symm (τ a)) hlt
  have hII' : min (A ((τ * Equiv.swap a b) a)) (B ((τ * Equiv.swap a b) b)) ≤
      min (A ((τ * Equiv.swap a b) b)) (B ((τ * Equiv.swap a b) a)) := by
    simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_left,Equiv.swap_apply_right] using hII
  have hh := interchange_F_le A B (τ * Equiv.swap a b) j hj hII'
  have he : τ * Equiv.swap a b * Equiv.swap a b=τ := by simp [mul_assoc]
  change F A B (τ * Equiv.swap a b) ≤ F A B τ
  rwa [he] at hh

end CJohnson
end

section

open JohnsonFlowShop TwoStage

theorem solution {n : ℕ} (A B : Fin n → ℝ) (hA : ∀ i,0 < A i) (hB : ∀ i,0 < B i) :
    (∃ σ : Equiv.Perm (Fin n),JohnsonOrdered A B σ) ∧
    ∀ σ : Equiv.Perm (Fin n),JohnsonOrdered A B σ →
      IsFeasible A B (asapStart1 A σ) (asapStart2 A B σ) ∧
      ∀ s1 s2 : Fin n → ℝ,IsFeasible A B s1 s2 →
        Shared.makespan B (asapStart2 A B σ) ≤ Shared.makespan B s2 := by
  refine ⟨CJohnson.ordered_exists A B hA hB,?_⟩
  intro σ hσ
  refine ⟨CJohnson.asap_feasible A B (fun i=>(hA i).le) (fun i=>(hB i).le) σ,?_⟩
  intro s1 s2 hs
  obtain ⟨τ,t1,t2,ht,ho,hspan⟩ := CJohnson.same_order A B hA hB s1 s2 hs
  have hopt := (CJohnson.asap_optimal A B hA hB τ).2.2 t1 t2 ht ho
  cases n with
  | zero => simp [Shared.makespan]
  | succ m =>
    have hF := CJohnson.ordered_F_min A B σ hσ τ
    have hh : Shared.makespan B (asapStart2 A B σ) ≤ Shared.makespan B (asapStart2 A B τ) := by
      rw [CJohnson.makespan_formula A B hA hB σ,CJohnson.makespan_formula A B hA hB τ]
      exact add_le_add le_rfl hF
    exact hh.trans (hopt.trans hspan)
end
