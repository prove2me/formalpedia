-- Prove2me | solution 1 for LawlerWCT.SeriesPar.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T11:11:25.977576+00:00
-- url     : https://prove2.me/submissions/0df7d689-62d1-4beb-81ff-203dd7ba0efa

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Linarith
import Definitions.Def_LawlerWCT_SeriesPar_Model
import Theorems.Thm_LawlerWCT_SeriesPar_theorem_2

open LawlerWCT.SeriesPar

private lemma exists_max_in_list {α : Type*} (f : α → ℝ) (P : α → Prop) :
    ∀ (L : List α) (x₀ : α), x₀ ∈ L → P x₀ →
      ∃ x ∈ L, P x ∧ ∀ y ∈ L, P y → f y ≤ f x
  | [], _, hx₀, _ => by cases hx₀
  | a :: as, x₀, hx₀, hPx₀ => by
    by_cases h : ∃ z ∈ as, P z
    · rcases h with ⟨z, hzas, hPz⟩
      rcases exists_max_in_list f P as z hzas hPz with ⟨m, hmas, hPm, hmax⟩
      by_cases hPa : P a
      · by_cases hle : f m ≤ f a
        · refine ⟨a, List.mem_cons_self, hPa, fun y hy hPy => ?_⟩
          rcases List.mem_cons.mp hy with rfl | hyas
          · exact le_rfl
          · exact le_trans (hmax y hyas hPy) hle
        · refine ⟨m, List.mem_cons_of_mem a hmas, hPm, fun y hy hPy => ?_⟩
          rcases List.mem_cons.mp hy with rfl | hyas
          · linarith
          · exact hmax y hyas hPy
      · refine ⟨m, List.mem_cons_of_mem a hmas, hPm, fun y hy hPy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hyas
        · exact absurd hPy hPa
        · exact hmax y hyas hPy
    · push Not at h
      rcases List.mem_cons.mp hx₀ with rfl | hx₀as
      · refine ⟨x₀, List.mem_cons_self, hPx₀, fun y hy hPy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hyas
        · exact le_rfl
        · exact absurd hPy (h y hyas)
      · exact absurd hPx₀ (h x₀ hx₀as)

private lemma exists_rhoMaximal_local {ι : Type*} [DecidableEq ι] (G : ι → ι → Prop)
    (p w : ι → ℝ) (M : Finset ι) (hM_ne : M.Nonempty) :
    ∃ I : Finset ι, IsRhoMaximal G p w M I := by
  have hM_mem : M ∈ M.powerset.toList :=
    Finset.mem_toList.mpr (Finset.mem_powerset.mpr (Finset.Subset.refl M))
  have hM_init : IsInitialSet G M M ∧ M.Nonempty :=
    ⟨⟨Finset.Subset.refl M, fun _ _ _ hiM _ => hiM⟩, hM_ne⟩
  rcases exists_max_in_list (rho p w) (fun I => IsInitialSet G M I ∧ I.Nonempty)
    M.powerset.toList M hM_mem hM_init with ⟨I, _, ⟨hI_init, hI_ne⟩, hI_max⟩
  refine ⟨I, hI_init, hI_ne, fun I' hI'_init hI'_ne => ?_⟩
  exact hI_max I' (Finset.mem_toList.mpr (Finset.mem_powerset.mpr hI'_init.1)) ⟨hI'_init, hI'_ne⟩

private lemma idxOf_lt_of_edge {ι : Type*} [DecidableEq ι] (G : ι → ι → Prop)
    (hacyc : ∀ j, ¬ Relation.TransGen G j j) {M : Finset ι} {l : List ι}
    (hl : LawlerPrec.MinMax.IsFeasible G M l) {x y : ι}
    (hx : x ∈ M) (hy : y ∈ M) (hxy : G x y) :
    l.idxOf x < l.idxOf y := by
  have hxl : x ∈ l := (hl.1.2 x).mpr hx
  have hyl : y ∈ l := (hl.1.2 y).mpr hy
  have hxi : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hxl
  have hyi : l.idxOf y < l.length := List.idxOf_lt_length_of_mem hyl
  by_contra hle
  rcases lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | heq
  · have hpair := (List.pairwise_iff_getElem.mp hl.2) (l.idxOf y) (l.idxOf x) hyi hxi hlt
    rw [List.getElem_idxOf hyi, List.getElem_idxOf hxi] at hpair
    exact hpair hxy
  · have hxy_eq : x = y := by
      have h1 := List.getElem_idxOf hxi
      have h2 := List.getElem_idxOf hyi
      simp only [heq] at h2
      exact h1.symm.trans h2
    exact hacyc x (Relation.TransGen.single (hxy_eq ▸ hxy))

private lemma idxOf_lt_of_transGen_N {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    {l : List ι} (hl : LawlerPrec.MinMax.IsFeasible G N l) {x y : ι}
    (hx : x ∈ N) (hy : y ∈ N) (hxy : Relation.TransGen G x y) :
    l.idxOf x < l.idxOf y := by
  induction hxy with
  | single h => exact idxOf_lt_of_edge G hacyc hl hx hy h
  | @tail b c _ hbc ih =>
    have hbN : b ∈ N := (hGN b c hbc).1
    exact lt_trans (ih hbN) (idxOf_lt_of_edge G hacyc hl hbN hy hbc)

private lemma idxOf_append_of_mem {ι : Type*} [DecidableEq ι] {l₁ l₂ : List ι} {x : ι}
    (hx : x ∈ l₁) : (l₁ ++ l₂).idxOf x = l₁.idxOf x := by
  induction l₁ with
  | nil => cases hx
  | cons a as ih =>
    simp only [List.cons_append, List.idxOf_cons]
    by_cases hax : a = x
    · simp [hax]
    · have hxs : x ∈ as := (List.mem_cons.mp hx).resolve_left (Ne.symm hax)
      simp [ih hxs]

private lemma idxOf_append_of_notMem {ι : Type*} [DecidableEq ι] {l₁ l₂ : List ι} {x : ι}
    (hx : x ∉ l₁) : (l₁ ++ l₂).idxOf x = l₁.length + l₂.idxOf x := by
  induction l₁ with
  | nil => simp
  | cons a as ih =>
    have hax : (a == x) = false := beq_false_of_ne (fun h => hx (h ▸ List.mem_cons_self))
    have hxs : x ∉ as := fun h => hx (List.mem_cons_of_mem a h)
    simp only [List.cons_append, List.idxOf_cons, hax, cond_false, List.length_cons, ih hxs]
    omega

private lemma completionTime_append_left {ι : Type*} [DecidableEq ι] (p : ι → ℝ)
    {l₁ l₂ : List ι} {x : ι} (hx : x ∈ l₁) :
    MooreLateJobs.Shared.completionTime p (l₁ ++ l₂) x =
      MooreLateJobs.Shared.completionTime p l₁ x := by
  unfold MooreLateJobs.Shared.completionTime MooreLateJobs.Shared.completionAt
  rw [idxOf_append_of_mem hx, List.take_append_of_le_length]
  exact Nat.succ_le_of_lt (List.idxOf_lt_length_of_mem hx)

private lemma completionTime_append_right {ι : Type*} [DecidableEq ι] (p : ι → ℝ)
    {l₁ l₂ : List ι} {x : ι} (hx : x ∉ l₁) :
    MooreLateJobs.Shared.completionTime p (l₁ ++ l₂) x =
      (l₁.map p).sum + MooreLateJobs.Shared.completionTime p l₂ x := by
  unfold MooreLateJobs.Shared.completionTime MooreLateJobs.Shared.completionAt
  rw [idxOf_append_of_notMem hx, Nat.add_assoc, List.take_append,
      List.take_of_length_le (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.map_append, List.sum_append]

private lemma weightedCompletion_append {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    {M₁ M₂ : Finset ι} (hdisj : Disjoint M₁ M₂) {l₁ l₂ : List ι}
    (hl₁ : ∀ x, x ∈ l₁ ↔ x ∈ M₁) :
    SingleMachinePrec.Biclique.weightedCompletion p w (M₁ ∪ M₂) (l₁ ++ l₂) =
      SingleMachinePrec.Biclique.weightedCompletion p w M₁ l₁ +
        (∑ j ∈ M₂, w j * (l₁.map p).sum) +
        SingleMachinePrec.Biclique.weightedCompletion p w M₂ l₂ := by
  unfold SingleMachinePrec.Biclique.weightedCompletion
  rw [Finset.sum_union hdisj]
  have hsum1 :
      ∑ j ∈ M₁, w j * MooreLateJobs.Shared.completionTime p (l₁ ++ l₂) j =
        ∑ j ∈ M₁, w j * MooreLateJobs.Shared.completionTime p l₁ j := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [completionTime_append_left p ((hl₁ j).mpr hj)]
  have hsum2 :
      ∑ j ∈ M₂, w j * MooreLateJobs.Shared.completionTime p (l₁ ++ l₂) j =
        (∑ j ∈ M₂, w j * (l₁.map p).sum) +
          ∑ j ∈ M₂, w j * MooreLateJobs.Shared.completionTime p l₂ j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj_not : j ∉ l₁ := fun h => Finset.disjoint_left.mp hdisj ((hl₁ j).mp h) hj
    rw [completionTime_append_right p hj_not, mul_add]
  linarith

private lemma sum_toFinset_eq_map_sum {ι : Type*} [DecidableEq ι] (f : ι → ℝ)
    {l : List ι} (hnd : l.Nodup) :
    ∑ x ∈ l.toFinset, f x = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.nodup_cons] at hnd
    have ha : a ∉ as.toFinset := by simpa using hnd.1
    rw [List.toFinset_cons, Finset.sum_insert ha, List.map_cons, List.sum_cons, ih hnd.2]

private lemma map_p_sum_pos {ι : Type*} (p : ι → ℝ) {l : List ι}
    (hne : l ≠ []) (hp : ∀ j ∈ l, 0 < p j) : 0 < (l.map p).sum := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a as ih =>
    rw [List.map_cons, List.sum_cons]
    have ha : 0 < p a := hp a List.mem_cons_self
    have has : 0 ≤ (as.map p).sum :=
      List.sum_nonneg (by
        intro x hx
        rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
        exact le_of_lt (hp j (List.mem_cons_of_mem a hj)))
    linarith

private lemma finset_sum_mul {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (c : ℝ) :
    (∑ x ∈ s, f x) * c = ∑ x ∈ s, f x * c := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mul, ih]

private lemma weightedCompletion_swap_diff {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (J : Finset ι) (X A B Y : List ι)
    (hnd : (X ++ A ++ B ++ Y).Nodup)
    (hmem : ∀ j, j ∈ X ++ A ++ B ++ Y ↔ j ∈ J) :
    SingleMachinePrec.Biclique.weightedCompletion p w J (X ++ A ++ B ++ Y) -
      SingleMachinePrec.Biclique.weightedCompletion p w J (X ++ B ++ A ++ Y) =
      (B.map w).sum * (A.map p).sum - (A.map w).sum * (B.map p).sum := by
  have hnd_XAB : (X ++ A ++ B).Nodup := (List.nodup_append.mp hnd).1
  have hnd_XA : (X ++ A).Nodup := (List.nodup_append.mp hnd_XAB).1
  have hnd_A : A.Nodup := (List.nodup_append.mp hnd_XA).2.1
  have hnd_B : B.Nodup := (List.nodup_append.mp hnd_XAB).2.1
  have hdisj_X_A : Disjoint X.toFinset A.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxX hxA
    exact (List.nodup_append.mp hnd_XA).2.2 x (List.mem_toFinset.mp hxX) x (List.mem_toFinset.mp hxA) rfl
  have hdisj_XA_B : Disjoint (X.toFinset ∪ A.toFinset) B.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxXA hxB
    have hx_mem : x ∈ X ++ A := by
      rcases Finset.mem_union.mp hxXA with hxX | hxA
      · exact List.mem_append_left _ (List.mem_toFinset.mp hxX)
      · exact List.mem_append_right _ (List.mem_toFinset.mp hxA)
    exact (List.nodup_append.mp hnd_XAB).2.2 x hx_mem x (List.mem_toFinset.mp hxB) rfl
  have hdisj_X_B : Disjoint X.toFinset B.toFinset :=
    Finset.disjoint_of_subset_left Finset.subset_union_left hdisj_XA_B
  have hdisj_B_A : Disjoint B.toFinset A.toFinset :=
    (Finset.disjoint_of_subset_left Finset.subset_union_right hdisj_XA_B).symm
  have hdisj_XB_A : Disjoint (X.toFinset ∪ B.toFinset) A.toFinset :=
    Finset.disjoint_union_left.mpr ⟨hdisj_X_A, hdisj_B_A⟩
  have hdisj_XAB_Y : Disjoint (X.toFinset ∪ A.toFinset ∪ B.toFinset) Y.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxXAB hxY
    have hx_mem : x ∈ X ++ A ++ B := by
      rcases Finset.mem_union.mp hxXAB with hxXA | hxB
      · rcases Finset.mem_union.mp hxXA with hxX | hxA
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_toFinset.mp hxX))
        · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_toFinset.mp hxA))
      · exact List.mem_append_right _ (List.mem_toFinset.mp hxB)
    exact (List.nodup_append.mp hnd).2.2 x hx_mem x (List.mem_toFinset.mp hxY) rfl
  have hunion_eq : X.toFinset ∪ B.toFinset ∪ A.toFinset = X.toFinset ∪ A.toFinset ∪ B.toFinset := by
    rw [Finset.union_assoc, Finset.union_assoc, Finset.union_comm B.toFinset A.toFinset]
  have hdisj_XBA_Y : Disjoint (X.toFinset ∪ B.toFinset ∪ A.toFinset) Y.toFinset := by
    rwa [hunion_eq]
  have hJ_eq : J = (X.toFinset ∪ A.toFinset ∪ B.toFinset) ∪ Y.toFinset := by
    ext j
    simp only [← hmem, List.mem_append, Finset.mem_union, List.mem_toFinset]
  have h1 := weightedCompletion_append p w hdisj_XAB_Y (l₁ := X ++ A ++ B) (l₂ := Y)
    (fun j => by simp [List.mem_append, Finset.mem_union])
  have h2 := weightedCompletion_append p w hdisj_XA_B (l₁ := X ++ A) (l₂ := B)
    (fun j => by simp [List.mem_append, Finset.mem_union])
  have h3 := weightedCompletion_append p w hdisj_X_A (l₁ := X) (l₂ := A)
    (fun j => by simp)
  have h4 := weightedCompletion_append p w hdisj_XBA_Y (l₁ := X ++ B ++ A) (l₂ := Y)
    (fun j => by simp [List.mem_append, Finset.mem_union])
  have h5 := weightedCompletion_append p w hdisj_XB_A (l₁ := X ++ B) (l₂ := A)
    (fun j => by simp [List.mem_append, Finset.mem_union])
  have h6 := weightedCompletion_append p w hdisj_X_B (l₁ := X) (l₂ := B)
    (fun j => by simp)
  rw [hunion_eq] at h4 h5
  have h_p_eq : ((X ++ B ++ A).map p).sum = ((X ++ A ++ B).map p).sum := by
    simp only [List.map_append, List.sum_append]
    linarith
  have h_cross_A : ∑ j ∈ A.toFinset, w j * ((X ++ B).map p).sum =
      (∑ j ∈ A.toFinset, w j * (X.map p).sum) + (A.map w).sum * (B.map p).sum := by
    simp only [List.map_append, List.sum_append, mul_add, Finset.sum_add_distrib]
    rw [← finset_sum_mul A.toFinset w (B.map p).sum, sum_toFinset_eq_map_sum w hnd_A]
  have h_cross_B : ∑ j ∈ B.toFinset, w j * ((X ++ A).map p).sum =
      (∑ j ∈ B.toFinset, w j * (X.map p).sum) + (B.map w).sum * (A.map p).sum := by
    simp only [List.map_append, List.sum_append, mul_add, Finset.sum_add_distrib]
    rw [← finset_sum_mul B.toFinset w (A.map p).sum, sum_toFinset_eq_map_sum w hnd_B]
  rw [hJ_eq, h1, h2, h3, h4, h5, h6, h_p_eq, h_cross_A, h_cross_B]
  linarith

private lemma weightedCompletion_swap_le {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (J : Finset ι) (X A B Y : List ι)
    (hnd : (X ++ A ++ B ++ Y).Nodup)
    (hmem : ∀ j, j ∈ X ++ A ++ B ++ Y ↔ j ∈ J)
    (hA_ne : A ≠ []) (hB_ne : B ≠ [])
    (hpA : ∀ j ∈ A, 0 < p j) (hpB : ∀ j ∈ B, 0 < p j)
    (hrho : crho p w A ≤ crho p w B) :
    SingleMachinePrec.Biclique.weightedCompletion p w J (X ++ B ++ A ++ Y) ≤
      SingleMachinePrec.Biclique.weightedCompletion p w J (X ++ A ++ B ++ Y) := by
  have hdiff := weightedCompletion_swap_diff p w J X A B Y hnd hmem
  have hpA_pos : 0 < (A.map p).sum := map_p_sum_pos p hA_ne hpA
  have hpB_pos : 0 < (B.map p).sum := map_p_sum_pos p hB_ne hpB
  have h_ineq : (A.map w).sum * (B.map p).sum ≤ (B.map w).sum * (A.map p).sum := by
    unfold crho at hrho
    rwa [div_le_div_iff₀ hpA_pos hpB_pos] at hrho
  linarith

private lemma weightedCompletion_swap_lt {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (J : Finset ι) (X A B Y : List ι)
    (hnd : (X ++ A ++ B ++ Y).Nodup)
    (hmem : ∀ j, j ∈ X ++ A ++ B ++ Y ↔ j ∈ J)
    (hA_ne : A ≠ []) (hB_ne : B ≠ [])
    (hpA : ∀ j ∈ A, 0 < p j) (hpB : ∀ j ∈ B, 0 < p j)
    (hrho : crho p w A < crho p w B) :
    SingleMachinePrec.Biclique.weightedCompletion p w J (X ++ B ++ A ++ Y) <
      SingleMachinePrec.Biclique.weightedCompletion p w J (X ++ A ++ B ++ Y) := by
  have hdiff := weightedCompletion_swap_diff p w J X A B Y hnd hmem
  have hpA_pos : 0 < (A.map p).sum := map_p_sum_pos p hA_ne hpA
  have hpB_pos : 0 < (B.map p).sum := map_p_sum_pos p hB_ne hpB
  have h_ineq : (A.map w).sum * (B.map p).sum < (B.map w).sum * (A.map p).sum := by
    unfold crho at hrho
    rwa [div_lt_div_iff₀ hpA_pos hpB_pos] at hrho
  linarith

private lemma weightedCompletion_middle_diff {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (N : Finset ι) (A m₁ m₂ C : List ι)
    (hnd : (A ++ m₂ ++ C).Nodup)
    (hmem : ∀ j, j ∈ A ++ m₂ ++ C ↔ j ∈ N)
    (hperm : m₁.Perm m₂) :
    SingleMachinePrec.Biclique.weightedCompletion p w N (A ++ m₂ ++ C) -
      SingleMachinePrec.Biclique.weightedCompletion p w N (A ++ m₁ ++ C) =
      SingleMachinePrec.Biclique.weightedCompletion p w m₂.toFinset m₂ -
        SingleMachinePrec.Biclique.weightedCompletion p w m₂.toFinset m₁ := by
  have hnd_Am₂ : (A ++ m₂).Nodup := (List.nodup_append.mp hnd).1
  have hdisj_Am₂ : Disjoint A.toFinset m₂.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxA hxm₂
    exact (List.nodup_append.mp hnd_Am₂).2.2 x (List.mem_toFinset.mp hxA) x (List.mem_toFinset.mp hxm₂) rfl
  have hdisj_Am₂_C : Disjoint (A.toFinset ∪ m₂.toFinset) C.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxAm₂ hxC
    have hx_mem : x ∈ A ++ m₂ := by
      rcases Finset.mem_union.mp hxAm₂ with hxA | hxm₂
      · exact List.mem_append_left _ (List.mem_toFinset.mp hxA)
      · exact List.mem_append_right _ (List.mem_toFinset.mp hxm₂)
    exact (List.nodup_append.mp hnd).2.2 x hx_mem x (List.mem_toFinset.mp hxC) rfl
  have hN_eq : N = (A.toFinset ∪ m₂.toFinset) ∪ C.toFinset := by
    ext j
    simp only [← hmem, List.mem_append, Finset.mem_union, List.mem_toFinset]
  have hm₁_mem : ∀ x, x ∈ m₁ ↔ x ∈ m₂.toFinset :=
    fun x => hperm.mem_iff.trans List.mem_toFinset.symm
  have h1 := weightedCompletion_append p w hdisj_Am₂_C (l₁ := A ++ m₁) (l₂ := C)
    (fun j => by simp [List.mem_append, Finset.mem_union, hm₁_mem])
  have h2 := weightedCompletion_append p w hdisj_Am₂ (l₁ := A) (l₂ := m₁)
    (fun j => by simp)
  have h3 := weightedCompletion_append p w hdisj_Am₂_C (l₁ := A ++ m₂) (l₂ := C)
    (fun j => by simp [List.mem_append, Finset.mem_union])
  have h4 := weightedCompletion_append p w hdisj_Am₂ (l₁ := A) (l₂ := m₂)
    (fun j => by simp)
  have hpsum : ((A ++ m₁).map p).sum = ((A ++ m₂).map p).sum := by
    simp only [List.map_append, List.sum_append, (hperm.map p).sum_eq]
  rw [hN_eq, h1, h2, h3, h4, hpsum]
  linarith

private lemma weightedCompletion_middle_le {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (N : Finset ι) (A m₁ m₂ C : List ι)
    (hnd : (A ++ m₂ ++ C).Nodup)
    (hmem : ∀ j, j ∈ A ++ m₂ ++ C ↔ j ∈ N)
    (hperm : m₁.Perm m₂)
    (hle : SingleMachinePrec.Biclique.weightedCompletion p w m₂.toFinset m₁ ≤
      SingleMachinePrec.Biclique.weightedCompletion p w m₂.toFinset m₂) :
    SingleMachinePrec.Biclique.weightedCompletion p w N (A ++ m₁ ++ C) ≤
      SingleMachinePrec.Biclique.weightedCompletion p w N (A ++ m₂ ++ C) := by
  have hdiff := weightedCompletion_middle_diff p w N A m₁ m₂ C hnd hmem hperm
  linarith

private lemma weightedCompletion_middle_lt {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (N : Finset ι) (A m₁ m₂ C : List ι)
    (hnd : (A ++ m₂ ++ C).Nodup)
    (hmem : ∀ j, j ∈ A ++ m₂ ++ C ↔ j ∈ N)
    (hperm : m₁.Perm m₂)
    (hlt : SingleMachinePrec.Biclique.weightedCompletion p w m₂.toFinset m₁ <
      SingleMachinePrec.Biclique.weightedCompletion p w m₂.toFinset m₂) :
    SingleMachinePrec.Biclique.weightedCompletion p w N (A ++ m₁ ++ C) <
      SingleMachinePrec.Biclique.weightedCompletion p w N (A ++ m₂ ++ C) := by
  have hdiff := weightedCompletion_middle_diff p w N A m₁ m₂ C hnd hmem hperm
  linarith

private lemma forall_lt_of_no_consecutive_le {ι : Type*} (p w : ι → ℝ) :
    ∀ (b₀ : List ι) (bs : List (List ι)),
      (∀ B₁ b₁ b₂ B₂, b₀ :: bs = B₁ ++ [b₁, b₂] ++ B₂ → crho p w b₂ < crho p w b₁) →
      ∀ b ∈ bs, crho p w b < crho p w b₀
  | _, [], _, _, hb => by cases hb
  | b₀, b₁ :: bs, h, b, hb => by
    have h01 : crho p w b₁ < crho p w b₀ := h [] b₀ b₁ bs rfl
    rcases List.mem_cons.mp hb with rfl | hbs
    · exact h01
    · have ih := forall_lt_of_no_consecutive_le p w b₁ bs
        (fun B₁ x y B₂ heq => h (b₀ :: B₁) x y B₂ (by simp [heq])) b hbs
      exact lt_trans ih h01

private lemma sum_w_lt_of_forall_crho_lt {ι : Type*} (p w : ι → ℝ) (c : ℝ) :
    ∀ (bs : List (List ι)), bs ≠ [] →
      (∀ b ∈ bs, b ≠ []) →
      (∀ j ∈ bs.flatten, 0 < p j) →
      (∀ b ∈ bs, crho p w b < c) →
      (bs.flatten.map w).sum < c * (bs.flatten.map p).sum
  | [], hne, _, _, _ => absurd rfl hne
  | [b], _, hb_ne, hp, hlt => by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    have hpb : 0 < (b.map p).sum := map_p_sum_pos p (hb_ne b List.mem_cons_self)
      (fun j hj => hp j (by simp [hj]))
    have hcb : (b.map w).sum / (b.map p).sum < c := hlt b List.mem_cons_self
    rwa [div_lt_iff₀ hpb] at hcb
  | b₁ :: b₂ :: bs, _, hb_ne, hp, hlt => by
    have hpb₁ : 0 < (b₁.map p).sum := map_p_sum_pos p (hb_ne b₁ List.mem_cons_self)
      (fun j hj => hp j (List.mem_append_left _ hj))
    have hcb₁ : (b₁.map w).sum < c * (b₁.map p).sum := by
      have h := hlt b₁ List.mem_cons_self
      unfold crho at h
      rwa [div_lt_iff₀ hpb₁] at h
    have ih := sum_w_lt_of_forall_crho_lt p w c (b₂ :: bs) (List.cons_ne_nil _ _)
      (fun b hb => hb_ne b (List.mem_cons_of_mem b₁ hb))
      (fun j hj => hp j (List.mem_append_right _ hj))
      (fun b hb => hlt b (List.mem_cons_of_mem b₁ hb))
    simp only [List.flatten_cons, List.map_append, List.sum_append] at ih ⊢
    linarith

private lemma exists_consecutive_le_of_isComposite {ι : Type*} (p w : ι → ℝ)
    (B : List (List ι)) (hlen : 2 ≤ B.length)
    (hb_ne : ∀ b ∈ B, b ≠ []) (hp : ∀ j ∈ B.flatten, 0 < p j)
    (hcomp : IsComposite p w B.flatten) :
    ∃ B₁ b₁ b₂ B₂, B = B₁ ++ [b₁, b₂] ++ B₂ ∧ crho p w b₁ ≤ crho p w b₂ := by
  by_contra hno
  push Not at hno
  rcases B with _ | ⟨b₀, _ | ⟨b₁, bs⟩⟩
  · simp at hlen
  · simp at hlen
  · have hall : ∀ b ∈ b₁ :: bs, crho p w b < crho p w b₀ :=
      forall_lt_of_no_consecutive_le p w b₀ (b₁ :: bs) hno
    have hlt := sum_w_lt_of_forall_crho_lt p w (crho p w b₀) (b₁ :: bs) (List.cons_ne_nil _ _)
      (fun b hb => hb_ne b (List.mem_cons_of_mem b₀ hb))
      (fun j hj => hp j (List.mem_append_right _ hj))
      hall
    have hpb₀ : 0 < (b₀.map p).sum := map_p_sum_pos p (hb_ne b₀ List.mem_cons_self)
      (fun j hj => hp j (List.mem_append_left _ hj))
    have heq₀ : (b₀.map w).sum = crho p w b₀ * (b₀.map p).sum := by
      unfold crho
      exact (div_mul_cancel₀ _ (ne_of_gt hpb₀)).symm
    have h_all_p : 0 < ((b₀ :: b₁ :: bs).flatten.map p).sum :=
      map_p_sum_pos p hcomp.1 hp
    have hb₁_pos : 0 < b₁.length :=
      List.length_pos_iff.mpr (hb_ne b₁ (List.mem_cons_of_mem b₀ List.mem_cons_self))
    have hb₀_ne_all : b₀ ≠ (b₀ :: b₁ :: bs).flatten := by
      intro heq
      have hlen_eq := congrArg List.length heq
      simp only [List.flatten_cons, List.length_append] at hlen_eq
      omega
    have hle : crho p w b₀ ≤
        (((b₀ :: b₁ :: bs).flatten).map w).sum / (((b₀ :: b₁ :: bs).flatten).map p).sum :=
      hcomp.2.2 b₀ ⟨(b₁ :: bs).flatten, rfl⟩ (hb_ne b₀ List.mem_cons_self) hb₀_ne_all
    rw [le_div_iff₀ h_all_p] at hle
    simp only [List.flatten_cons, List.map_append, List.sum_append] at hle hlt
    linarith

private lemma split_of_filter_fst_cons {α : Type*} :
    ∀ (P : List (Bool × α)) (L₁ : List α) (b : α) (L₂ : List α),
      (P.filter Prod.fst).map Prod.snd = L₁ ++ b :: L₂ →
      ∃ X Z : List (Bool × α),
        P = X ++ [(true, b)] ++ Z ∧
        (X.filter Prod.fst).map Prod.snd = L₁ ∧
        (Z.filter Prod.fst).map Prod.snd = L₂
  | [], L₁, b, L₂, h => by cases L₁ <;> simp at h
  | (false, a) :: P, L₁, b, L₂, h => by
    simp only [List.filter_cons] at h
    rcases split_of_filter_fst_cons P L₁ b L₂ h with ⟨X, Z, rfl, hX, hZ⟩
    exact ⟨(false, a) :: X, Z, rfl, hX, hZ⟩
  | (true, a) :: P, [], b, L₂, h => by
    simp at h
    rcases h with ⟨rfl, hP⟩
    exact ⟨[], P, rfl, rfl, hP⟩
  | (true, a) :: P, l :: L₁, b, L₂, h => by
    simp at h
    rcases h with ⟨rfl, hP⟩
    rcases split_of_filter_fst_cons P L₁ b L₂ hP with ⟨X, Z, rfl, hX, hZ⟩
    exact ⟨(true, a) :: X, Z, rfl, by simp [hX], hZ⟩

private lemma filter_fst_empty_of_map_snd_eq_nil {α : Type*} {U : List (Bool × α)}
    (h : (U.filter Prod.fst).map Prod.snd = []) : U.filter Prod.fst = [] :=
  List.map_eq_nil_iff.mp h

private lemma filter_not_fst_of_map_snd_eq_nil {α : Type*} {U : List (Bool × α)}
    (h : (U.filter Prod.fst).map Prod.snd = []) : U.filter (fun x => !x.1) = U := by
  have h1 := filter_fst_empty_of_map_snd_eq_nil h
  rw [List.filter_eq_self]
  intro x hx
  cases hx1 : x.1
  · rfl
  · have : x ∈ U.filter Prod.fst := List.mem_filter.mpr ⟨hx, hx1⟩
    rw [h1] at this
    cases this

private lemma flatten_append_two {α : Type*} (B₁ B₂ : List (List α)) (b₁ b₂ : List α) :
    (B₁ ++ [b₁ ++ b₂] ++ B₂).flatten = (B₁ ++ [b₁, b₂] ++ B₂).flatten := by
  simp [List.append_assoc]

private lemma perm_middle_swap {α : Type*} (X A B Y : List α) :
    (X ++ B ++ A ++ Y).Perm (X ++ A ++ B ++ Y) := by
  rw [List.append_assoc X B A, List.append_assoc X A B]
  exact List.Perm.append_right Y (List.Perm.append_left X List.perm_append_comm)

private lemma exists_last_elem {α : Type*} :
    ∀ (l : List α), l ≠ [] → ∃ init last, l = init ++ [last]
  | [], h => absurd rfl h
  | [a], _ => ⟨[], a, rfl⟩
  | a :: b :: bs, _ => by
    rcases exists_last_elem (b :: bs) (List.cons_ne_nil _ _) with ⟨init, last, heq⟩
    exact ⟨a :: init, last, by simp [heq]⟩

private lemma merge_one_composite {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (J : Finset ι) (hp : ∀ j ∈ J, 0 < p j) :
    ∀ (n : ℕ) (P : List (Bool × List ι)), P.length = n →
      ((P.map Prod.snd).flatten).Nodup →
      (∀ j, j ∈ (P.map Prod.snd).flatten ↔ j ∈ J) →
      (∀ x ∈ P, x.2 ≠ []) →
      IsComposite p w ((P.filter Prod.fst).map Prod.snd).flatten →
      ∃ R₁ R₂ : List (List ι),
        R₁ ++ R₂ = (P.filter (fun x => !x.1)).map Prod.snd ∧
        (R₁ ++ [((P.filter Prod.fst).map Prod.snd).flatten] ++ R₂).flatten.Perm
          ((P.map Prod.snd).flatten) ∧
        SingleMachinePrec.Biclique.weightedCompletion p w J
            (R₁ ++ [((P.filter Prod.fst).map Prod.snd).flatten] ++ R₂).flatten ≤
          SingleMachinePrec.Biclique.weightedCompletion p w J ((P.map Prod.snd).flatten) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hlen hnd hmem hne hcomp
    set B := (P.filter Prod.fst).map Prod.snd with hB_def
    by_cases hB_len : 2 ≤ B.length
    · have hb_ne : ∀ b ∈ B, b ≠ [] := by
        intro b hb
        rcases List.mem_map.mp hb with ⟨x, hx, rfl⟩
        exact hne x (List.mem_of_mem_filter hx)
      have hpB : ∀ j ∈ B.flatten, 0 < p j := by
        intro j hj
        rcases List.mem_flatten.mp hj with ⟨b, hb, hjb⟩
        rcases List.mem_map.mp hb with ⟨x, hx, rfl⟩
        exact hp j ((hmem j).mp (List.mem_flatten.mpr ⟨x.2, List.mem_map_of_mem (List.mem_of_mem_filter hx), hjb⟩))
      rcases exists_consecutive_le_of_isComposite p w B hB_len hb_ne hpB hcomp with
        ⟨B₁, b₁, b₂, B₂, hB_eq, hrho12⟩
      have hB_eq1 : (P.filter Prod.fst).map Prod.snd = B₁ ++ b₁ :: (b₂ :: B₂) := by
        simpa [List.append_assoc] using hB_eq
      rcases split_of_filter_fst_cons P B₁ b₁ (b₂ :: B₂) hB_eq1 with ⟨X, Z, rfl, hX, hZ⟩
      have hZ_eq : (Z.filter Prod.fst).map Prod.snd = [] ++ b₂ :: B₂ := by simpa using hZ
      rcases split_of_filter_fst_cons Z [] b₂ B₂ hZ_eq with ⟨U, Y, rfl, hU, hY⟩
      have hU_fst : U.filter Prod.fst = [] := filter_fst_empty_of_map_snd_eq_nil hU
      have hb₁_ne : b₁ ≠ [] := hne (true, b₁) (by simp)
      have hb₂_ne : b₂ ≠ [] := hne (true, b₂) (by simp)
      have hb₁₂_ne : b₁ ++ b₂ ≠ [] := List.append_ne_nil_of_left_ne_nil hb₁_ne b₂
      set x_f := (X.map Prod.snd).flatten
      set u_f := (U.map Prod.snd).flatten
      set y_f := (Y.map Prod.snd).flatten
      have hP_flat : ((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten =
          x_f ++ b₁ ++ u_f ++ b₂ ++ y_f := by
        simp [x_f, u_f, y_f, List.append_assoc]
      have hpb₁ : ∀ j ∈ b₁, 0 < p j := fun j hj =>
        hp j ((hmem j).mp (by rw [hP_flat]; simp [hj]))
      have hpb₂ : ∀ j ∈ b₂, 0 < p j := fun j hj =>
        hp j ((hmem j).mp (by rw [hP_flat]; simp [hj]))
      have hpu : ∀ j ∈ u_f, 0 < p j := fun j hj =>
        hp j ((hmem j).mp (by rw [hP_flat]; simp [hj]))
      by_cases hu_case : u_f = [] ∨ crho p w u_f ≤ crho p w b₂
      · let P' := X ++ [(true, b₁ ++ b₂)] ++ U ++ Y
        have hP'_len : P'.length < n := by subst hlen; simp [P']
        have hP'_flat : (P'.map Prod.snd).flatten = (x_f ++ b₁) ++ b₂ ++ u_f ++ y_f := by
          simp [P', x_f, u_f, y_f, List.append_assoc]
        have hP_flat' : (((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten) =
            (x_f ++ b₁) ++ u_f ++ b₂ ++ y_f := by
          simp [x_f, u_f, y_f, List.append_assoc]
        have hperm_step : (P'.map Prod.snd).flatten.Perm
            (((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten) := by
          rw [hP'_flat, hP_flat']
          exact perm_middle_swap (x_f ++ b₁) u_f b₂ y_f
        have hwc_step : SingleMachinePrec.Biclique.weightedCompletion p w J (P'.map Prod.snd).flatten ≤
            SingleMachinePrec.Biclique.weightedCompletion p w J
              (((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten) := by
          rcases hu_case with hu_nil | hrho_ub₂
          · rw [hP'_flat, hP_flat', hu_nil]; simp
          · by_cases hu_nil : u_f = []
            · rw [hP'_flat, hP_flat', hu_nil]; simp
            · rw [hP'_flat, hP_flat']
              exact weightedCompletion_swap_le p w J (x_f ++ b₁) u_f b₂ y_f
                (hP_flat' ▸ hnd) (fun j => by rw [← hP_flat']; exact hmem j)
                hu_nil hb₂_ne hpu hpb₂ hrho_ub₂
        have hP'_B : ((P'.filter Prod.fst).map Prod.snd).flatten = B.flatten := by
          have : (P'.filter Prod.fst).map Prod.snd = B₁ ++ [b₁ ++ b₂] ++ B₂ := by
            simp [P', List.filter_append, hX, hU_fst, hY, List.append_assoc]
          rw [this, hB_eq, flatten_append_two]
        have hP'_R : (P'.filter (fun x => !x.1)).map Prod.snd =
            ((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).filter (fun x => !x.1)).map Prod.snd := by
          simp [P', List.filter_append, List.append_assoc]
        have hP'_ne : ∀ x ∈ P', x.2 ≠ [] := by
          intro x hx
          simp only [P', List.mem_append, List.mem_singleton] at hx
          rcases hx with ((hx | rfl) | hx) | hx
          · exact hne x (by simp [hx])
          · exact hb₁₂_ne
          · exact hne x (by simp [hx])
          · exact hne x (by simp [hx])
        rcases ih P'.length hP'_len P' rfl (hperm_step.nodup_iff.mpr hnd)
          (fun j => hperm_step.mem_iff.trans (hmem j)) hP'_ne (hP'_B.symm ▸ hcomp) with
          ⟨R₁, R₂, hR_eq, hR_perm, hR_wc⟩
        rw [hP'_R] at hR_eq
        rw [hP'_B] at hR_perm hR_wc
        exact ⟨R₁, R₂, hR_eq, hR_perm.trans hperm_step, le_trans hR_wc hwc_step⟩
      · push Not at hu_case
        have hu_ne : u_f ≠ [] := hu_case.1
        have hrho_b₁u : crho p w b₁ ≤ crho p w u_f := le_of_lt (lt_of_le_of_lt hrho12 hu_case.2)
        let P' := X ++ U ++ [(true, b₁ ++ b₂)] ++ Y
        have hP'_len : P'.length < n := by subst hlen; simp [P']
        have hP'_flat : (P'.map Prod.snd).flatten = x_f ++ u_f ++ b₁ ++ (b₂ ++ y_f) := by
          simp [P', x_f, u_f, y_f, List.append_assoc]
        have hP_flat' : (((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten) =
            x_f ++ b₁ ++ u_f ++ (b₂ ++ y_f) := by
          simp [x_f, u_f, y_f, List.append_assoc]
        have hperm_step : (P'.map Prod.snd).flatten.Perm
            (((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten) := by
          rw [hP'_flat, hP_flat']
          exact perm_middle_swap x_f b₁ u_f (b₂ ++ y_f)
        have hwc_step : SingleMachinePrec.Biclique.weightedCompletion p w J (P'.map Prod.snd).flatten ≤
            SingleMachinePrec.Biclique.weightedCompletion p w J
              (((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten) := by
          rw [hP'_flat, hP_flat']
          exact weightedCompletion_swap_le p w J x_f b₁ u_f (b₂ ++ y_f)
            (hP_flat' ▸ hnd) (fun j => by rw [← hP_flat']; exact hmem j)
            hb₁_ne hu_ne hpb₁ hpu hrho_b₁u
        have hP'_B : ((P'.filter Prod.fst).map Prod.snd).flatten = B.flatten := by
          have : (P'.filter Prod.fst).map Prod.snd = B₁ ++ [b₁ ++ b₂] ++ B₂ := by
            simp [P', List.filter_append, hX, hU_fst, hY, List.append_assoc]
          rw [this, hB_eq, flatten_append_two]
        have hP'_R : (P'.filter (fun x => !x.1)).map Prod.snd =
            ((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).filter (fun x => !x.1)).map Prod.snd := by
          simp [P', List.filter_append, List.append_assoc]
        have hP'_ne : ∀ x ∈ P', x.2 ≠ [] := by
          intro x hx
          simp only [P', List.mem_append, List.mem_singleton] at hx
          rcases hx with ((hx | hx) | rfl) | hx
          · exact hne x (by simp [hx])
          · exact hne x (by simp [hx])
          · exact hb₁₂_ne
          · exact hne x (by simp [hx])
        rcases ih P'.length hP'_len P' rfl (hperm_step.nodup_iff.mpr hnd)
          (fun j => hperm_step.mem_iff.trans (hmem j)) hP'_ne (hP'_B.symm ▸ hcomp) with
          ⟨R₁, R₂, hR_eq, hR_perm, hR_wc⟩
        rw [hP'_R] at hR_eq
        rw [hP'_B] at hR_perm hR_wc
        exact ⟨R₁, R₂, hR_eq, hR_perm.trans hperm_step, le_trans hR_wc hwc_step⟩
    · rcases B with _ | ⟨c, _ | ⟨d, bs⟩⟩
      · exact absurd rfl hcomp.1
      · have hB_eq : (P.filter Prod.fst).map Prod.snd = [] ++ c :: [] := hB_def.symm
        rcases split_of_filter_fst_cons P [] c [] hB_eq with ⟨X, Z, rfl, hX, hZ⟩
        have hX_not : X.filter (fun x => !x.1) = X := filter_not_fst_of_map_snd_eq_nil hX
        have hZ_not : Z.filter (fun x => !x.1) = Z := filter_not_fst_of_map_snd_eq_nil hZ
        refine ⟨X.map Prod.snd, Z.map Prod.snd, ?_, ?_, ?_⟩
        · simp [List.filter_append, hX_not, hZ_not]
        · have : (X.map Prod.snd ++ [[c].flatten] ++ Z.map Prod.snd).flatten =
              (((X ++ [(true, c)] ++ Z).map Prod.snd).flatten) := by simp
          rw [this]
        · have : (X.map Prod.snd ++ [[c].flatten] ++ Z.map Prod.snd).flatten =
              (((X ++ [(true, c)] ++ Z).map Prod.snd).flatten) := by simp
          rw [this]
      · simp at hB_len

private lemma merge_one_composite_right {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (J : Finset ι) (hp : ∀ j ∈ J, 0 < p j) :
    ∀ (n : ℕ) (P : List (Bool × List ι)), P.length = n →
      ((P.map Prod.snd).flatten).Nodup →
      (∀ j, j ∈ (P.map Prod.snd).flatten ↔ j ∈ J) →
      (∀ x ∈ P, x.2 ≠ []) →
      (∃ init b_last, P = init ++ [(true, b_last)]) →
      IsComposite p w ((P.filter Prod.fst).map Prod.snd).flatten →
      ∃ R₁ R₂ : List (List ι),
        R₁ ++ R₂ = (P.filter (fun x => !x.1)).map Prod.snd ∧
        (R₁ ++ [((P.filter Prod.fst).map Prod.snd).flatten] ++ R₂).flatten.Perm
          ((P.map Prod.snd).flatten) ∧
        ((SingleMachinePrec.Biclique.weightedCompletion p w J
            (R₁ ++ [((P.filter Prod.fst).map Prod.snd).flatten] ++ R₂).flatten <
          SingleMachinePrec.Biclique.weightedCompletion p w J ((P.map Prod.snd).flatten)) ∨
         (R₂ = [] ∧ SingleMachinePrec.Biclique.weightedCompletion p w J
            (R₁ ++ [((P.filter Prod.fst).map Prod.snd).flatten] ++ R₂).flatten ≤
          SingleMachinePrec.Biclique.weightedCompletion p w J ((P.map Prod.snd).flatten))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hlen hnd hmem hne hlast hcomp
    set B := (P.filter Prod.fst).map Prod.snd with hB_def
    by_cases hB_len : 2 ≤ B.length
    · have hb_ne : ∀ b ∈ B, b ≠ [] := by
        intro b hb
        rcases List.mem_map.mp hb with ⟨x, hx, rfl⟩
        exact hne x (List.mem_of_mem_filter hx)
      have hpB : ∀ j ∈ B.flatten, 0 < p j := by
        intro j hj
        rcases List.mem_flatten.mp hj with ⟨b, hb, hjb⟩
        rcases List.mem_map.mp hb with ⟨x, hx, rfl⟩
        exact hp j ((hmem j).mp (List.mem_flatten.mpr ⟨x.2, List.mem_map_of_mem (List.mem_of_mem_filter hx), hjb⟩))
      rcases exists_consecutive_le_of_isComposite p w B hB_len hb_ne hpB hcomp with
        ⟨B₁, b₁, b₂, B₂, hB_eq, hrho12⟩
      have hB_eq1 : (P.filter Prod.fst).map Prod.snd = B₁ ++ b₁ :: (b₂ :: B₂) := by
        simpa [List.append_assoc] using hB_eq
      rcases split_of_filter_fst_cons P B₁ b₁ (b₂ :: B₂) hB_eq1 with ⟨X, Z, rfl, hX, hZ⟩
      have hZ_eq : (Z.filter Prod.fst).map Prod.snd = [] ++ b₂ :: B₂ := by simpa using hZ
      rcases split_of_filter_fst_cons Z [] b₂ B₂ hZ_eq with ⟨U, Y, rfl, hU, hY⟩
      have hU_fst : U.filter Prod.fst = [] := filter_fst_empty_of_map_snd_eq_nil hU
      have hb₁_ne : b₁ ≠ [] := hne (true, b₁) (by simp)
      have hb₂_ne : b₂ ≠ [] := hne (true, b₂) (by simp)
      have hb₁₂_ne : b₁ ++ b₂ ≠ [] := List.append_ne_nil_of_left_ne_nil hb₁_ne b₂
      set x_f := (X.map Prod.snd).flatten
      set u_f := (U.map Prod.snd).flatten
      set y_f := (Y.map Prod.snd).flatten
      have hP_flat : ((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten =
          x_f ++ b₁ ++ u_f ++ b₂ ++ y_f := by
        simp [x_f, u_f, y_f, List.append_assoc]
      have hpb₁ : ∀ j ∈ b₁, 0 < p j := fun j hj =>
        hp j ((hmem j).mp (by rw [hP_flat]; simp [hj]))
      have hpb₂ : ∀ j ∈ b₂, 0 < p j := fun j hj =>
        hp j ((hmem j).mp (by rw [hP_flat]; simp [hj]))
      have hpu : ∀ j ∈ u_f, 0 < p j := fun j hj =>
        hp j ((hmem j).mp (by rw [hP_flat]; simp [hj]))
      by_cases hu_case : u_f = [] ∨ crho p w b₁ ≤ crho p w u_f
      · let P' := X ++ U ++ [(true, b₁ ++ b₂)] ++ Y
        have hP'_len : P'.length < n := by subst hlen; simp [P']
        have hP'_flat : (P'.map Prod.snd).flatten = x_f ++ u_f ++ b₁ ++ (b₂ ++ y_f) := by
          simp [P', x_f, u_f, y_f, List.append_assoc]
        have hP_flat' : (((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten) =
            x_f ++ b₁ ++ u_f ++ (b₂ ++ y_f) := by
          simp [x_f, u_f, y_f, List.append_assoc]
        have hperm_step : (P'.map Prod.snd).flatten.Perm
            (((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten) := by
          rw [hP'_flat, hP_flat']
          exact perm_middle_swap x_f b₁ u_f (b₂ ++ y_f)
        have hwc_step : SingleMachinePrec.Biclique.weightedCompletion p w J (P'.map Prod.snd).flatten ≤
            SingleMachinePrec.Biclique.weightedCompletion p w J
              (((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten) := by
          rcases hu_case with hu_nil | hrho_b₁u
          · rw [hP'_flat, hP_flat', hu_nil]; simp
          · by_cases hu_nil : u_f = []
            · rw [hP'_flat, hP_flat', hu_nil]; simp
            · rw [hP'_flat, hP_flat']
              exact weightedCompletion_swap_le p w J x_f b₁ u_f (b₂ ++ y_f)
                (hP_flat' ▸ hnd) (fun j => by rw [← hP_flat']; exact hmem j)
                hb₁_ne hu_nil hpb₁ hpu hrho_b₁u
        have hP'_B : ((P'.filter Prod.fst).map Prod.snd).flatten = B.flatten := by
          have : (P'.filter Prod.fst).map Prod.snd = B₁ ++ [b₁ ++ b₂] ++ B₂ := by
            simp [P', List.filter_append, hX, hU_fst, hY, List.append_assoc]
          rw [this, hB_eq, flatten_append_two]
        have hP'_R : (P'.filter (fun x => !x.1)).map Prod.snd =
            ((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).filter (fun x => !x.1)).map Prod.snd := by
          simp [P', List.filter_append, List.append_assoc]
        have hP'_ne : ∀ x ∈ P', x.2 ≠ [] := by
          intro x hx
          simp only [P', List.mem_append, List.mem_singleton] at hx
          rcases hx with ((hx | hx) | rfl) | hx
          · exact hne x (by simp [hx])
          · exact hne x (by simp [hx])
          · exact hb₁₂_ne
          · exact hne x (by simp [hx])
        have hP'_last : ∃ init' b_last', P' = init' ++ [(true, b_last')] := by
          by_cases hY_nil : Y = []
          · exact ⟨X ++ U, b₁ ++ b₂, by simp [P', hY_nil]⟩
          · rcases exists_last_elem Y hY_nil with ⟨Y_init, y_last, rfl⟩
            rcases hlast with ⟨init, b_last, heq_last⟩
            have hy_eq : y_last = (true, b_last) := by
              have h1 : (X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ (Y_init ++ [y_last]))) =
                  (X ++ [(true, b₁)] ++ U ++ [(true, b₂)] ++ Y_init) ++ [y_last] := by
                simp [List.append_assoc]
              rw [h1] at heq_last
              exact List.singleton_inj.mp (List.append_inj_right' heq_last rfl)
            subst hy_eq
            exact ⟨X ++ U ++ [(true, b₁ ++ b₂)] ++ Y_init, b_last, by simp [P', List.append_assoc]⟩
        rcases ih P'.length hP'_len P' rfl (hperm_step.nodup_iff.mpr hnd)
          (fun j => hperm_step.mem_iff.trans (hmem j)) hP'_ne hP'_last (hP'_B.symm ▸ hcomp) with
          ⟨R₁, R₂, hR_eq, hR_perm, hR_res⟩
        rw [hP'_R] at hR_eq
        rw [hP'_B] at hR_perm hR_res
        refine ⟨R₁, R₂, hR_eq, hR_perm.trans hperm_step, ?_⟩
        rcases hR_res with hlt | ⟨hR₂_nil, hle⟩
        · exact Or.inl (lt_of_lt_of_le hlt hwc_step)
        · exact Or.inr ⟨hR₂_nil, le_trans hle hwc_step⟩
      · push Not at hu_case
        have hu_ne : u_f ≠ [] := hu_case.1
        have hrho_ub₂ : crho p w u_f < crho p w b₂ := lt_of_lt_of_le hu_case.2 hrho12
        let P' := X ++ [(true, b₁ ++ b₂)] ++ U ++ Y
        have hP'_flat : (P'.map Prod.snd).flatten = (x_f ++ b₁) ++ b₂ ++ u_f ++ y_f := by
          simp [P', x_f, u_f, y_f, List.append_assoc]
        have hP_flat' : (((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten) =
            (x_f ++ b₁) ++ u_f ++ b₂ ++ y_f := by
          simp [x_f, u_f, y_f, List.append_assoc]
        have hperm_step : (P'.map Prod.snd).flatten.Perm
            (((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten) := by
          rw [hP'_flat, hP_flat']
          exact perm_middle_swap (x_f ++ b₁) u_f b₂ y_f
        have hwc_step : SingleMachinePrec.Biclique.weightedCompletion p w J (P'.map Prod.snd).flatten <
            SingleMachinePrec.Biclique.weightedCompletion p w J
              (((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten) := by
          rw [hP'_flat, hP_flat']
          exact weightedCompletion_swap_lt p w J (x_f ++ b₁) u_f b₂ y_f
            (hP_flat' ▸ hnd) (fun j => by rw [← hP_flat']; exact hmem j)
            hu_ne hb₂_ne hpu hpb₂ hrho_ub₂
        have hP'_B : ((P'.filter Prod.fst).map Prod.snd).flatten = B.flatten := by
          have : (P'.filter Prod.fst).map Prod.snd = B₁ ++ [b₁ ++ b₂] ++ B₂ := by
            simp [P', List.filter_append, hX, hU_fst, hY, List.append_assoc]
          rw [this, hB_eq, flatten_append_two]
        have hP'_R : (P'.filter (fun x => !x.1)).map Prod.snd =
            ((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).filter (fun x => !x.1)).map Prod.snd := by
          simp [P', List.filter_append, List.append_assoc]
        have hP'_ne : ∀ x ∈ P', x.2 ≠ [] := by
          intro x hx
          simp only [P', List.mem_append, List.mem_singleton] at hx
          rcases hx with ((hx | rfl) | hx) | hx
          · exact hne x (by simp [hx])
          · exact hb₁₂_ne
          · exact hne x (by simp [hx])
          · exact hne x (by simp [hx])
        rcases merge_one_composite p w J hp P'.length P' rfl (hperm_step.nodup_iff.mpr hnd)
          (fun j => hperm_step.mem_iff.trans (hmem j)) hP'_ne (hP'_B.symm ▸ hcomp) with
          ⟨R₁, R₂, hR_eq, hR_perm, hR_wc⟩
        rw [hP'_R] at hR_eq
        rw [hP'_B] at hR_perm hR_wc
        exact ⟨R₁, R₂, hR_eq, hR_perm.trans hperm_step, Or.inl (lt_of_le_of_lt hR_wc hwc_step)⟩
    · rcases B with _ | ⟨c, _ | ⟨d, bs⟩⟩
      · exact absurd rfl hcomp.1
      · have hB_eq : (P.filter Prod.fst).map Prod.snd = [] ++ c :: [] := hB_def.symm
        rcases split_of_filter_fst_cons P [] c [] hB_eq with ⟨X, Z, rfl, hX, hZ⟩
        have hX_not : X.filter (fun x => !x.1) = X := filter_not_fst_of_map_snd_eq_nil hX
        have hZ_nil : Z = [] := by
          by_contra hZ_ne
          rcases exists_last_elem Z hZ_ne with ⟨Z_init, z_last, rfl⟩
          rcases hlast with ⟨init, b_last, heq_last⟩
          have hz_eq : z_last = (true, b_last) := by
            have h1 : (X ++ [(true, c)] ++ (Z_init ++ [z_last])) =
                (X ++ [(true, c)] ++ Z_init) ++ [z_last] := by
              simp [List.append_assoc]
            rw [h1] at heq_last
            exact List.singleton_inj.mp (List.append_inj_right' heq_last rfl)
          subst hz_eq
          have hmem_fst : (true, b_last) ∈ (Z_init ++ [(true, b_last)]).filter Prod.fst :=
            List.mem_filter.mpr ⟨by simp, rfl⟩
          rw [filter_fst_empty_of_map_snd_eq_nil hZ] at hmem_fst
          cases hmem_fst
        subst hZ_nil
        refine ⟨X.map Prod.snd, [], ?_, ?_, Or.inr ⟨rfl, ?_⟩⟩
        · simp [List.filter_append, hX_not]
        · have : (X.map Prod.snd ++ [[c].flatten] ++ []).flatten =
              (((X ++ [(true, c)] ++ []).map Prod.snd).flatten) := by simp
          rw [this]
        · have : (X.map Prod.snd ++ [[c].flatten] ++ []).flatten =
              (((X ++ [(true, c)] ++ []).map Prod.snd).flatten) := by simp
          rw [this]
      · simp at hB_len

private lemma crho_eq_rho_toFinset {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    {c : List ι} (hnd : c.Nodup) :
    crho p w c = rho p w c.toFinset := by
  unfold crho rho
  rw [sum_toFinset_eq_map_sum w hnd, sum_toFinset_eq_map_sum p hnd]

private lemma split_last_mem {α : Type*} (P : α → Bool) :
    ∀ (l : List α), (∃ x ∈ l, P x = true) →
      ∃ A m B, l = A ++ [m] ++ B ∧ P m = true ∧ ∀ x ∈ B, P x = false
  | [], ⟨_, hx, _⟩ => by cases hx
  | x :: xs, h => by
    by_cases hxs : ∃ y ∈ xs, P y = true
    · rcases split_last_mem P xs hxs with ⟨A, m, B, rfl, hm, hB⟩
      exact ⟨x :: A, m, B, rfl, hm, hB⟩
    · push Not at hxs
      rcases h with ⟨y, hy, hPy⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · refine ⟨[], y, xs, rfl, hPy, ?_⟩
        intro z hz
        exact Bool.eq_false_iff.mpr (hxs z hz)
      · exact absurd hPy (hxs y hy')

private lemma prefix_of_filter {α : Type*} (P : α → Bool) :
    ∀ (l q : List α), q <+: l.filter P → ∃ pref : List α, pref <+: l ∧ pref.filter P = q
  | l, [], _ => ⟨[], List.nil_prefix, rfl⟩
  | [], a :: q, hq => by simp at hq
  | x :: xs, a :: q, hq => by
    by_cases hx : P x = true
    · rw [List.filter_cons_of_pos hx] at hq
      rcases hq with ⟨t, ht⟩
      have hxa : x = a := (List.cons.inj ht).1.symm
      have hqt : q <+: xs.filter P := ⟨t, (List.cons.inj ht).2⟩
      rcases prefix_of_filter P xs q hqt with ⟨pref, ⟨t', rfl⟩, hfilt⟩
      exact ⟨x :: pref, ⟨t', rfl⟩, by rw [List.filter_cons_of_pos hx, hfilt, hxa]⟩
    · rw [List.filter_cons_of_neg hx] at hq
      rcases prefix_of_filter P xs (a :: q) hq with ⟨pref, ⟨t', rfl⟩, hfilt⟩
      exact ⟨x :: pref, ⟨t', rfl⟩, by rw [List.filter_cons_of_neg hx, hfilt]⟩

private lemma map_singleton_flatten {α : Type*} :
    ∀ (l : List α), (l.map (fun x => [x])).flatten = l
  | [] => rfl
  | x :: xs => by simp [map_singleton_flatten xs]

private lemma filter_fst_map_singleton {α : Type*} (P : α → Bool) :
    ∀ (l : List α),
      (((l.map (fun x => (P x, [x]))).filter Prod.fst).map Prod.snd).flatten = l.filter P
  | [] => rfl
  | x :: xs => by
    by_cases hx : P x = true
    · simp [hx, filter_fst_map_singleton P xs]
    · have hxf : P x = false := Bool.eq_false_iff.mpr hx
      simp [hxf, filter_fst_map_singleton P xs]

private lemma filter_not_fst_map_singleton {α : Type*} (P : α → Bool) :
    ∀ (l : List α),
      ((l.map (fun x => (P x, [x]))).filter (fun x => !x.1)).map Prod.snd =
        (l.filter (fun x => !P x)).map (fun x => [x])
  | [] => rfl
  | x :: xs => by
    by_cases hx : P x = true
    · simp [hx, filter_not_fst_map_singleton P xs]
    · have hxf : P x = false := Bool.eq_false_iff.mpr hx
      simp [hxf, filter_not_fst_map_singleton P xs]

private lemma rel_of_pairwise_filter {α : Type*} (P : α → Bool) (R : α → α → Prop) :
    ∀ (l : List α), (l.filter P).Pairwise R →
      l.Pairwise (fun x y => P x = true → P y = true → R x y)
  | [], _ => List.Pairwise.nil
  | a :: as, h => by
    rw [List.pairwise_cons]
    by_cases ha : P a = true
    · rw [List.filter_cons_of_pos ha, List.pairwise_cons] at h
      refine ⟨fun y hy _ hyP => h.1 y (List.mem_filter.mpr ⟨hy, hyP⟩),
              rel_of_pairwise_filter P R as h.2⟩
    · rw [List.filter_cons_of_neg ha] at h
      refine ⟨fun y _ haP _ => absurd haP ha,
              rel_of_pairwise_filter P R as h⟩

private lemma pairwise_and {α : Type*} {R₁ R₂ : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R₁ → l.Pairwise R₂ → l.Pairwise (fun x y => R₁ x y ∧ R₂ x y)
  | [], _, _ => List.Pairwise.nil
  | a :: as, h₁, h₂ => by
    rw [List.pairwise_cons] at h₁ h₂ ⊢
    exact ⟨fun y hy => ⟨h₁.1 y hy, h₂.1 y hy⟩, pairwise_and h₁.2 h₂.2⟩

private lemma pairwise_imp_of_mem {α : Type*} {R₁ R₂ : α → α → Prop} {l : List α}
    (h : l.Pairwise R₁) (himp : ∀ x ∈ l, ∀ y ∈ l, R₁ x y → R₂ x y) :
    l.Pairwise R₂ := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a as ih =>
    rw [List.pairwise_cons] at h ⊢
    exact ⟨fun y hy => himp a List.mem_cons_self y (List.mem_cons_of_mem a hy) (h.1 y hy),
           ih h.2 (fun x hx y hy => himp x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy))⟩

private lemma pairwise_middle_perm {α : Type*} (R : α → α → Prop) (A m₁ m₂ C : List α)
    (h : (A ++ m₂ ++ C).Pairwise R) (hperm : m₁.Perm m₂) (hm₁ : m₁.Pairwise R) :
    (A ++ m₁ ++ C).Pairwise R := by
  rw [List.append_assoc, List.pairwise_append] at h ⊢
  rcases h with ⟨hA, hm₂C, hA_m₂C⟩
  rw [List.pairwise_append] at hm₂C ⊢
  rcases hm₂C with ⟨_, hC, hm₂_C⟩
  refine ⟨hA, ⟨hm₁, hC, fun x hx y hy => hm₂_C x (hperm.subset hx) y hy⟩, fun x hx y hy => ?_⟩
  rcases List.mem_append.mp hy with hym₁ | hyC
  · exact hA_m₂C x hx y (List.mem_append_left _ (hperm.subset hym₁))
  · exact hA_m₂C x hx y (List.mem_append_right _ hyC)

private lemma transGen_mono {ι : Type*} {G₁ G₂ : ι → ι → Prop}
    (h : ∀ x y, G₁ x y → G₂ x y) {a b : ι} (htr : Relation.TransGen G₁ a b) :
    Relation.TransGen G₂ a b := by
  induction htr with
  | single hxy => exact .single (h _ _ hxy)
  | tail _ hbc ih => exact .tail ih (h _ _ hbc)

private lemma transGen_restrict_upward {ι : Type*} (G : ι → ι → Prop) (C : Finset ι)
    (hup : ∀ x y, x ∈ C → G x y → y ∈ C) {a b : ι}
    (ha : a ∈ C) (htr : Relation.TransGen G a b) :
    b ∈ C ∧ Relation.TransGen (fun x y => x ∈ C ∧ y ∈ C ∧ G x y) a b := by
  induction htr with
  | @single y hxy =>
    have hy : y ∈ C := hup a y ha hxy
    exact ⟨hy, .single ⟨ha, hy, hxy⟩⟩
  | @tail z y _ hzy ih =>
    have hy : y ∈ C := hup z y ih.1 hzy
    exact ⟨hy, .tail ih.2 ⟨ih.1, hy, hzy⟩⟩

private lemma theorem_1_aux {ι : Type*} [DecidableEq ι] :
    ∀ (n : ℕ) (N : Finset ι) (G : ι → ι → Prop)
      (_ : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (_ : ∀ j, ¬ Relation.TransGen G j j)
      (p w : ι → ℝ) (_ : ∀ j ∈ N, 0 < p j)
      (M : Finset ι), M.card = n → IsModule G N M →
      ∀ (σ : List ι), SingleMachinePrec.Biclique.IsOptimalSchedule G p w M σ →
      ∃ τ : List ι, SingleMachinePrec.Biclique.IsOptimalSchedule G p w N τ ∧
        τ.filter (· ∈ M) = σ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro N G hGN hacyc p w hp M hcard hM σ hσ
    rcases exists_rhoMaximal_local G p w M hM.1 with ⟨I_star, hI_star⟩
    have hI_star_init : IsInitialSet G M I_star := hI_star.1
    have hI_star_ne : I_star.Nonempty := hI_star.2.1
    have hI_star_M : I_star ⊆ M := hI_star_init.1
    have hMN : M ⊆ N := hM.2.1
    have hI_star_max : ∀ I', IsInitialSet G M I' → I'.Nonempty → rho p w I' ≤ rho p w I_star :=
      hI_star.2.2
    have hσ_feas : LawlerPrec.MinMax.IsFeasible G M σ := hσ.1
    have hσ_nd : σ.Nodup := hσ_feas.1.1
    have hσ_mem : ∀ j, j ∈ σ ↔ j ∈ M := hσ_feas.1.2
    have hσ_pair : σ.Pairwise (fun a b => ¬ G b a) := hσ_feas.2
    have hσ_opt : ∀ l', LawlerPrec.MinMax.IsFeasible G M l' →
        SingleMachinePrec.Biclique.weightedCompletion p w M σ ≤
          SingleMachinePrec.Biclique.weightedCompletion p w M l' := hσ.2
    let G_M : ι → ι → Prop := fun x y => x ∈ M ∧ y ∈ M ∧ G x y
    have hGM_M : ∀ i j, G_M i j → i ∈ M ∧ j ∈ M := fun _ _ h => ⟨h.1, h.2.1⟩
    have hGM_acyc : ∀ j, ¬ Relation.TransGen G_M j j := fun j htr =>
      hacyc j (transGen_mono (fun _ _ h => h.2.2) htr)
    have hσ_feas_GM : LawlerPrec.MinMax.IsFeasible G_M M σ :=
      ⟨hσ_feas.1, pairwise_imp_of_mem hσ_pair (fun _ _ _ _ h hGM => h hGM.2.2)⟩
    have hM_transGen : ∀ x y, x ∈ M → y ∈ M → Relation.TransGen G x y → Relation.TransGen G_M x y := by
      intro x y hxM hyM htr
      induction htr with
      | @single z hxz => exact .single ⟨hxM, hyM, hxz⟩
      | @tail b c hab hbc ih_tr =>
        have hbN : b ∈ N := (hGN b c hbc).1
        have hbM : b ∈ M := by
          by_contra hb_notM
          rcases hM.2.2 b hbN hb_notM with h1 | h2 | h3
          · exact hacyc x (Relation.TransGen.trans hab (h1 x hxM))
          · exact hacyc c (Relation.TransGen.trans (h2 c hyM) (.single hbc))
          · exact (h3 x hxM).2 hab
        exact .tail (ih_tr hbM) ⟨hbM, hyM, hbc⟩
    have hpref_σ_init : ∀ pref : List ι, pref <+: σ → IsInitialSet G M pref.toFinset := by
      intro pref ⟨suff, hσ_pref⟩
      refine ⟨fun x hx => (hσ_mem x).mp (hσ_pref ▸ List.mem_append_left _ (List.mem_toFinset.mp hx)),
        fun j hj i hiM hij => ?_⟩
      rw [List.mem_toFinset] at hj ⊢
      have hjM : j ∈ M := (hσ_mem j).mp (hσ_pref ▸ List.mem_append_left _ hj)
      have hij_GM := hM_transGen i j hiM hjM hij
      have hlt := idxOf_lt_of_transGen_N M G_M hGM_M hGM_acyc hσ_feas_GM hiM hjM hij_GM
      have hiσ : i ∈ pref ++ suff := hσ_pref ▸ (hσ_mem i).mpr hiM
      rcases List.mem_append.mp hiσ with hipref | hisuff
      · exact hipref
      · have hi_not_pref : i ∉ pref := fun hip =>
          (List.nodup_append.mp (hσ_pref ▸ hσ_nd)).2.2 i hip i hisuff rfl
        rw [← hσ_pref, idxOf_append_of_notMem hi_not_pref, idxOf_append_of_mem hj] at hlt
        have := List.idxOf_lt_length_of_mem hj
        omega
    rcases hI_star_ne with ⟨x₀, hx₀I⟩
    have hx₀σ : x₀ ∈ σ := (hσ_mem x₀).mpr (hI_star_M hx₀I)
    rcases split_last_mem (fun x => decide (x ∈ I_star)) σ ⟨x₀, hx₀σ, decide_eq_true hx₀I⟩ with
      ⟨mid_init, i_last, s_rest, hσ_split, hi_last_dec, hs_rest_dec⟩
    have hi_lastI : i_last ∈ I_star := of_decide_eq_true hi_last_dec
    have hs_rest_notI : ∀ x ∈ s_rest, x ∉ I_star := fun x hx hxI => by
      have := hs_rest_dec x hx
      simp [hxI] at this
    set q_last := mid_init ++ [i_last]
    have hσ_eq : σ = q_last ++ s_rest := by
      simp [q_last, hσ_split, List.append_assoc]
    have hq_last_nd : q_last.Nodup := (List.nodup_append.mp (hσ_eq ▸ hσ_nd)).1
    have hq_last_pair : q_last.Pairwise (fun a b => ¬ G b a) :=
      (List.pairwise_append.mp (hσ_eq ▸ hσ_pair)).1
    have hq_last_subM : ∀ x ∈ q_last, x ∈ M := fun x hx =>
      (hσ_mem x).mp (hσ_eq ▸ List.mem_append_left _ hx)
    have hI_star_in_q : ∀ x ∈ I_star, x ∈ q_last := by
      intro x hxI
      have hxσ : x ∈ q_last ++ s_rest := hσ_eq ▸ (hσ_mem x).mpr (hI_star_M hxI)
      rcases List.mem_append.mp hxσ with hxq | hxs
      · exact hxq
      · exact absurd hxI (hs_rest_notI x hxs)
    set I₁ := q_last.toFinset
    have hI₁_init : IsInitialSet G M I₁ := hpref_σ_init q_last ⟨s_rest, hσ_eq.symm⟩
    have hI₁_ne : I₁.Nonempty := ⟨i_last, List.mem_toFinset.mpr (by simp [q_last])⟩
    have hI₁_max : IsRhoMaximal G p w M I₁ := by
      refine ⟨hI₁_init, hI₁_ne, fun I' hI'_init hI'_ne => ?_⟩
      refine le_trans (hI_star_max I' hI'_init hI'_ne) ?_
      rw [← crho_eq_rho_toFinset p w hq_last_nd]
      by_contra h_lt
      push Not at h_lt
      set b_star := q_last.filter (fun x => decide (x ∈ I_star))
      set d_star := q_last.filter (fun x => !decide (x ∈ I_star))
      have hb_star_mem : ∀ j, j ∈ b_star ↔ j ∈ I_star := by
        intro j
        simp only [b_star, List.mem_filter, decide_eq_true_eq]
        exact ⟨And.right, fun hjI => ⟨hI_star_in_q j hjI, hjI⟩⟩
      have hb_star_toFinset : b_star.toFinset = I_star := by
        ext j
        simp [hb_star_mem]
      have hb_star_nd : b_star.Nodup := hq_last_nd.filter _
      have hb_star_ne : b_star ≠ [] := List.ne_nil_of_mem ((hb_star_mem i_last).mpr hi_lastI)
      have hb_star_crho : crho p w b_star = rho p w I_star := by
        rw [crho_eq_rho_toFinset p w hb_star_nd, hb_star_toFinset]
      have hb_star_comp : IsComposite p w b_star := by
        refine ⟨hb_star_ne, hb_star_nd, fun q hq hq_ne _ => ?_⟩
        rcases prefix_of_filter (fun x => decide (x ∈ I_star)) q_last q hq with ⟨pref, hpref, hfilt⟩
        have hq_nd : q.Nodup := hq.sublist.nodup hb_star_nd
        have hpref_σ : pref <+: σ := hpref.trans ⟨s_rest, hσ_eq.symm⟩
        have hq_toFinset : q.toFinset = pref.toFinset ∩ I_star := by
          ext j
          simp only [← hfilt, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_inter]
        have hq_init : IsInitialSet G M q.toFinset := by
          rw [hq_toFinset]
          have h1 := hpref_σ_init pref hpref_σ
          refine ⟨Finset.inter_subset_right.trans hI_star_M, fun j hj i hiM hij => ?_⟩
          rw [Finset.mem_inter] at hj ⊢
          exact ⟨h1.2 j hj.1 i hiM hij, hI_star_init.2 j hj.2 i hiM hij⟩
        have hq_fin_ne : q.toFinset.Nonempty := by
          rcases List.exists_mem_of_ne_nil q hq_ne with ⟨x, hx⟩
          exact ⟨x, List.mem_toFinset.mpr hx⟩
        rw [crho_eq_rho_toFinset p w hq_nd, hb_star_crho]
        exact hI_star_max q.toFinset hq_init hq_fin_ne
      have hd_star_pref : ∀ q : List ι, q <+: d_star → q ≠ [] → crho p w q ≤ crho p w b_star := by
        intro q hq hq_ne
        rcases prefix_of_filter (fun x => !decide (x ∈ I_star)) q_last q hq with ⟨pref, hpref, hfilt⟩
        have hq_nd : q.Nodup := hq.sublist.nodup (hq_last_nd.filter _)
        have hpref_σ : pref <+: σ := hpref.trans ⟨s_rest, hσ_eq.symm⟩
        have hq_sub : ∀ x ∈ q.toFinset, x ∈ M ∧ x ∉ I_star := by
          intro x hx
          rw [List.mem_toFinset, ← hfilt, List.mem_filter] at hx
          exact ⟨hq_last_subM x (hpref.subset hx.1), by simpa using hx.2⟩
        have hdisj_Iq : Disjoint I_star q.toFinset := by
          rw [Finset.disjoint_left]
          intro x hxI hxq
          exact (hq_sub x hxq).2 hxI
        have hIq_eq : I_star ∪ q.toFinset = I_star ∪ pref.toFinset := by
          ext x
          simp only [Finset.mem_union, List.mem_toFinset, ← hfilt, List.mem_filter]
          by_cases hxI : x ∈ I_star <;> simp [hxI]
        have hIq_init : IsInitialSet G M (I_star ∪ q.toFinset) := by
          rw [hIq_eq]
          have h1 := hpref_σ_init pref hpref_σ
          refine ⟨Finset.union_subset hI_star_M h1.1, fun j hj i hiM hij => ?_⟩
          rcases Finset.mem_union.mp hj with hjI | hjP
          · exact Finset.mem_union_left _ (hI_star_init.2 j hjI i hiM hij)
          · exact Finset.mem_union_right _ (h1.2 j hjP i hiM hij)
        have hIq_ne : (I_star ∪ q.toFinset).Nonempty := ⟨x₀, Finset.mem_union_left _ hx₀I⟩
        have hle := hI_star_max (I_star ∪ q.toFinset) hIq_init hIq_ne
        have hpI : 0 < ∑ j ∈ I_star, p j := by
          rw [← hb_star_toFinset, sum_toFinset_eq_map_sum p hb_star_nd]
          exact map_p_sum_pos p hb_star_ne (fun j hj => hp j (hMN (hI_star_M ((hb_star_mem j).mp hj))))
        have hpq : 0 < (q.map p).sum :=
          map_p_sum_pos p hq_ne (fun j hj => hp j (hMN (hq_sub j (List.mem_toFinset.mpr hj)).1))
        have hpIq : 0 < (∑ j ∈ I_star, p j) + (q.map p).sum := by linarith
        unfold rho at hle
        rw [Finset.sum_union hdisj_Iq, Finset.sum_union hdisj_Iq,
            sum_toFinset_eq_map_sum w hq_nd, sum_toFinset_eq_map_sum p hq_nd] at hle
        rw [div_le_iff₀ hpIq] at hle
        have hmul : (∑ j ∈ I_star, w j) / (∑ j ∈ I_star, p j) * (∑ j ∈ I_star, p j) = ∑ j ∈ I_star, w j :=
          div_mul_cancel₀ _ (ne_of_gt hpI)
        have hle2 : (q.map w).sum ≤ (∑ j ∈ I_star, w j) / (∑ j ∈ I_star, p j) * (q.map p).sum := by linarith
        rw [hb_star_crho]
        unfold crho rho
        rwa [div_le_iff₀ hpq]
      have hbd_perm : (b_star ++ d_star).Perm q_last :=
        List.filter_append_perm (fun x => decide (x ∈ I_star)) q_last
      have hdb_perm : (d_star ++ b_star).Perm q_last :=
        List.perm_append_comm.trans hbd_perm
      have hp_I₁ : ∀ j ∈ I₁, 0 < p j := fun j hj =>
        hp j (hMN (hq_last_subM j (List.mem_toFinset.mp hj)))
      have hd_star_ne : d_star ≠ [] := by
        intro hd_nil
        have hperm_b : b_star.Perm q_last := by simpa [hd_nil] using hbd_perm
        have hcrho_eq : crho p w q_last = crho p w b_star := by
          unfold crho
          rw [(hperm_b.map w).sum_eq, (hperm_b.map p).sum_eq]
        linarith [hb_star_crho]
      have hcrho_d_lt : crho p w d_star < crho p w b_star := by
        have hpb : 0 < (b_star.map p).sum :=
          map_p_sum_pos p hb_star_ne (fun j hj => hp j (hMN (hI_star_M ((hb_star_mem j).mp hj))))
        have hpd : 0 < (d_star.map p).sum :=
          map_p_sum_pos p hd_star_ne (fun j hj =>
            hp j (hMN (hq_last_subM j (List.mem_of_mem_filter hj))))
        have hpq : 0 < (q_last.map p).sum := by
          have := (hdb_perm.map p).sum_eq
          simp only [List.map_append, List.sum_append] at this
          linarith
        have hlt1 : (q_last.map w).sum / (q_last.map p).sum < (b_star.map w).sum / (b_star.map p).sum := by
          rwa [← hb_star_crho] at h_lt
        rw [div_lt_div_iff₀ hpq hpb] at hlt1
        have hw_sum : (q_last.map w).sum = (d_star.map w).sum + (b_star.map w).sum := by
          have := (hdb_perm.map w).sum_eq
          simpa [List.map_append, List.sum_append] using this.symm
        have hp_sum : (q_last.map p).sum = (d_star.map p).sum + (b_star.map p).sum := by
          have := (hdb_perm.map p).sum_eq
          simpa [List.map_append, List.sum_append] using this.symm
        rw [hw_sum, hp_sum] at hlt1
        unfold crho
        rw [div_lt_div_iff₀ hpd hpb]
        linarith
      set P₀ := q_last.map (fun x => (decide (x ∈ I_star), [x]))
      have hP₀_flat : (P₀.map Prod.snd).flatten = q_last := by
        simp [P₀, Function.comp_def, map_singleton_flatten]
      have hP₀_B : ((P₀.filter Prod.fst).map Prod.snd).flatten = b_star :=
        filter_fst_map_singleton (fun x => decide (x ∈ I_star)) q_last
      have hP₀_R : (P₀.filter (fun x => !x.1)).map Prod.snd = d_star.map (fun x => [x]) :=
        filter_not_fst_map_singleton (fun x => decide (x ∈ I_star)) q_last
      have hP₀_ne : ∀ x ∈ P₀, x.2 ≠ [] := by
        intro x hx
        rcases List.mem_map.mp hx with ⟨a, _, rfl⟩
        exact List.cons_ne_nil _ _
      have hP₀_last : ∃ init b_last, P₀ = init ++ [(true, b_last)] :=
        ⟨mid_init.map (fun x => (decide (x ∈ I_star), [x])), [i_last],
          by simp [P₀, q_last, hi_lastI]⟩
      rcases merge_one_composite_right p w I₁ hp_I₁ P₀.length P₀ rfl
        (hP₀_flat ▸ hq_last_nd) (fun j => by rw [hP₀_flat, List.mem_toFinset])
        hP₀_ne hP₀_last (hP₀_B ▸ hb_star_comp) with
        ⟨R₁, R₂, hR_eq, hR_perm, hR_res⟩
      rw [hP₀_R] at hR_eq
      rw [hP₀_B, hP₀_flat] at hR_perm hR_res
      set r₁ := R₁.flatten
      set r₂ := R₂.flatten
      have hR_flat_eq : (R₁ ++ [b_star] ++ R₂).flatten = r₁ ++ b_star ++ r₂ := by
        simp [r₁, r₂, List.append_assoc]
      rw [hR_flat_eq] at hR_perm hR_res
      have hr₁₂_eq : r₁ ++ r₂ = d_star := by
        have := congrArg List.flatten hR_eq
        simpa [r₁, r₂, map_singleton_flatten] using this
      have hbd_eq : b_star ++ d_star = [] ++ b_star ++ r₁ ++ r₂ := by
        simp [← hr₁₂_eq, List.append_assoc]
      have hwc_bd_lt : SingleMachinePrec.Biclique.weightedCompletion p w I₁ (b_star ++ d_star) <
          SingleMachinePrec.Biclique.weightedCompletion p w I₁ q_last := by
        have hstep_le : SingleMachinePrec.Biclique.weightedCompletion p w I₁ (b_star ++ d_star) ≤
            SingleMachinePrec.Biclique.weightedCompletion p w I₁ (r₁ ++ b_star ++ r₂) := by
          by_cases hr₁_nil : r₁ = []
          · rw [hbd_eq, hr₁_nil]; simp
          · rw [hbd_eq]
            have hr₁_pref : r₁ <+: d_star := ⟨r₂, hr₁₂_eq⟩
            have hpr₁ : ∀ j ∈ r₁, 0 < p j := fun j hj =>
              hp_I₁ j (List.mem_toFinset.mpr (hR_perm.subset (by simp [hj])))
            have hpb_star : ∀ j ∈ b_star, 0 < p j := fun j hj =>
              hp_I₁ j (List.mem_toFinset.mpr (hR_perm.subset (by simp [hj])))
            exact weightedCompletion_swap_le p w I₁ [] r₁ b_star r₂
              (by simpa using hR_perm.nodup_iff.mpr hq_last_nd)
              (fun j => by rw [List.nil_append]; exact hR_perm.mem_iff.trans List.mem_toFinset.symm)
              hr₁_nil hb_star_ne hpr₁ hpb_star (hd_star_pref r₁ hr₁_pref hr₁_nil)
        rcases hR_res with hlt | ⟨hR₂_nil, hle⟩
        · exact lt_of_le_of_lt hstep_le hlt
        · have hr₂_nil : r₂ = [] := by simp [r₂, hR₂_nil]
          have hr₁_eq : r₁ = d_star := by simpa [hr₂_nil] using hr₁₂_eq
          have hlt_swap : SingleMachinePrec.Biclique.weightedCompletion p w I₁ ([] ++ b_star ++ d_star ++ []) <
              SingleMachinePrec.Biclique.weightedCompletion p w I₁ ([] ++ d_star ++ b_star ++ []) := by
            have hpd : ∀ j ∈ d_star, 0 < p j := fun j hj =>
              hp_I₁ j (List.mem_toFinset.mpr (List.mem_of_mem_filter hj))
            have hpb : ∀ j ∈ b_star, 0 < p j := fun j hj =>
              hp_I₁ j (List.mem_toFinset.mpr (List.mem_of_mem_filter hj))
            exact weightedCompletion_swap_lt p w I₁ [] d_star b_star []
              (by simpa using hdb_perm.nodup_iff.mpr hq_last_nd)
              (fun j => by rw [List.nil_append, List.append_nil]; exact hdb_perm.mem_iff.trans List.mem_toFinset.symm)
              hd_star_ne hb_star_ne hpd hpb hcrho_d_lt
          simp only [List.nil_append, List.append_nil] at hlt_swap
          rw [hr₁_eq, hr₂_nil, List.append_nil] at hle
          exact lt_of_lt_of_le hlt_swap hle
      have hbd_pair : (b_star ++ d_star).Pairwise (fun a b => ¬ G b a) := by
        rw [List.pairwise_append]
        refine ⟨hq_last_pair.filter _, hq_last_pair.filter _, fun x hx y hy hGyx => ?_⟩
        have hxI : x ∈ I_star := (hb_star_mem x).mp hx
        have hyM : y ∈ M := hq_last_subM y (List.mem_of_mem_filter hy)
        have hy_notI : y ∉ I_star := by
          have := (List.mem_filter.mp hy).2
          simpa using this
        exact hy_notI (hI_star_init.2 x hxI y hyM (.single hGyx))
      have hσ'_feas : LawlerPrec.MinMax.IsFeasible G M ([] ++ (b_star ++ d_star) ++ s_rest) := by
        have hperm_σ' : ([] ++ (b_star ++ d_star) ++ s_rest).Perm ([] ++ q_last ++ s_rest) :=
          (hbd_perm.append_left []).append_right s_rest
        have hσ_eq0 : σ = [] ++ q_last ++ s_rest := by simpa using hσ_eq
        refine ⟨⟨hperm_σ'.nodup_iff.mpr (hσ_eq0 ▸ hσ_nd),
          fun j => hperm_σ'.mem_iff.trans (hσ_eq0 ▸ hσ_mem j)⟩, ?_⟩
        exact pairwise_middle_perm (fun a b => ¬ G b a) [] (b_star ++ d_star) q_last s_rest
          (hσ_eq0 ▸ hσ_pair) hbd_perm hbd_pair
      have hσ'_lt : SingleMachinePrec.Biclique.weightedCompletion p w M ([] ++ (b_star ++ d_star) ++ s_rest) <
          SingleMachinePrec.Biclique.weightedCompletion p w M σ := by
        have hσ_eq0 : σ = [] ++ q_last ++ s_rest := by simpa using hσ_eq
        rw [hσ_eq0]
        exact weightedCompletion_middle_lt p w M [] (b_star ++ d_star) q_last s_rest
          (hσ_eq0 ▸ hσ_nd) (fun j => by rw [← hσ_eq0]; exact hσ_mem j) hbd_perm hwc_bd_lt
      have hσ'_ge := hσ_opt ([] ++ (b_star ++ d_star) ++ s_rest) hσ'_feas
      linarith
    rcases theorem_2 N G hGN hacyc p w hp M hM I₁ hI₁_max with
      ⟨τ₁, hτ₁_opt, a, b, c, hτ₁_eq, hb_mem, hc_mem⟩
    have hτ₁_nd : τ₁.Nodup := hτ₁_opt.1.1.1
    have hτ₁_mem : ∀ j, j ∈ τ₁ ↔ j ∈ N := hτ₁_opt.1.1.2
    have hτ₁_pair : τ₁.Pairwise (fun x y => ¬ G y x) := hτ₁_opt.1.2
    have hb_nd : b.Nodup := by
      have h1 : (a ++ b).Nodup := (List.nodup_append.mp (hτ₁_eq ▸ hτ₁_nd)).1
      exact (List.nodup_append.mp h1).2.1
    have hb_pair : b.Pairwise (fun x y => ¬ G y x) := by
      have h1 : (a ++ b).Pairwise (fun x y => ¬ G y x) :=
        (List.pairwise_append.mp (hτ₁_eq ▸ hτ₁_pair)).1
      exact (List.pairwise_append.mp h1).2.1
    have hq_perm_b : q_last.Perm b := by
      refine (List.perm_ext_iff_of_nodup hq_last_nd hb_nd).mpr (fun j => ?_)
      rw [hb_mem, ← List.mem_toFinset]
    have hwc_q_le_b : SingleMachinePrec.Biclique.weightedCompletion p w b.toFinset q_last ≤
        SingleMachinePrec.Biclique.weightedCompletion p w b.toFinset b := by
      have hbs_feas : LawlerPrec.MinMax.IsFeasible G M ([] ++ b ++ s_rest) := by
        have hperm_bs : ([] ++ b ++ s_rest).Perm ([] ++ q_last ++ s_rest) :=
          (hq_perm_b.symm.append_left []).append_right s_rest
        have hσ_eq0 : σ = [] ++ q_last ++ s_rest := by simpa using hσ_eq
        refine ⟨⟨hperm_bs.nodup_iff.mpr (hσ_eq0 ▸ hσ_nd),
          fun j => hperm_bs.mem_iff.trans (hσ_eq0 ▸ hσ_mem j)⟩, ?_⟩
        exact pairwise_middle_perm (fun x y => ¬ G y x) [] b q_last s_rest
          (hσ_eq0 ▸ hσ_pair) hq_perm_b.symm hb_pair
      have hle_σ := hσ_opt ([] ++ b ++ s_rest) hbs_feas
      have hσ_eq0 : σ = [] ++ q_last ++ s_rest := by simpa using hσ_eq
      rw [hσ_eq0] at hle_σ
      have hdiff := weightedCompletion_middle_diff p w M [] b q_last s_rest
        (hσ_eq0 ▸ hσ_nd) (fun j => by rw [← hσ_eq0]; exact hσ_mem j) hq_perm_b.symm
      have hb_toFinset : b.toFinset = q_last.toFinset := by
        ext j
        simp [I₁, hb_mem]
      rw [hb_toFinset]
      linarith
    set τ₂ := a ++ q_last ++ c
    have hτ₂_perm : τ₂.Perm τ₁ := by
      rw [hτ₁_eq]
      exact (hq_perm_b.append_left a).append_right c
    have hτ₂_feas : LawlerPrec.MinMax.IsFeasible G N τ₂ := by
      refine ⟨⟨hτ₂_perm.nodup_iff.mpr hτ₁_nd, fun j => hτ₂_perm.mem_iff.trans (hτ₁_mem j)⟩, ?_⟩
      exact pairwise_middle_perm (fun x y => ¬ G y x) a q_last b c (hτ₁_eq ▸ hτ₁_pair) hq_perm_b hq_last_pair
    have hτ₂_wc : SingleMachinePrec.Biclique.weightedCompletion p w N τ₂ ≤
        SingleMachinePrec.Biclique.weightedCompletion p w N τ₁ := by
      rw [hτ₁_eq]
      exact weightedCompletion_middle_le p w N a q_last b c
        (hτ₁_eq ▸ hτ₁_nd) (fun j => by rw [← hτ₁_eq]; exact hτ₁_mem j) hq_perm_b hwc_q_le_b
    have hτ₂_opt : SingleMachinePrec.Biclique.IsOptimalSchedule G p w N τ₂ :=
      ⟨hτ₂_feas, fun l' hl' => le_trans hτ₂_wc (hτ₁_opt.2 l' hl')⟩
    have ha_notM : ∀ x ∈ a, x ∉ M := by
      intro x hxa hxM
      by_cases hxI₁ : x ∈ I₁
      · have hxb : x ∈ b := (hb_mem x).mpr hxI₁
        have h1 : (a ++ b).Nodup := (List.nodup_append.mp (hτ₁_eq ▸ hτ₁_nd)).1
        exact (List.nodup_append.mp h1).2.2 x hxa x hxb rfl
      · have hxc : x ∈ c := hc_mem x hxM hxI₁
        have hxab : x ∈ a ++ b := List.mem_append_left _ hxa
        exact (List.nodup_append.mp (hτ₁_eq ▸ hτ₁_nd)).2.2 x hxab x hxc rfl
    have ha_filtM : a.filter (· ∈ M) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      simp [ha_notM x hx]
    have hq_filtM : q_last.filter (· ∈ M) = q_last := by
      rw [List.filter_eq_self]
      intro x hx
      simp [hq_last_subM x hx]
    set M' := M \ I₁
    have hs_rest_mem : ∀ x, x ∈ s_rest ↔ x ∈ M' := by
      intro x
      rw [Finset.mem_sdiff, ← hσ_mem x, hσ_eq, List.mem_append, List.mem_toFinset]
      refine ⟨fun hxs => ⟨Or.inr hxs, fun hxq => ?_⟩, fun ⟨hx, hx_notq⟩ => hx.resolve_left hx_notq⟩
      exact (List.nodup_append.mp (hσ_eq ▸ hσ_nd)).2.2 x hxq x hxs rfl
    by_cases hs_rest_nil : s_rest = []
    · have hc_filtM : c.filter (· ∈ M) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hxc
        simp only [decide_eq_true_eq]
        intro hxM
        by_cases hxI₁ : x ∈ I₁
        · have hxb : x ∈ b := (hb_mem x).mpr hxI₁
          exact (List.nodup_append.mp (hτ₁_eq ▸ hτ₁_nd)).2.2 x (List.mem_append_right _ hxb) x hxc rfl
        · have hxM' : x ∈ M' := Finset.mem_sdiff.mpr ⟨hxM, hxI₁⟩
          have hxs : x ∈ s_rest := (hs_rest_mem x).mpr hxM'
          rw [hs_rest_nil] at hxs
          cases hxs
      refine ⟨τ₂, hτ₂_opt, ?_⟩
      simp [τ₂, List.filter_append, ha_filtM, hq_filtM, hc_filtM, hσ_eq, hs_rest_nil]
    · set C_set := c.toFinset
      let G_C : ι → ι → Prop := fun x y => x ∈ C_set ∧ y ∈ C_set ∧ G x y
      have hGC_C : ∀ i j, G_C i j → i ∈ C_set ∧ j ∈ C_set := fun _ _ h => ⟨h.1, h.2.1⟩
      have hGC_acyc : ∀ j, ¬ Relation.TransGen G_C j j := fun j htr =>
        hacyc j (transGen_mono (fun _ _ h => h.2.2) htr)
      have hc_subN : ∀ x ∈ C_set, x ∈ N := fun x hx =>
        (hτ₁_mem x).mp (hτ₁_eq ▸ List.mem_append_right _ (List.mem_toFinset.mp hx))
      have hp_C : ∀ j ∈ C_set, 0 < p j := fun j hj => hp j (hc_subN j hj)
      have hC_up : ∀ x y, x ∈ C_set → G x y → y ∈ C_set := by
        intro x y hxC hxy
        have hyN : y ∈ N := (hGN x y hxy).2
        have hyτ₁ : y ∈ (a ++ b) ++ c := hτ₁_eq ▸ (hτ₁_mem y).mpr hyN
        rcases List.mem_append.mp hyτ₁ with hyab | hyc
        · exfalso
          have hpair_abc : ((a ++ b) ++ c).Pairwise (fun u v => ¬ G v u) := hτ₁_eq ▸ hτ₁_pair
          exact (List.pairwise_append.mp hpair_abc).2.2 y hyab x (List.mem_toFinset.mp hxC) hxy
        · exact List.mem_toFinset.mpr hyc
      have hM'_subC : M' ⊆ C_set := by
        intro x hxM'
        rcases Finset.mem_sdiff.mp hxM' with ⟨hxM, hx_notI₁⟩
        exact List.mem_toFinset.mpr (hc_mem x hxM hx_notI₁)
      have hM'_ne : M'.Nonempty := by
        rcases List.exists_mem_of_ne_nil s_rest hs_rest_nil with ⟨x, hx⟩
        exact ⟨x, (hs_rest_mem x).mp hx⟩
      have hc_notI₁ : ∀ x ∈ C_set, x ∉ I₁ := by
        intro x hxC hxI₁
        have hxb : x ∈ b := (hb_mem x).mpr hxI₁
        exact (List.nodup_append.mp (hτ₁_eq ▸ hτ₁_nd)).2.2 x (List.mem_append_right _ hxb)
          x (List.mem_toFinset.mp hxC) rfl
      have hM'_mod : IsModule G_C C_set M' := by
        refine ⟨hM'_ne, hM'_subC, fun u huC hu_notM' => ?_⟩
        have huN : u ∈ N := hc_subN u huC
        have hu_notM : u ∉ M := fun huM =>
          hu_notM' (Finset.mem_sdiff.mpr ⟨huM, hc_notI₁ u huC⟩)
        rcases hM.2.2 u huN hu_notM with h1 | h2 | h3
        · left
          intro m hmM'
          exact (transGen_restrict_upward G C_set hC_up huC (h1 m (Finset.sdiff_subset hmM'))).2
        · right; left
          intro m hmM'
          exact (transGen_restrict_upward G C_set hC_up (hM'_subC hmM') (h2 m (Finset.sdiff_subset hmM'))).2
        · right; right
          intro m hmM'
          have hmM : m ∈ M := Finset.sdiff_subset hmM'
          exact ⟨fun htr => (h3 m hmM).1 (transGen_mono (fun _ _ h => h.2.2) htr),
                 fun htr => (h3 m hmM).2 (transGen_mono (fun _ _ h => h.2.2) htr)⟩
      have hs_rest_nd : s_rest.Nodup := (List.nodup_append.mp (hσ_eq ▸ hσ_nd)).2.1
      have hs_rest_pair : s_rest.Pairwise (fun x y => ¬ G y x) :=
        (List.pairwise_append.mp (hσ_eq ▸ hσ_pair)).2.1
      have hs_rest_feas : LawlerPrec.MinMax.IsFeasible G_C M' s_rest := by
        refine ⟨⟨hs_rest_nd, hs_rest_mem⟩, ?_⟩
        exact pairwise_imp_of_mem hs_rest_pair (fun _ _ _ _ h hGC => h hGC.2.2)
      have hs_rest_opt : SingleMachinePrec.Biclique.IsOptimalSchedule G_C p w M' s_rest := by
        refine ⟨hs_rest_feas, fun s' hs' => ?_⟩
        have hs'_pairG : s'.Pairwise (fun x y => ¬ G y x) := by
          refine pairwise_imp_of_mem hs'.2 (fun x hx y hy h hGyx => h ?_)
          exact ⟨hM'_subC ((hs'.1.2 y).mp hy), hM'_subC ((hs'.1.2 x).mp hx), hGyx⟩
        have hqs'_pair : (q_last ++ s').Pairwise (fun x y => ¬ G y x) := by
          rw [List.pairwise_append]
          refine ⟨hq_last_pair, hs'_pairG, fun x hx y hy hGyx => ?_⟩
          have hxI₁ : x ∈ I₁ := List.mem_toFinset.mpr hx
          have hyM' : y ∈ M' := (hs'.1.2 y).mp hy
          have hyM : y ∈ M := Finset.sdiff_subset hyM'
          exact (Finset.mem_sdiff.mp hyM').2 (hI₁_init.2 x hxI₁ y hyM (.single hGyx))
        have hperm_s' : s'.Perm s_rest := by
          refine (List.perm_ext_iff_of_nodup hs'.1.1 hs_rest_nd).mpr (fun j => ?_)
          rw [hs'.1.2, hs_rest_mem]
        have hperm_qs' : (q_last ++ s').Perm σ := by
          rw [hσ_eq]
          exact hperm_s'.append_left q_last
        have hqs'_feas : LawlerPrec.MinMax.IsFeasible G M (q_last ++ s') :=
          ⟨⟨hperm_qs'.nodup_iff.mpr hσ_nd, fun j => hperm_qs'.mem_iff.trans (hσ_mem j)⟩, hqs'_pair⟩
        have hle := hσ_opt (q_last ++ s') hqs'_feas
        have hσ_eq0 : σ = (q_last ++ s_rest) ++ [] := by simp [hσ_eq]
        have hqs'_eq0 : q_last ++ s' = (q_last ++ s') ++ [] := by simp
        have hdiff := weightedCompletion_middle_diff p w M q_last s' s_rest []
          (by simpa [List.append_assoc] using hσ_eq ▸ hσ_nd)
          (fun j => by simpa [List.append_assoc, ← hσ_eq] using hσ_mem j)
          hperm_s'
        have hs_rest_toFinset : s_rest.toFinset = M' := by
          ext j
          simp [hs_rest_mem]
        rw [List.append_nil, List.append_nil, ← hσ_eq, hs_rest_toFinset] at hdiff
        linarith
      have hcard_lt : M'.card < n := by
        rw [← hcard]
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩)
        intro heq
        have hi_in_M : i_last ∈ M := hI_star_M hi_lastI
        rw [← heq] at hi_in_M
        exact (Finset.mem_sdiff.mp hi_in_M).2 (List.mem_toFinset.mpr (by simp [q_last]))
      rcases ih M'.card hcard_lt C_set G_C hGC_C hGC_acyc p w hp_C M' rfl hM'_mod s_rest hs_rest_opt with
        ⟨c', hc'_opt, hc'_filt⟩
      have hc_nd : c.Nodup := (List.nodup_append.mp (hτ₁_eq ▸ hτ₁_nd)).2.1
      have hc_pair : c.Pairwise (fun x y => ¬ G y x) :=
        (List.pairwise_append.mp (hτ₁_eq ▸ hτ₁_pair)).2.1
      have hc_feas_GC : LawlerPrec.MinMax.IsFeasible G_C C_set c :=
        ⟨⟨hc_nd, fun j => List.mem_toFinset.symm⟩,
         pairwise_imp_of_mem hc_pair (fun _ _ _ _ h hGC => h hGC.2.2)⟩
      have hwc_c'_le_c : SingleMachinePrec.Biclique.weightedCompletion p w C_set c' ≤
          SingleMachinePrec.Biclique.weightedCompletion p w C_set c :=
        hc'_opt.2 c hc_feas_GC
      have hc'_perm_c : c'.Perm c := by
        refine (List.perm_ext_iff_of_nodup hc'_opt.1.1.1 hc_nd).mpr (fun j => ?_)
        rw [hc'_opt.1.1.2, ← List.mem_toFinset]
      have hc'_pairG : c'.Pairwise (fun x y => ¬ G y x) := by
        refine pairwise_imp_of_mem hc'_opt.1.2 (fun x hx y hy h hGyx => h ?_)
        exact ⟨(hc'_opt.1.1.2 y).mp hy, (hc'_opt.1.1.2 x).mp hx, hGyx⟩
      set τ := (a ++ q_last) ++ c'
      have hτ_eq0 : τ = (a ++ q_last) ++ c' ++ [] := by simp [τ]
      have hτ₂_eq0 : τ₂ = (a ++ q_last) ++ c ++ [] := by simp [τ₂]
      have hτ_perm : τ.Perm τ₂ := hc'_perm_c.append_left (a ++ q_last)
      have hτ_feas : LawlerPrec.MinMax.IsFeasible G N τ := by
        refine ⟨⟨hτ_perm.nodup_iff.mpr hτ₂_feas.1.1,
          fun j => hτ_perm.mem_iff.trans (hτ₂_feas.1.2 j)⟩, ?_⟩
        rw [hτ_eq0]
        exact pairwise_middle_perm (fun x y => ¬ G y x) (a ++ q_last) c' c []
          (hτ₂_eq0 ▸ hτ₂_feas.2) hc'_perm_c hc'_pairG
      have hτ_wc : SingleMachinePrec.Biclique.weightedCompletion p w N τ ≤
          SingleMachinePrec.Biclique.weightedCompletion p w N τ₂ := by
        rw [hτ_eq0, hτ₂_eq0]
        exact weightedCompletion_middle_le p w N (a ++ q_last) c' c []
          (hτ₂_eq0 ▸ hτ₂_feas.1.1) (fun j => by rw [← hτ₂_eq0]; exact hτ₂_feas.1.2 j)
          hc'_perm_c hwc_c'_le_c
      have hτ_opt : SingleMachinePrec.Biclique.IsOptimalSchedule G p w N τ :=
        ⟨hτ_feas, fun l' hl' => le_trans hτ_wc (hτ₂_opt.2 l' hl')⟩
      have hc'_filtM : c'.filter (· ∈ M) = s_rest := by
        rw [← hc'_filt]
        refine List.filter_congr (fun x hx => ?_)
        have hxC : x ∈ C_set := (hc'_opt.1.1.2 x).mp hx
        have hx_notI₁ : x ∉ I₁ := hc_notI₁ x hxC
        simp [M', hx_notI₁]
      refine ⟨τ, hτ_opt, ?_⟩
      simp [τ, List.filter_append, ha_filtM, hq_filtM, hc'_filtM, hσ_eq]

theorem solution {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (M : Finset ι) (hM : IsModule G N M)
    (σ : List ι) (hσ : SingleMachinePrec.Biclique.IsOptimalSchedule G p w M σ) :
    ∃ τ : List ι, SingleMachinePrec.Biclique.IsOptimalSchedule G p w N τ ∧
      τ.filter (· ∈ M) = σ :=
  theorem_1_aux M.card N G hGN hacyc p w hp M rfl hM σ hσ
