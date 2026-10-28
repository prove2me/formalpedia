-- Prove2me | solution 1 for LawlerWCT.SeriesPar.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T10:47:11.077567+00:00
-- url     : https://prove2.me/submissions/d078bed4-40bd-40c9-b06d-8f1be89f8a28

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

open LawlerWCT.SeriesPar

private lemma module_convex {ι : Type*} (N : Finset ι) (G : ι → ι → Prop)
    (hacyc : ∀ j, ¬ Relation.TransGen G j j) {M : Finset ι} (hM : IsModule G N M)
    {a b c : ι} (ha : a ∈ M) (hb : b ∈ N) (hc : c ∈ M)
    (hab : Relation.TransGen G a b) (hbc : Relation.TransGen G b c) :
    b ∈ M := by
  by_contra hbM
  rcases hM.2.2 b hb hbM with h1 | h2 | h3
  · exact hacyc a (Relation.TransGen.trans hab (h1 a ha))
  · exact hacyc c (Relation.TransGen.trans (h2 c hc) hbc)
  · exact (h3 a ha).2 hab

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

private lemma weightedCompletion_swap_le {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (J : Finset ι) (X A B Y : List ι)
    (hnd : (X ++ A ++ B ++ Y).Nodup)
    (hmem : ∀ j, j ∈ X ++ A ++ B ++ Y ↔ j ∈ J)
    (hA_ne : A ≠ []) (hB_ne : B ≠ [])
    (hpA : ∀ j ∈ A, 0 < p j) (hpB : ∀ j ∈ B, 0 < p j)
    (hrho : crho p w A ≤ crho p w B) :
    SingleMachinePrec.Biclique.weightedCompletion p w J (X ++ B ++ A ++ Y) ≤
      SingleMachinePrec.Biclique.weightedCompletion p w J (X ++ A ++ B ++ Y) := by
  have hnd_XAB : (X ++ A ++ B).Nodup := (List.nodup_append.mp hnd).1
  have hnd_XA : (X ++ A).Nodup := (List.nodup_append.mp hnd_XAB).1
  have hnd_A : A.Nodup := (List.nodup_append.mp hnd_XA).2.1
  have hnd_B : B.Nodup := (List.nodup_append.mp hnd_XAB).2.1
  have hdisj_XA : Disjoint X.toFinset A.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxX hxA
    exact (List.nodup_append.mp hnd_XA).2.2 x (List.mem_toFinset.mp hxX) x (List.mem_toFinset.mp hxA) rfl
  have hdisj_XAB : Disjoint (X.toFinset ∪ A.toFinset) B.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxXA hxB
    have hx_mem : x ∈ X ++ A := by
      rcases Finset.mem_union.mp hxXA with hxX | hxA
      · exact List.mem_append_left _ (List.mem_toFinset.mp hxX)
      · exact List.mem_append_right _ (List.mem_toFinset.mp hxA)
    exact (List.nodup_append.mp hnd_XAB).2.2 x hx_mem x (List.mem_toFinset.mp hxB) rfl
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
  have hJ_eq : J = X.toFinset ∪ A.toFinset ∪ B.toFinset ∪ Y.toFinset := by
    ext j
    simp only [← hmem, List.mem_append, Finset.mem_union, List.mem_toFinset]
  have hdisj_XB : Disjoint X.toFinset B.toFinset :=
    Disjoint.mono_left Finset.subset_union_left hdisj_XAB
  have hdisj_AB : Disjoint A.toFinset B.toFinset :=
    Disjoint.mono_left Finset.subset_union_right hdisj_XAB
  have hdisj_XBA : Disjoint (X.toFinset ∪ B.toFinset) A.toFinset := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdisj_XA, hdisj_AB.symm⟩
  have hJ_eq' : X.toFinset ∪ A.toFinset ∪ B.toFinset = X.toFinset ∪ B.toFinset ∪ A.toFinset := by
    rw [Finset.union_assoc, Finset.union_assoc, Finset.union_comm A.toFinset B.toFinset]
  have hdisj_XBA_Y : Disjoint (X.toFinset ∪ B.toFinset ∪ A.toFinset) Y.toFinset :=
    hJ_eq' ▸ hdisj_XAB_Y
  have h1 := weightedCompletion_append p w hdisj_XAB_Y (l₁ := X ++ A ++ B) (l₂ := Y)
    (fun j => by simp [List.mem_append, Finset.mem_union])
  have h2 := weightedCompletion_append p w hdisj_XAB (l₁ := X ++ A) (l₂ := B)
    (fun j => by simp [List.mem_append, Finset.mem_union])
  have h3 := weightedCompletion_append p w hdisj_XA (l₁ := X) (l₂ := A)
    (fun j => by simp)
  have h4 := weightedCompletion_append p w hdisj_XBA_Y (l₁ := X ++ B ++ A) (l₂ := Y)
    (fun j => by simp [List.mem_append, Finset.mem_union])
  have h5 := weightedCompletion_append p w hdisj_XBA (l₁ := X ++ B) (l₂ := A)
    (fun j => by simp [List.mem_append, Finset.mem_union])
  have h6 := weightedCompletion_append p w hdisj_XB (l₁ := X) (l₂ := B)
    (fun j => by simp)
  have hsum_XAB_XBA : ((X ++ A ++ B).map p).sum = ((X ++ B ++ A).map p).sum := by
    simp only [List.map_append, List.sum_append]
    linarith
  have hXA_sum : ((X ++ A).map p).sum = (X.map p).sum + (A.map p).sum := by
    simp [List.map_append, List.sum_append]
  have hXB_sum : ((X ++ B).map p).sum = (X.map p).sum + (B.map p).sum := by
    simp [List.map_append, List.sum_append]
  have hWA : ∑ j ∈ A.toFinset, w j = (A.map w).sum := sum_toFinset_eq_map_sum w hnd_A
  have hWB : ∑ j ∈ B.toFinset, w j = (B.map w).sum := sum_toFinset_eq_map_sum w hnd_B
  have hB_split : ∑ j ∈ B.toFinset, w j * ((X.map p).sum + (A.map p).sum) =
      (∑ j ∈ B.toFinset, w j * (X.map p).sum) + (B.map w).sum * (A.map p).sum := by
    rw [← hWB, finset_sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => mul_add (w j) _ _)
  have hA_split : ∑ j ∈ A.toFinset, w j * ((X.map p).sum + (B.map p).sum) =
      (∑ j ∈ A.toFinset, w j * (X.map p).sum) + (A.map w).sum * (B.map p).sum := by
    rw [← hWA, finset_sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => mul_add (w j) _ _)
  have hPA : 0 < (A.map p).sum := map_p_sum_pos p hA_ne hpA
  have hPB : 0 < (B.map p).sum := map_p_sum_pos p hB_ne hpB
  unfold crho at hrho
  have hcross : (A.map w).sum * (B.map p).sum ≤ (B.map w).sum * (A.map p).sum := by
    rwa [div_le_div_iff₀ hPA hPB] at hrho
  rw [hJ_eq, h1, h2, h3, hXA_sum, hB_split]
  rw [hJ_eq', h4, h5, h6, hXB_sum, hA_split, ← hsum_XAB_XBA]
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

private lemma exists_source_aux {ι : Type*} [DecidableEq ι] (G : ι → ι → Prop)
    (hacyc : ∀ j, ¬ Relation.TransGen G j j) (S : Finset ι) :
    ∀ (k : ℕ) (x : ι), x ∈ S →
      (@Finset.filter ι (fun y => Relation.TransGen G y x) (Classical.decPred _) S).card = k →
      ∃ m ∈ S, ∀ z ∈ S, ¬ G z m := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro x hx hcard
    by_cases hmin : ∀ z ∈ S, ¬ G z x
    · exact ⟨x, hx, hmin⟩
    · push Not at hmin
      rcases hmin with ⟨y, hyS, hyx⟩
      let dec : DecidablePred (fun z => Relation.TransGen G z x) := Classical.decPred _
      let decy : DecidablePred (fun z => Relation.TransGen G z y) := Classical.decPred _
      have hssub : @Finset.filter ι (fun z => Relation.TransGen G z y) decy S ⊂
          @Finset.filter ι (fun z => Relation.TransGen G z x) dec S := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun z hz => ?_, fun heq => ?_⟩
        · rw [@Finset.mem_filter _ _ decy] at hz
          rw [@Finset.mem_filter _ _ dec]
          exact ⟨hz.1, Relation.TransGen.tail hz.2 hyx⟩
        · have hy_in_x : y ∈ @Finset.filter ι (fun z => Relation.TransGen G z x) dec S := by
            rw [@Finset.mem_filter _ _ dec]
            exact ⟨hyS, .single hyx⟩
          rw [← heq, @Finset.mem_filter _ _ decy] at hy_in_x
          exact hacyc y hy_in_x.2
      have hlt : (@Finset.filter ι (fun z => Relation.TransGen G z y) decy S).card < k := by
        rw [← hcard]
        exact Finset.card_lt_card hssub
      exact ih _ hlt y hyS rfl

private lemma exists_feasible_aux {ι : Type*} [DecidableEq ι] (G : ι → ι → Prop)
    (hacyc : ∀ j, ¬ Relation.TransGen G j j) :
    ∀ (n : ℕ) (S : Finset ι), S.card = n →
      ∃ l : List ι, LawlerPrec.MinMax.IsFeasible G S l
  | 0, S, hcard => by
    rw [Finset.card_eq_zero.mp hcard]
    exact ⟨[], ⟨⟨List.nodup_nil, fun x => by simp⟩, List.Pairwise.nil⟩⟩
  | n + 1, S, hcard => by
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    rcases hne with ⟨x₀, hx₀⟩
    rcases exists_source_aux G hacyc S _ x₀ hx₀ rfl with ⟨m, hmS, hmin⟩
    have hcard' : (S.erase m).card = n := by
      rw [Finset.card_erase_of_mem hmS, hcard]
      rfl
    rcases exists_feasible_aux G hacyc n (S.erase m) hcard' with ⟨l, hl⟩
    refine ⟨m :: l, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · rw [List.nodup_cons]
      exact ⟨fun hm => (Finset.notMem_erase m S) ((hl.1.2 m).mp hm), hl.1.1⟩
    · intro x
      rw [List.mem_cons, hl.1.2, Finset.mem_erase]
      exact ⟨fun h => h.elim (fun hxm => hxm ▸ hmS) And.right,
             fun hxS => by by_cases hxm : x = m <;> [exact Or.inl hxm; exact Or.inr ⟨hxm, hxS⟩]⟩
    · rw [List.pairwise_cons]
      refine ⟨fun y hy => hmin y (Finset.mem_of_mem_erase ((hl.1.2 y).mp hy)), hl.2⟩

private noncomputable def listsOfFinset {ι : Type*} [DecidableEq ι] (S : Finset ι) : ℕ → List (List ι)
  | 0 => [[]]
  | n + 1 => S.toList.flatMap (fun x => (listsOfFinset (S.erase x) n).map (fun l => x :: l))

private lemma mem_listsOfFinset {ι : Type*} [DecidableEq ι] :
    ∀ (l : List ι) (S : Finset ι), l.Nodup → (∀ x, x ∈ l ↔ x ∈ S) →
      l ∈ listsOfFinset S S.card
  | [], S, _, hmem => by
    have hS : S = ∅ := Finset.ext (fun x => by simpa using (hmem x).symm)
    subst hS
    simp [listsOfFinset]
  | a :: as, S, hnd, hmem => by
    rw [List.nodup_cons] at hnd
    have haS : a ∈ S := (hmem a).mp List.mem_cons_self
    have hcard : S.card = (S.erase a).card + 1 := (Finset.card_erase_add_one haS).symm
    have has_mem : ∀ x, x ∈ as ↔ x ∈ S.erase a := by
      intro x
      rw [Finset.mem_erase, ← hmem x, List.mem_cons]
      exact ⟨fun h => ⟨fun hxa => hnd.1 (hxa ▸ h), Or.inr h⟩,
             fun ⟨hne, h⟩ => h.resolve_left hne⟩
    have ih := mem_listsOfFinset as (S.erase a) hnd.2 has_mem
    rw [hcard, listsOfFinset, List.mem_flatMap]
    exact ⟨a, Finset.mem_toList.mpr haS, List.mem_map.mpr ⟨as, ih, rfl⟩⟩

private lemma exists_min_in_list {α : Type*} (f : α → ℝ) (P : α → Prop) :
    ∀ (L : List α) (x₀ : α), x₀ ∈ L → P x₀ →
      ∃ x ∈ L, P x ∧ ∀ y ∈ L, P y → f x ≤ f y
  | [], _, hx₀, _ => by cases hx₀
  | a :: as, x₀, hx₀, hPx₀ => by
    by_cases h : ∃ z ∈ as, P z
    · rcases h with ⟨z, hzas, hPz⟩
      rcases exists_min_in_list f P as z hzas hPz with ⟨m, hmas, hPm, hmin⟩
      by_cases hPa : P a
      · by_cases hle : f a ≤ f m
        · refine ⟨a, List.mem_cons_self, hPa, fun y hy hPy => ?_⟩
          rcases List.mem_cons.mp hy with rfl | hyas
          · exact le_rfl
          · exact le_trans hle (hmin y hyas hPy)
        · refine ⟨m, List.mem_cons_of_mem a hmas, hPm, fun y hy hPy => ?_⟩
          rcases List.mem_cons.mp hy with rfl | hyas
          · linarith
          · exact hmin y hyas hPy
      · refine ⟨m, List.mem_cons_of_mem a hmas, hPm, fun y hy hPy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hyas
        · exact absurd hPy hPa
        · exact hmin y hyas hPy
    · push Not at h
      rcases List.mem_cons.mp hx₀ with rfl | hx₀as
      · refine ⟨x₀, List.mem_cons_self, hPx₀, fun y hy hPy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hyas
        · exact le_rfl
        · exact absurd hPy (h y hyas)
      · exact absurd hPx₀ (h x₀ hx₀as)

private lemma exists_optimalSchedule {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hacyc : ∀ j, ¬ Relation.TransGen G j j) (p w : ι → ℝ) :
    ∃ τ : List ι, SingleMachinePrec.Biclique.IsOptimalSchedule G p w N τ := by
  rcases exists_feasible_aux G hacyc N.card N rfl with ⟨l₀, hl₀⟩
  have hl₀_mem : l₀ ∈ listsOfFinset N N.card := mem_listsOfFinset l₀ N hl₀.1.1 hl₀.1.2
  rcases exists_min_in_list (SingleMachinePrec.Biclique.weightedCompletion p w N)
    (LawlerPrec.MinMax.IsFeasible G N) (listsOfFinset N N.card) l₀ hl₀_mem hl₀ with
    ⟨τ, _, hτ_feas, hτ_min⟩
  exact ⟨τ, hτ_feas, fun l' hl' => hτ_min l' (mem_listsOfFinset l' N hl'.1.1 hl'.1.2) hl'⟩

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

private lemma filter_not_fst_of_map_snd_eq_nil {α : Type*} {L : List (Bool × α)}
    (h : (L.filter Prod.fst).map Prod.snd = []) :
    L.filter (fun x => !x.1) = L := by
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  exact List.filter_eq_self.mpr (fun x hx => by simp [h x hx])

private lemma filter_fst_empty_of_map_snd_eq_nil {α : Type*} {L : List (Bool × α)}
    (h : (L.filter Prod.fst).map Prod.snd = []) :
    L.filter Prod.fst = [] :=
  List.map_eq_nil_iff.mp h

private lemma flatten_append_two {α : Type*} (B₁ : List (List α)) (b₁ b₂ : List α) (B₂ : List (List α)) :
    (B₁ ++ [b₁ ++ b₂] ++ B₂).flatten = (B₁ ++ [b₁, b₂] ++ B₂).flatten := by
  simp [List.append_assoc]

private lemma perm_middle_swap {α : Type*} (X A B Y : List α) :
    (X ++ B ++ A ++ Y).Perm (X ++ A ++ B ++ Y) := by
  rw [List.append_assoc X B A, List.append_assoc X A B]
  exact List.Perm.append_right Y (List.Perm.append_left X List.perm_append_comm)

private lemma filter_swap_eq {α : Type*} (p : α → Bool) (X A B Y : List α)
    (h : A.filter p = [] ∨ B.filter p = []) :
    (X ++ B ++ A ++ Y).filter p = (X ++ A ++ B ++ Y).filter p := by
  rcases h with hA | hB
  · simp [List.filter_append, hA]
  · simp [List.filter_append, hB]

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
      have hP_flat : (((X ++ [(true, b₁)] ++ (U ++ [(true, b₂)] ++ Y)).map Prod.snd).flatten) =
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
        have hP'_len : P'.length < n := by
          subst hlen
          simp [P']
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
        have hP'_len : P'.length < n := by
          subst hlen
          simp [P']
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

private lemma exists_last_elem {α : Type*} :
    ∀ (l : List α), l ≠ [] → ∃ init last, l = init ++ [last]
  | [], h => absurd rfl h
  | [a], _ => ⟨[], a, rfl⟩
  | a :: b :: bs, _ => by
    rcases exists_last_elem (b :: bs) (List.cons_ne_nil _ _) with ⟨init, last, heq⟩
    exact ⟨a :: init, last, by simp [heq]⟩

private lemma d_blocks_dichotomy {ι : Type*} (p w : ι → ℝ) (b : List ι)
    (B : List (List ι)) (hB_ne : B ≠ []) (hd_ne : ∀ d ∈ B, d ≠ [])
    (hpref : ∀ q : List ι, q <+: B.flatten → q ≠ [] → crho p w q ≤ crho p w b) :
    (∃ B₁ d₁ d₂ B₂, B = B₁ ++ [d₁, d₂] ++ B₂ ∧ crho p w d₁ ≤ crho p w d₂) ∨
      (∃ B_init d_k, B = B_init ++ [d_k] ∧ crho p w d_k ≤ crho p w b) := by
  by_cases h1 : ∃ B₁ d₁ d₂ B₂, B = B₁ ++ [d₁, d₂] ++ B₂ ∧ crho p w d₁ ≤ crho p w d₂
  · exact Or.inl h1
  · right
    push Not at h1
    rcases B with _ | ⟨d₀, ds⟩
    · exact absurd rfl hB_ne
    · have hd₀_le : crho p w d₀ ≤ crho p w b :=
        hpref d₀ ⟨ds.flatten, rfl⟩ (hd_ne d₀ List.mem_cons_self)
      rcases ds with _ | ⟨d₁, ds'⟩
      · exact ⟨[], d₀, rfl, hd₀_le⟩
      · have hall := forall_lt_of_no_consecutive_le p w d₀ (d₁ :: ds') h1
        rcases exists_last_elem (d₁ :: ds') (List.cons_ne_nil _ _) with ⟨init, d_k, heq⟩
        have hd_k_mem : d_k ∈ d₁ :: ds' := by rw [heq]; simp
        have hd_k_lt : crho p w d_k < crho p w d₀ := hall d_k hd_k_mem
        exact ⟨d₀ :: init, d_k, by simp [heq], le_trans (le_of_lt hd_k_lt) hd₀_le⟩

private lemma push_D_right {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (J D U : Finset ι) (hp : ∀ j ∈ J, 0 < p j)
    (b : List ι) (hb_ne : b ≠ [])
    (hbD : b.filter (fun x => decide (x ∈ D)) = [])
    (hbU : b.filter (fun x => decide (x ∈ U)) = []) :
    ∀ (n : ℕ) (P : List (Bool × List ι)) (r₂ : List ι), P.length = n →
      ((P.map Prod.snd).flatten ++ b ++ r₂).Nodup →
      (∀ j, j ∈ (P.map Prod.snd).flatten ++ b ++ r₂ ↔ j ∈ J) →
      (∀ x ∈ P, x.2 ≠ []) →
      (∀ x ∈ P, x.1 = true → ∀ j ∈ x.2, j ∈ D ∧ j ∉ U) →
      (∀ x ∈ P, x.1 = false → ∀ j ∈ x.2, j ∈ U ∧ j ∉ D) →
      (∀ q : List ι, q <+: ((P.filter Prod.fst).map Prod.snd).flatten → q ≠ [] →
        crho p w q ≤ crho p w b) →
      ∃ u₁ r₂' : List ι,
        (∀ j ∈ u₁, j ∈ U) ∧
        (u₁ ++ b ++ r₂').Perm ((P.map Prod.snd).flatten ++ b ++ r₂) ∧
        (u₁ ++ b ++ r₂').filter (fun x => decide (x ∈ D)) =
          ((P.map Prod.snd).flatten ++ b ++ r₂).filter (fun x => decide (x ∈ D)) ∧
        (u₁ ++ b ++ r₂').filter (fun x => decide (x ∈ U)) =
          ((P.map Prod.snd).flatten ++ b ++ r₂).filter (fun x => decide (x ∈ U)) ∧
        SingleMachinePrec.Biclique.weightedCompletion p w J (u₁ ++ b ++ r₂') ≤
          SingleMachinePrec.Biclique.weightedCompletion p w J ((P.map Prod.snd).flatten ++ b ++ r₂) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P r₂ hlen hnd hmem hne htrue hfalse hpref
    set B := (P.filter Prod.fst).map Prod.snd with hB_def
    by_cases hB_ne : B = []
    · have hP_false : ∀ x ∈ P, x.1 = false := by
        intro x hx
        cases hx1 : x.1
        · rfl
        · have hxB : x.2 ∈ B := List.mem_map_of_mem (List.mem_filter.mpr ⟨hx, hx1⟩)
          rw [hB_ne] at hxB
          cases hxB
      refine ⟨(P.map Prod.snd).flatten, r₂, ?_, List.Perm.refl _, rfl, rfl, le_rfl⟩
      intro j hj
      rcases List.mem_flatten.mp hj with ⟨s, hs, hjs⟩
      rcases List.mem_map.mp hs with ⟨x, hx, rfl⟩
      exact (hfalse x hx (hP_false x hx) j hjs).1
    · have hd_ne : ∀ d ∈ B, d ≠ [] := by
        intro d hd
        rcases List.mem_map.mp hd with ⟨x, hx, rfl⟩
        exact hne x (List.mem_of_mem_filter hx)
      rcases d_blocks_dichotomy p w b B hB_ne hd_ne hpref with
        ⟨B₁, d₁, d₂, B₂, hB_eq, hrho12⟩ | ⟨B_init, d_k, hB_eq, hrho_dk⟩
      · have hB_eq1 : (P.filter Prod.fst).map Prod.snd = B₁ ++ d₁ :: (d₂ :: B₂) := by
          simpa [List.append_assoc] using hB_eq
        rcases split_of_filter_fst_cons P B₁ d₁ (d₂ :: B₂) hB_eq1 with ⟨X, Z, rfl, hX, hZ⟩
        have hZ_eq : (Z.filter Prod.fst).map Prod.snd = [] ++ d₂ :: B₂ := by simpa using hZ
        rcases split_of_filter_fst_cons Z [] d₂ B₂ hZ_eq with ⟨U_mid, Y, rfl, hU, hY⟩
        have hU_fst : U_mid.filter Prod.fst = [] := filter_fst_empty_of_map_snd_eq_nil hU
        have hd₁_ne : d₁ ≠ [] := hne (true, d₁) (by simp)
        have hd₂_ne : d₂ ≠ [] := hne (true, d₂) (by simp)
        have hd₁₂_ne : d₁ ++ d₂ ≠ [] := List.append_ne_nil_of_left_ne_nil hd₁_ne d₂
        set x_f := (X.map Prod.snd).flatten
        set u_f := (U_mid.map Prod.snd).flatten
        set y_f := (Y.map Prod.snd).flatten
        have hP_flat : ((X ++ [(true, d₁)] ++ (U_mid ++ [(true, d₂)] ++ Y)).map Prod.snd).flatten =
            x_f ++ d₁ ++ u_f ++ d₂ ++ y_f := by
          simp [x_f, u_f, y_f, List.append_assoc]
        have hpd₁ : ∀ j ∈ d₁, 0 < p j := fun j hj =>
          hp j ((hmem j).mp (by rw [hP_flat]; simp [hj]))
        have hpd₂ : ∀ j ∈ d₂, 0 < p j := fun j hj =>
          hp j ((hmem j).mp (by rw [hP_flat]; simp [hj]))
        have hpu : ∀ j ∈ u_f, 0 < p j := fun j hj =>
          hp j ((hmem j).mp (by rw [hP_flat]; simp [hj]))
        have hu_mem : ∀ j ∈ u_f, j ∈ U ∧ j ∉ D := by
          intro j hj
          rcases List.mem_flatten.mp hj with ⟨s, hs, hjs⟩
          rcases List.mem_map.mp hs with ⟨x, hx, rfl⟩
          have hx_false : x.1 = false := by
            cases hx1 : x.1
            · rfl
            · have : x ∈ U_mid.filter Prod.fst := List.mem_filter.mpr ⟨hx, hx1⟩
              rw [hU_fst] at this
              cases this
          exact hfalse x (by simp [hx]) hx_false j hjs
        have hu_filt_D : u_f.filter (fun x => decide (x ∈ D)) = [] :=
          List.filter_eq_nil_iff.mpr (fun j hj => by simp [(hu_mem j hj).2])
        have hd₁_filt_U : d₁.filter (fun x => decide (x ∈ U)) = [] :=
          List.filter_eq_nil_iff.mpr (fun j hj => by simp [(htrue (true, d₁) (by simp) rfl j hj).2])
        have hd₂_filt_U : d₂.filter (fun x => decide (x ∈ U)) = [] :=
          List.filter_eq_nil_iff.mpr (fun j hj => by simp [(htrue (true, d₂) (by simp) rfl j hj).2])
        by_cases hu_case : u_f = [] ∨ crho p w u_f ≤ crho p w d₂
        · let P' := X ++ [(true, d₁ ++ d₂)] ++ U_mid ++ Y
          have hP'_len : P'.length < n := by subst hlen; simp [P']
          have hP'_all : (P'.map Prod.snd).flatten ++ b ++ r₂ =
              (x_f ++ d₁) ++ d₂ ++ u_f ++ (y_f ++ b ++ r₂) := by
            simp [P', x_f, u_f, y_f, List.append_assoc]
          have hP_all : ((X ++ [(true, d₁)] ++ (U_mid ++ [(true, d₂)] ++ Y)).map Prod.snd).flatten ++ b ++ r₂ =
              (x_f ++ d₁) ++ u_f ++ d₂ ++ (y_f ++ b ++ r₂) := by
            simp [x_f, u_f, y_f, List.append_assoc]
          have hperm_step : ((P'.map Prod.snd).flatten ++ b ++ r₂).Perm
              (((X ++ [(true, d₁)] ++ (U_mid ++ [(true, d₂)] ++ Y)).map Prod.snd).flatten ++ b ++ r₂) := by
            rw [hP'_all, hP_all]
            exact perm_middle_swap (x_f ++ d₁) u_f d₂ (y_f ++ b ++ r₂)
          have hfilt_D_step : ((P'.map Prod.snd).flatten ++ b ++ r₂).filter (fun x => decide (x ∈ D)) =
              (((X ++ [(true, d₁)] ++ (U_mid ++ [(true, d₂)] ++ Y)).map Prod.snd).flatten ++ b ++ r₂).filter
                (fun x => decide (x ∈ D)) := by
            rw [hP'_all, hP_all]
            exact filter_swap_eq _ (x_f ++ d₁) u_f d₂ (y_f ++ b ++ r₂) (Or.inl hu_filt_D)
          have hfilt_U_step : ((P'.map Prod.snd).flatten ++ b ++ r₂).filter (fun x => decide (x ∈ U)) =
              (((X ++ [(true, d₁)] ++ (U_mid ++ [(true, d₂)] ++ Y)).map Prod.snd).flatten ++ b ++ r₂).filter
                (fun x => decide (x ∈ U)) := by
            rw [hP'_all, hP_all]
            exact filter_swap_eq _ (x_f ++ d₁) u_f d₂ (y_f ++ b ++ r₂) (Or.inr hd₂_filt_U)
          have hwc_step : SingleMachinePrec.Biclique.weightedCompletion p w J
              ((P'.map Prod.snd).flatten ++ b ++ r₂) ≤
              SingleMachinePrec.Biclique.weightedCompletion p w J
                (((X ++ [(true, d₁)] ++ (U_mid ++ [(true, d₂)] ++ Y)).map Prod.snd).flatten ++ b ++ r₂) := by
            rcases hu_case with hu_nil | hrho_ud₂
            · rw [hP'_all, hP_all, hu_nil]; simp
            · by_cases hu_nil : u_f = []
              · rw [hP'_all, hP_all, hu_nil]; simp
              · rw [hP'_all, hP_all]
                exact weightedCompletion_swap_le p w J (x_f ++ d₁) u_f d₂ (y_f ++ b ++ r₂)
                  (hP_all ▸ hnd) (fun j => by rw [← hP_all]; exact hmem j)
                  hu_nil hd₂_ne hpu hpd₂ hrho_ud₂
          have hP'_B : ((P'.filter Prod.fst).map Prod.snd).flatten = B.flatten := by
            have : (P'.filter Prod.fst).map Prod.snd = B₁ ++ [d₁ ++ d₂] ++ B₂ := by
              simp [P', List.filter_append, hX, hU_fst, hY, List.append_assoc]
            rw [this, hB_eq, flatten_append_two]
          have hP'_ne : ∀ x ∈ P', x.2 ≠ [] := by
            intro x hx
            simp only [P', List.mem_append, List.mem_singleton] at hx
            rcases hx with ((hx | rfl) | hx) | hx
            · exact hne x (by simp [hx])
            · exact hd₁₂_ne
            · exact hne x (by simp [hx])
            · exact hne x (by simp [hx])
          have hP'_true : ∀ x ∈ P', x.1 = true → ∀ j ∈ x.2, j ∈ D ∧ j ∉ U := by
            intro x hx hx1 j hj
            simp only [P', List.mem_append, List.mem_singleton] at hx
            rcases hx with ((hx | rfl) | hx) | hx
            · exact htrue x (by simp [hx]) hx1 j hj
            · rcases List.mem_append.mp hj with hj1 | hj2
              · exact htrue (true, d₁) (by simp) rfl j hj1
              · exact htrue (true, d₂) (by simp) rfl j hj2
            · exact htrue x (by simp [hx]) hx1 j hj
            · exact htrue x (by simp [hx]) hx1 j hj
          have hP'_false : ∀ x ∈ P', x.1 = false → ∀ j ∈ x.2, j ∈ U ∧ j ∉ D := by
            intro x hx hx1 j hj
            simp only [P', List.mem_append, List.mem_singleton] at hx
            rcases hx with ((hx | rfl) | hx) | hx
            · exact hfalse x (by simp [hx]) hx1 j hj
            · cases hx1
            · exact hfalse x (by simp [hx]) hx1 j hj
            · exact hfalse x (by simp [hx]) hx1 j hj
          rcases ih P'.length hP'_len P' r₂ rfl (hperm_step.nodup_iff.mpr hnd)
            (fun j => hperm_step.mem_iff.trans (hmem j)) hP'_ne hP'_true hP'_false
            (fun q hq => hpref q (hP'_B ▸ hq)) with
            ⟨u₁, r₂', hu₁, hperm', hfiltD', hfiltU', hwc'⟩
          exact ⟨u₁, r₂', hu₁, hperm'.trans hperm_step,
            hfiltD'.trans hfilt_D_step, hfiltU'.trans hfilt_U_step, le_trans hwc' hwc_step⟩
        · push Not at hu_case
          have hu_ne : u_f ≠ [] := hu_case.1
          have hrho_d₁u : crho p w d₁ ≤ crho p w u_f := le_of_lt (lt_of_le_of_lt hrho12 hu_case.2)
          let P' := X ++ U_mid ++ [(true, d₁ ++ d₂)] ++ Y
          have hP'_len : P'.length < n := by subst hlen; simp [P']
          have hP'_all : (P'.map Prod.snd).flatten ++ b ++ r₂ =
              x_f ++ u_f ++ d₁ ++ (d₂ ++ y_f ++ b ++ r₂) := by
            simp [P', x_f, u_f, y_f, List.append_assoc]
          have hP_all : ((X ++ [(true, d₁)] ++ (U_mid ++ [(true, d₂)] ++ Y)).map Prod.snd).flatten ++ b ++ r₂ =
              x_f ++ d₁ ++ u_f ++ (d₂ ++ y_f ++ b ++ r₂) := by
            simp [x_f, u_f, y_f, List.append_assoc]
          have hperm_step : ((P'.map Prod.snd).flatten ++ b ++ r₂).Perm
              (((X ++ [(true, d₁)] ++ (U_mid ++ [(true, d₂)] ++ Y)).map Prod.snd).flatten ++ b ++ r₂) := by
            rw [hP'_all, hP_all]
            exact perm_middle_swap x_f d₁ u_f (d₂ ++ y_f ++ b ++ r₂)
          have hfilt_D_step : ((P'.map Prod.snd).flatten ++ b ++ r₂).filter (fun x => decide (x ∈ D)) =
              (((X ++ [(true, d₁)] ++ (U_mid ++ [(true, d₂)] ++ Y)).map Prod.snd).flatten ++ b ++ r₂).filter
                (fun x => decide (x ∈ D)) := by
            rw [hP'_all, hP_all]
            exact filter_swap_eq _ x_f d₁ u_f (d₂ ++ y_f ++ b ++ r₂) (Or.inr hu_filt_D)
          have hfilt_U_step : ((P'.map Prod.snd).flatten ++ b ++ r₂).filter (fun x => decide (x ∈ U)) =
              (((X ++ [(true, d₁)] ++ (U_mid ++ [(true, d₂)] ++ Y)).map Prod.snd).flatten ++ b ++ r₂).filter
                (fun x => decide (x ∈ U)) := by
            rw [hP'_all, hP_all]
            exact filter_swap_eq _ x_f d₁ u_f (d₂ ++ y_f ++ b ++ r₂) (Or.inl hd₁_filt_U)
          have hwc_step : SingleMachinePrec.Biclique.weightedCompletion p w J
              ((P'.map Prod.snd).flatten ++ b ++ r₂) ≤
              SingleMachinePrec.Biclique.weightedCompletion p w J
                (((X ++ [(true, d₁)] ++ (U_mid ++ [(true, d₂)] ++ Y)).map Prod.snd).flatten ++ b ++ r₂) := by
            rw [hP'_all, hP_all]
            exact weightedCompletion_swap_le p w J x_f d₁ u_f (d₂ ++ y_f ++ b ++ r₂)
              (hP_all ▸ hnd) (fun j => by rw [← hP_all]; exact hmem j)
              hd₁_ne hu_ne hpd₁ hpu hrho_d₁u
          have hP'_B : ((P'.filter Prod.fst).map Prod.snd).flatten = B.flatten := by
            have : (P'.filter Prod.fst).map Prod.snd = B₁ ++ [d₁ ++ d₂] ++ B₂ := by
              simp [P', List.filter_append, hX, hU_fst, hY, List.append_assoc]
            rw [this, hB_eq, flatten_append_two]
          have hP'_ne : ∀ x ∈ P', x.2 ≠ [] := by
            intro x hx
            simp only [P', List.mem_append, List.mem_singleton] at hx
            rcases hx with ((hx | hx) | rfl) | hx
            · exact hne x (by simp [hx])
            · exact hne x (by simp [hx])
            · exact hd₁₂_ne
            · exact hne x (by simp [hx])
          have hP'_true : ∀ x ∈ P', x.1 = true → ∀ j ∈ x.2, j ∈ D ∧ j ∉ U := by
            intro x hx hx1 j hj
            simp only [P', List.mem_append, List.mem_singleton] at hx
            rcases hx with ((hx | hx) | rfl) | hx
            · exact htrue x (by simp [hx]) hx1 j hj
            · exact htrue x (by simp [hx]) hx1 j hj
            · rcases List.mem_append.mp hj with hj1 | hj2
              · exact htrue (true, d₁) (by simp) rfl j hj1
              · exact htrue (true, d₂) (by simp) rfl j hj2
            · exact htrue x (by simp [hx]) hx1 j hj
          have hP'_false : ∀ x ∈ P', x.1 = false → ∀ j ∈ x.2, j ∈ U ∧ j ∉ D := by
            intro x hx hx1 j hj
            simp only [P', List.mem_append, List.mem_singleton] at hx
            rcases hx with ((hx | hx) | rfl) | hx
            · exact hfalse x (by simp [hx]) hx1 j hj
            · exact hfalse x (by simp [hx]) hx1 j hj
            · cases hx1
            · exact hfalse x (by simp [hx]) hx1 j hj
          rcases ih P'.length hP'_len P' r₂ rfl (hperm_step.nodup_iff.mpr hnd)
            (fun j => hperm_step.mem_iff.trans (hmem j)) hP'_ne hP'_true hP'_false
            (fun q hq => hpref q (hP'_B ▸ hq)) with
            ⟨u₁, r₂', hu₁, hperm', hfiltD', hfiltU', hwc'⟩
          exact ⟨u₁, r₂', hu₁, hperm'.trans hperm_step,
            hfiltD'.trans hfilt_D_step, hfiltU'.trans hfilt_U_step, le_trans hwc' hwc_step⟩
      · have hB_eq1 : (P.filter Prod.fst).map Prod.snd = B_init ++ d_k :: [] := by
          simpa [List.append_assoc] using hB_eq
        rcases split_of_filter_fst_cons P B_init d_k [] hB_eq1 with ⟨X, U_tail, rfl, hX, hU⟩
        have hU_fst : U_tail.filter Prod.fst = [] := filter_fst_empty_of_map_snd_eq_nil hU
        have hdk_ne : d_k ≠ [] := hne (true, d_k) (by simp)
        set x_f := (X.map Prod.snd).flatten
        set u_f := (U_tail.map Prod.snd).flatten
        have hP_all : ((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂ =
            x_f ++ d_k ++ u_f ++ b ++ r₂ := by
          simp [x_f, u_f, List.append_assoc]
        have hpdk : ∀ j ∈ d_k, 0 < p j := fun j hj =>
          hp j ((hmem j).mp (by rw [hP_all]; simp [hj]))
        have hpu : ∀ j ∈ u_f, 0 < p j := fun j hj =>
          hp j ((hmem j).mp (by rw [hP_all]; simp [hj]))
        have hpb : ∀ j ∈ b, 0 < p j := fun j hj =>
          hp j ((hmem j).mp (by rw [hP_all]; simp [hj]))
        have hu_mem : ∀ j ∈ u_f, j ∈ U ∧ j ∉ D := by
          intro j hj
          rcases List.mem_flatten.mp hj with ⟨s, hs, hjs⟩
          rcases List.mem_map.mp hs with ⟨x, hx, rfl⟩
          have hx_false : x.1 = false := by
            cases hx1 : x.1
            · rfl
            · have : x ∈ U_tail.filter Prod.fst := List.mem_filter.mpr ⟨hx, hx1⟩
              rw [hU_fst] at this
              cases this
          exact hfalse x (by simp [hx]) hx_false j hjs
        have hu_filt_D : u_f.filter (fun x => decide (x ∈ D)) = [] :=
          List.filter_eq_nil_iff.mpr (fun j hj => by simp [(hu_mem j hj).2])
        have hdk_filt_U : d_k.filter (fun x => decide (x ∈ U)) = [] :=
          List.filter_eq_nil_iff.mpr (fun j hj => by simp [(htrue (true, d_k) (by simp) rfl j hj).2])
        by_cases hu_case : u_f = [] ∨ crho p w u_f ≤ crho p w b
        · let P' := X
          let r₂_next := d_k ++ u_f ++ r₂
          have hP'_len : P'.length < n := by subst hlen; simp [P']
          have hP'_all : (P'.map Prod.snd).flatten ++ b ++ r₂_next =
              x_f ++ b ++ d_k ++ (u_f ++ r₂) := by
            simp [P', r₂_next, x_f, List.append_assoc]
          have hmid_eq1 : (x_f ++ d_k) ++ b ++ u_f ++ r₂ = x_f ++ d_k ++ b ++ (u_f ++ r₂) := by
            simp [List.append_assoc]
          have hP_all1 : ((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂ =
              (x_f ++ d_k) ++ u_f ++ b ++ r₂ := by
            simp [x_f, u_f, List.append_assoc]
          have hperm1 : ((x_f ++ d_k) ++ b ++ u_f ++ r₂).Perm
              (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂) := by
            rw [hP_all1]
            exact perm_middle_swap (x_f ++ d_k) u_f b r₂
          have hfiltD1 : ((x_f ++ d_k) ++ b ++ u_f ++ r₂).filter (fun x => decide (x ∈ D)) =
              (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂).filter
                (fun x => decide (x ∈ D)) := by
            rw [hP_all1]
            exact filter_swap_eq _ (x_f ++ d_k) u_f b r₂ (Or.inl hu_filt_D)
          have hfiltU1 : ((x_f ++ d_k) ++ b ++ u_f ++ r₂).filter (fun x => decide (x ∈ U)) =
              (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂).filter
                (fun x => decide (x ∈ U)) := by
            rw [hP_all1]
            exact filter_swap_eq _ (x_f ++ d_k) u_f b r₂ (Or.inr hbU)
          have hwc1 : SingleMachinePrec.Biclique.weightedCompletion p w J
              ((x_f ++ d_k) ++ b ++ u_f ++ r₂) ≤
              SingleMachinePrec.Biclique.weightedCompletion p w J
                (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂) := by
            rcases hu_case with hu_nil | hrho_ub
            · rw [hP_all1, hu_nil]; simp
            · by_cases hu_nil : u_f = []
              · rw [hP_all1, hu_nil]; simp
              · rw [hP_all1]
                exact weightedCompletion_swap_le p w J (x_f ++ d_k) u_f b r₂
                  (hP_all1 ▸ hnd) (fun j => by rw [← hP_all1]; exact hmem j)
                  hu_nil hb_ne hpu hpb hrho_ub
          have hnd_mid : (x_f ++ d_k ++ b ++ (u_f ++ r₂)).Nodup :=
            hmid_eq1 ▸ hperm1.nodup_iff.mpr hnd
          have hmem_mid : ∀ j, j ∈ x_f ++ d_k ++ b ++ (u_f ++ r₂) ↔ j ∈ J :=
            fun j => (hmid_eq1 ▸ hperm1).mem_iff.trans (hmem j)
          have hperm2 : ((P'.map Prod.snd).flatten ++ b ++ r₂_next).Perm
              (x_f ++ d_k ++ b ++ (u_f ++ r₂)) := by
            rw [hP'_all]
            exact perm_middle_swap x_f d_k b (u_f ++ r₂)
          have hfiltD2 : ((P'.map Prod.snd).flatten ++ b ++ r₂_next).filter (fun x => decide (x ∈ D)) =
              (x_f ++ d_k ++ b ++ (u_f ++ r₂)).filter (fun x => decide (x ∈ D)) := by
            rw [hP'_all]
            exact filter_swap_eq _ x_f d_k b (u_f ++ r₂) (Or.inr hbD)
          have hfiltU2 : ((P'.map Prod.snd).flatten ++ b ++ r₂_next).filter (fun x => decide (x ∈ U)) =
              (x_f ++ d_k ++ b ++ (u_f ++ r₂)).filter (fun x => decide (x ∈ U)) := by
            rw [hP'_all]
            exact filter_swap_eq _ x_f d_k b (u_f ++ r₂) (Or.inl hdk_filt_U)
          have hwc2 : SingleMachinePrec.Biclique.weightedCompletion p w J
              ((P'.map Prod.snd).flatten ++ b ++ r₂_next) ≤
              SingleMachinePrec.Biclique.weightedCompletion p w J
                (x_f ++ d_k ++ b ++ (u_f ++ r₂)) := by
            rw [hP'_all]
            exact weightedCompletion_swap_le p w J x_f d_k b (u_f ++ r₂)
              hnd_mid hmem_mid hdk_ne hb_ne hpdk hpb hrho_dk
          have hperm_step : ((P'.map Prod.snd).flatten ++ b ++ r₂_next).Perm
              (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂) :=
            hperm2.trans (hmid_eq1 ▸ hperm1)
          have hfilt_D_step : ((P'.map Prod.snd).flatten ++ b ++ r₂_next).filter (fun x => decide (x ∈ D)) =
              (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂).filter
                (fun x => decide (x ∈ D)) := by
            rw [hfiltD2, ← hmid_eq1, hfiltD1]
          have hfilt_U_step : ((P'.map Prod.snd).flatten ++ b ++ r₂_next).filter (fun x => decide (x ∈ U)) =
              (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂).filter
                (fun x => decide (x ∈ U)) := by
            rw [hfiltU2, ← hmid_eq1, hfiltU1]
          have hwc_step : SingleMachinePrec.Biclique.weightedCompletion p w J
              ((P'.map Prod.snd).flatten ++ b ++ r₂_next) ≤
              SingleMachinePrec.Biclique.weightedCompletion p w J
                (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂) := by
            rw [← hmid_eq1] at hwc2
            exact le_trans hwc2 hwc1
          have hP'_ne : ∀ x ∈ P', x.2 ≠ [] := fun x hx => hne x (by simp [P', hx])
          have hP'_true : ∀ x ∈ P', x.1 = true → ∀ j ∈ x.2, j ∈ D ∧ j ∉ U :=
            fun x hx => htrue x (by simp [P', hx])
          have hP'_false : ∀ x ∈ P', x.1 = false → ∀ j ∈ x.2, j ∈ U ∧ j ∉ D :=
            fun x hx => hfalse x (by simp [P', hx])
          have hP'_pref : ∀ q : List ι, q <+: ((P'.filter Prod.fst).map Prod.snd).flatten →
              q ≠ [] → crho p w q ≤ crho p w b := by
            intro q hq hq_ne
            refine hpref q (hq.trans ?_) hq_ne
            rw [show (P'.filter Prod.fst).map Prod.snd = B_init from hX, hB_eq]
            exact ⟨d_k, by simp⟩
          rcases ih P'.length hP'_len P' r₂_next rfl (hperm_step.nodup_iff.mpr hnd)
            (fun j => hperm_step.mem_iff.trans (hmem j)) hP'_ne hP'_true hP'_false hP'_pref with
            ⟨u₁, r₂', hu₁, hperm', hfiltD', hfiltU', hwc'⟩
          exact ⟨u₁, r₂', hu₁, hperm'.trans hperm_step,
            hfiltD'.trans hfilt_D_step, hfiltU'.trans hfilt_U_step, le_trans hwc' hwc_step⟩
        · push Not at hu_case
          have hu_ne : u_f ≠ [] := hu_case.1
          have hrho_dku : crho p w d_k ≤ crho p w u_f := le_of_lt (lt_of_le_of_lt hrho_dk hu_case.2)
          let P' := X ++ U_tail
          let r₂_next := d_k ++ r₂
          have hP'_len : P'.length < n := by subst hlen; simp [P']
          have hP'_all : (P'.map Prod.snd).flatten ++ b ++ r₂_next =
              (x_f ++ u_f) ++ b ++ d_k ++ r₂ := by
            simp [P', r₂_next, x_f, u_f, List.append_assoc]
          have hmid_eq1 : x_f ++ u_f ++ d_k ++ (b ++ r₂) = (x_f ++ u_f) ++ d_k ++ b ++ r₂ := by
            simp [List.append_assoc]
          have hP_all1 : ((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂ =
              x_f ++ d_k ++ u_f ++ (b ++ r₂) := by
            simp [x_f, u_f, List.append_assoc]
          have hperm1 : (x_f ++ u_f ++ d_k ++ (b ++ r₂)).Perm
              (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂) := by
            rw [hP_all1]
            exact perm_middle_swap x_f d_k u_f (b ++ r₂)
          have hfiltD1 : (x_f ++ u_f ++ d_k ++ (b ++ r₂)).filter (fun x => decide (x ∈ D)) =
              (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂).filter
                (fun x => decide (x ∈ D)) := by
            rw [hP_all1]
            exact filter_swap_eq _ x_f d_k u_f (b ++ r₂) (Or.inr hu_filt_D)
          have hfiltU1 : (x_f ++ u_f ++ d_k ++ (b ++ r₂)).filter (fun x => decide (x ∈ U)) =
              (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂).filter
                (fun x => decide (x ∈ U)) := by
            rw [hP_all1]
            exact filter_swap_eq _ x_f d_k u_f (b ++ r₂) (Or.inl hdk_filt_U)
          have hwc1 : SingleMachinePrec.Biclique.weightedCompletion p w J
              (x_f ++ u_f ++ d_k ++ (b ++ r₂)) ≤
              SingleMachinePrec.Biclique.weightedCompletion p w J
                (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂) := by
            rw [hP_all1]
            exact weightedCompletion_swap_le p w J x_f d_k u_f (b ++ r₂)
              (hP_all1 ▸ hnd) (fun j => by rw [← hP_all1]; exact hmem j)
              hdk_ne hu_ne hpdk hpu hrho_dku
          have hnd_mid : ((x_f ++ u_f) ++ d_k ++ b ++ r₂).Nodup :=
            hmid_eq1 ▸ hperm1.nodup_iff.mpr hnd
          have hmem_mid : ∀ j, j ∈ (x_f ++ u_f) ++ d_k ++ b ++ r₂ ↔ j ∈ J :=
            fun j => (hmid_eq1 ▸ hperm1).mem_iff.trans (hmem j)
          have hperm2 : ((P'.map Prod.snd).flatten ++ b ++ r₂_next).Perm
              ((x_f ++ u_f) ++ d_k ++ b ++ r₂) := by
            rw [hP'_all]
            exact perm_middle_swap (x_f ++ u_f) d_k b r₂
          have hfiltD2 : ((P'.map Prod.snd).flatten ++ b ++ r₂_next).filter (fun x => decide (x ∈ D)) =
              ((x_f ++ u_f) ++ d_k ++ b ++ r₂).filter (fun x => decide (x ∈ D)) := by
            rw [hP'_all]
            exact filter_swap_eq _ (x_f ++ u_f) d_k b r₂ (Or.inr hbD)
          have hfiltU2 : ((P'.map Prod.snd).flatten ++ b ++ r₂_next).filter (fun x => decide (x ∈ U)) =
              ((x_f ++ u_f) ++ d_k ++ b ++ r₂).filter (fun x => decide (x ∈ U)) := by
            rw [hP'_all]
            exact filter_swap_eq _ (x_f ++ u_f) d_k b r₂ (Or.inl hdk_filt_U)
          have hwc2 : SingleMachinePrec.Biclique.weightedCompletion p w J
              ((P'.map Prod.snd).flatten ++ b ++ r₂_next) ≤
              SingleMachinePrec.Biclique.weightedCompletion p w J
                ((x_f ++ u_f) ++ d_k ++ b ++ r₂) := by
            rw [hP'_all]
            exact weightedCompletion_swap_le p w J (x_f ++ u_f) d_k b r₂
              hnd_mid hmem_mid hdk_ne hb_ne hpdk hpb hrho_dk
          have hperm_step : ((P'.map Prod.snd).flatten ++ b ++ r₂_next).Perm
              (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂) :=
            hperm2.trans (hmid_eq1 ▸ hperm1)
          have hfilt_D_step : ((P'.map Prod.snd).flatten ++ b ++ r₂_next).filter (fun x => decide (x ∈ D)) =
              (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂).filter
                (fun x => decide (x ∈ D)) := by
            rw [hfiltD2, ← hmid_eq1, hfiltD1]
          have hfilt_U_step : ((P'.map Prod.snd).flatten ++ b ++ r₂_next).filter (fun x => decide (x ∈ U)) =
              (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂).filter
                (fun x => decide (x ∈ U)) := by
            rw [hfiltU2, ← hmid_eq1, hfiltU1]
          have hwc_step : SingleMachinePrec.Biclique.weightedCompletion p w J
              ((P'.map Prod.snd).flatten ++ b ++ r₂_next) ≤
              SingleMachinePrec.Biclique.weightedCompletion p w J
                (((X ++ [(true, d_k)] ++ U_tail).map Prod.snd).flatten ++ b ++ r₂) := by
            rw [← hmid_eq1] at hwc2
            exact le_trans hwc2 hwc1
          have hP'_ne : ∀ x ∈ P', x.2 ≠ [] := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hne x (by simp [hx])
            · exact hne x (by simp [hx])
          have hP'_true : ∀ x ∈ P', x.1 = true → ∀ j ∈ x.2, j ∈ D ∧ j ∉ U := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact htrue x (by simp [hx])
            · exact htrue x (by simp [hx])
          have hP'_false : ∀ x ∈ P', x.1 = false → ∀ j ∈ x.2, j ∈ U ∧ j ∉ D := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hfalse x (by simp [hx])
            · exact hfalse x (by simp [hx])
          have hP'_pref : ∀ q : List ι, q <+: ((P'.filter Prod.fst).map Prod.snd).flatten →
              q ≠ [] → crho p w q ≤ crho p w b := by
            intro q hq hq_ne
            refine hpref q (hq.trans ?_) hq_ne
            have hP'_B : (P'.filter Prod.fst).map Prod.snd = B_init := by
              simp [P', List.filter_append, hX, hU_fst]
            rw [hP'_B, hB_eq]
            exact ⟨d_k, by simp⟩
          rcases ih P'.length hP'_len P' r₂_next rfl (hperm_step.nodup_iff.mpr hnd)
            (fun j => hperm_step.mem_iff.trans (hmem j)) hP'_ne hP'_true hP'_false hP'_pref with
            ⟨u₁, r₂', hu₁, hperm', hfiltD', hfiltU', hwc'⟩
          exact ⟨u₁, r₂', hu₁, hperm'.trans hperm_step,
            hfiltD'.trans hfilt_D_step, hfiltU'.trans hfilt_U_step, le_trans hwc' hwc_step⟩

private lemma crho_eq_rho_toFinset {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    {c : List ι} (hnd : c.Nodup) :
    crho p w c = rho p w c.toFinset := by
  unfold crho rho
  rw [sum_toFinset_eq_map_sum w hnd, sum_toFinset_eq_map_sum p hnd]

private lemma split_first_mem {α : Type*} (P : α → Bool) :
    ∀ (l : List α), (∃ x ∈ l, P x = true) →
      ∃ A m B, l = A ++ m :: B ∧ P m = true ∧ ∀ x ∈ A, P x = false
  | [], ⟨_, hx, _⟩ => by cases hx
  | x :: xs, h => by
    by_cases hx : P x = true
    · exact ⟨[], x, xs, rfl, hx, fun _ hmem => by cases hmem⟩
    · have hx_false : P x = false := Bool.eq_false_iff.mpr hx
      have hxs : ∃ y ∈ xs, P y = true := by
        rcases h with ⟨y, hy, hPy⟩
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd hPy hx
        · exact ⟨y, hy', hPy⟩
      rcases split_first_mem P xs hxs with ⟨A, m, B, rfl, hm, hA⟩
      refine ⟨x :: A, m, B, rfl, hm, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hx_false
      · exact hA y hy'

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

theorem solution {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (M : Finset ι) (hM : IsModule G N M)
    (I : Finset ι) (hI : IsRhoMaximal G p w M I) :
    ∃ τ : List ι, SingleMachinePrec.Biclique.IsOptimalSchedule G p w N τ ∧
      ∃ a b c : List ι, τ = a ++ b ++ c ∧ (∀ j, j ∈ b ↔ j ∈ I) ∧
        ∀ m ∈ M, m ∉ I → m ∈ c := by
  rcases exists_optimalSchedule N G hacyc p w with ⟨τ₀, hτ₀_feas, hτ₀_opt⟩
  have hnd₀ : τ₀.Nodup := hτ₀_feas.1.1
  have hmem₀ : ∀ j, j ∈ τ₀ ↔ j ∈ N := hτ₀_feas.1.2
  have hpair₀ : τ₀.Pairwise (fun a b => ¬ G b a) := hτ₀_feas.2
  have hI_init : IsInitialSet G M I := hI.1
  have hI_ne : I.Nonempty := hI.2.1
  have hIM : I ⊆ M := hI_init.1
  have hMN : M ⊆ N := hM.2.1
  have hI_max : ∀ I', IsInitialSet G M I' → I'.Nonempty → rho p w I' ≤ rho p w I := hI.2.2
  rcases hI_ne with ⟨x₀, hx₀I⟩
  have hx₀M : x₀ ∈ M := hIM hx₀I
  have hx₀τ₀ : x₀ ∈ τ₀ := (hmem₀ x₀).mpr (hMN hx₀M)
  rcases split_first_mem (fun x => decide (x ∈ M)) τ₀ ⟨x₀, hx₀τ₀, decide_eq_true hx₀M⟩ with
    ⟨A, m_first, rest₀, hτ₀_split1, hm_first_dec, hA_dec⟩
  have hm_firstM : m_first ∈ M := of_decide_eq_true hm_first_dec
  have hA_notM : ∀ x ∈ A, x ∉ M := fun x hx hxM => by
    have := hA_dec x hx
    simp [hxM] at this
  have hx₀_rest : x₀ ∈ m_first :: rest₀ := by
    have hx₀_app : x₀ ∈ A ++ m_first :: rest₀ := hτ₀_split1 ▸ hx₀τ₀
    rcases List.mem_append.mp hx₀_app with hx₀A | hx₀R
    · exact absurd hx₀M (hA_notM x₀ hx₀A)
    · exact hx₀R
  rcases split_last_mem (fun x => decide (x ∈ I)) (m_first :: rest₀)
    ⟨x₀, hx₀_rest, decide_eq_true hx₀I⟩ with
    ⟨mid_init, i_last, C, hrest_split, hi_last_dec, hC_dec⟩
  have hi_lastI : i_last ∈ I := of_decide_eq_true hi_last_dec
  have hi_lastM : i_last ∈ M := hIM hi_lastI
  have hC_notI : ∀ x ∈ C, x ∉ I := fun x hx hxI => by
    have := hC_dec x hx
    simp [hxI] at this
  set Mid := mid_init ++ [i_last]
  have hrest_eq : m_first :: rest₀ = Mid ++ C := by
    simp [Mid, hrest_split, List.append_assoc]
  have hτ₀_eq : τ₀ = A ++ Mid ++ C := by
    rw [hτ₀_split1, hrest_eq, ← List.append_assoc]
  have hMid_nd : Mid.Nodup := by
    have h1 : (A ++ Mid).Nodup := (List.nodup_append.mp (hτ₀_eq ▸ hnd₀)).1
    exact (List.nodup_append.mp h1).2.1
  have hMid_pair : Mid.Pairwise (fun a b => ¬ G b a) := by
    have h1 : (A ++ Mid).Pairwise (fun a b => ¬ G b a) :=
      (List.pairwise_append.mp (hτ₀_eq ▸ hpair₀)).1
    exact (List.pairwise_append.mp h1).2.1
  have hMid_subN : ∀ x ∈ Mid, x ∈ N := fun x hx =>
    (hmem₀ x).mp (by rw [hτ₀_eq]; simp [hx])
  have hI_in_Mid : ∀ x ∈ I, x ∈ Mid := by
    intro x hxI
    have hxτ₀ : x ∈ A ++ Mid ++ C := hτ₀_eq ▸ (hmem₀ x).mpr (hMN (hIM hxI))
    rcases List.mem_append.mp hxτ₀ with hxAM | hxC
    · rcases List.mem_append.mp hxAM with hxA | hxMid
      · exact absurd (hIM hxI) (hA_notM x hxA)
      · exact hxMid
    · exact absurd hxI (hC_notI x hxC)
  have hU_no_edge : ∀ u ∈ Mid, u ∉ M → ∀ m ∈ M, ¬ G u m ∧ ¬ G m u := by
    intro u huMid hu_notM m hmM
    have huN : u ∈ N := hMid_subN u huMid
    have hu_not_before_mfirst : ¬ Relation.TransGen G u m_first := by
      intro htr
      have hlt := idxOf_lt_of_transGen_N N G hGN hacyc hτ₀_feas huN (hMN hm_firstM) htr
      have hu_notA : u ∉ A := by
        have h1 : (A ++ Mid).Nodup := (List.nodup_append.mp (hτ₀_eq ▸ hnd₀)).1
        exact fun huA => (List.nodup_append.mp h1).2.2 u huA u huMid rfl
      have hm_notA : m_first ∉ A := fun hmA => hA_notM m_first hmA hm_firstM
      rw [hτ₀_split1, idxOf_append_of_notMem hu_notA, idxOf_append_of_notMem hm_notA] at hlt
      simp at hlt
    have hu_not_after_ilast : ¬ Relation.TransGen G i_last u := by
      intro htr
      have hlt := idxOf_lt_of_transGen_N N G hGN hacyc hτ₀_feas (hMN hi_lastM) huN htr
      have hτ₀_eq2 : τ₀ = (A ++ mid_init) ++ (i_last :: C) := by
        simp [hτ₀_eq, Mid, List.append_assoc]
      rcases List.mem_append.mp huMid with hu_init | hu_last
      · have hu_left : u ∈ A ++ mid_init := List.mem_append_right _ hu_init
        have hi_not_left : i_last ∉ A ++ mid_init := by
          have hnd2 : ((A ++ mid_init) ++ (i_last :: C)).Nodup := hτ₀_eq2 ▸ hnd₀
          exact fun hiL => (List.nodup_append.mp hnd2).2.2 i_last hiL i_last List.mem_cons_self rfl
        rw [hτ₀_eq2, idxOf_append_of_notMem hi_not_left, idxOf_append_of_mem hu_left] at hlt
        have := List.idxOf_lt_length_of_mem hu_left
        omega
      · simp only [List.mem_singleton] at hu_last
        subst hu_last
        exact lt_irrefl _ hlt
    rcases hM.2.2 u huN hu_notM with h1 | h2 | h3
    · exact absurd (h1 m_first hm_firstM) hu_not_before_mfirst
    · exact absurd (h2 i_last hi_lastM) hu_not_after_ilast
    · exact ⟨fun h => (h3 m hmM).1 (.single h), fun h => (h3 m hmM).2 (.single h)⟩
  have hpref_init : ∀ pref : List ι, pref <+: Mid → IsInitialSet G M (pref.toFinset ∩ M) := by
    intro pref ⟨suff, hMid_pref⟩
    refine ⟨Finset.inter_subset_right, fun j hjS i hiM hij => ?_⟩
    rw [Finset.mem_inter, List.mem_toFinset] at hjS ⊢
    refine ⟨?_, hiM⟩
    have hτ₀_split_pref : τ₀ = (A ++ pref) ++ (suff ++ C) := by
      simp [hτ₀_eq, ← hMid_pref, List.append_assoc]
    have hiτ₀ : i ∈ (A ++ pref) ++ (suff ++ C) :=
      hτ₀_split_pref ▸ (hmem₀ i).mpr (hMN hiM)
    rcases List.mem_append.mp hiτ₀ with hi_left | hi_right
    · rcases List.mem_append.mp hi_left with hiA | hipref
      · exact absurd hiM (hA_notM i hiA)
      · exact hipref
    · have hlt := idxOf_lt_of_transGen_N N G hGN hacyc hτ₀_feas (hMN hiM) (hMN hjS.2) hij
      have hj_left : j ∈ A ++ pref := List.mem_append_right _ hjS.1
      have hi_not_left : i ∉ A ++ pref := by
        have hnd_sp : ((A ++ pref) ++ (suff ++ C)).Nodup := hτ₀_split_pref ▸ hnd₀
        exact fun hiL => (List.nodup_append.mp hnd_sp).2.2 i hiL i hi_right rfl
      rw [hτ₀_split_pref, idxOf_append_of_notMem hi_not_left, idxOf_append_of_mem hj_left] at hlt
      have := List.idxOf_lt_length_of_mem hj_left
      omega
  set b := Mid.filter (fun x => decide (x ∈ I))
  set D := M \ I
  set U := Mid.toFinset \ M
  have hb_mem : ∀ j, j ∈ b ↔ j ∈ I := by
    intro j
    simp only [b, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun hjI => ⟨hI_in_Mid j hjI, hjI⟩⟩
  have hb_toFinset : b.toFinset = I := by
    ext j
    simp [hb_mem]
  have hb_nd : b.Nodup := hMid_nd.filter _
  have hb_ne : b ≠ [] := List.ne_nil_of_mem ((hb_mem i_last).mpr hi_lastI)
  have hb_crho : crho p w b = rho p w I := by
    rw [crho_eq_rho_toFinset p w hb_nd, hb_toFinset]
  have hb_comp : IsComposite p w b := by
    refine ⟨hb_ne, hb_nd, fun q hq hq_ne _ => ?_⟩
    rcases prefix_of_filter (fun x => decide (x ∈ I)) Mid q hq with ⟨pref, hpref, hfilt⟩
    have hq_nd : q.Nodup := hq.sublist.nodup hb_nd
    have hq_toFinset : q.toFinset = (pref.toFinset ∩ M) ∩ I := by
      ext j
      simp only [← hfilt, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
        Finset.mem_inter]
      exact ⟨fun ⟨hjp, hjI⟩ => ⟨⟨hjp, hIM hjI⟩, hjI⟩, fun ⟨⟨hjp, _⟩, hjI⟩ => ⟨hjp, hjI⟩⟩
    have hq_init : IsInitialSet G M q.toFinset := by
      rw [hq_toFinset]
      have h1 := hpref_init pref hpref
      refine ⟨Finset.inter_subset_right.trans hIM, fun j hj i hiM hij => ?_⟩
      rw [Finset.mem_inter] at hj ⊢
      exact ⟨h1.2 j hj.1 i hiM hij, hI_init.2 j hj.2 i hiM hij⟩
    have hq_fin_ne : q.toFinset.Nonempty := by
      rcases List.exists_mem_of_ne_nil q hq_ne with ⟨x, hx⟩
      exact ⟨x, List.mem_toFinset.mpr hx⟩
    rw [crho_eq_rho_toFinset p w hq_nd, hb_crho]
    exact hI_max q.toFinset hq_init hq_fin_ne
  set d_seq := Mid.filter (fun x => decide (x ∈ D))
  have hd_pref : ∀ q : List ι, q <+: d_seq → q ≠ [] → crho p w q ≤ crho p w b := by
    intro q hq hq_ne
    rcases prefix_of_filter (fun x => decide (x ∈ D)) Mid q hq with ⟨pref, hpref, hfilt⟩
    have hq_nd : q.Nodup := hq.sublist.nodup (hMid_nd.filter _)
    have hq_subD : q.toFinset ⊆ D := by
      intro x hx
      rw [List.mem_toFinset, ← hfilt, List.mem_filter, decide_eq_true_eq] at hx
      exact hx.2
    have hdisj_Iq : Disjoint I q.toFinset := by
      rw [Finset.disjoint_left]
      intro x hxI hxq
      exact (Finset.mem_sdiff.mp (hq_subD hxq)).2 hxI
    have hIq_eq : I ∪ q.toFinset = I ∪ (pref.toFinset ∩ M) := by
      ext x
      simp only [Finset.mem_union, List.mem_toFinset, ← hfilt, List.mem_filter,
        decide_eq_true_eq, Finset.mem_inter, D, Finset.mem_sdiff]
      by_cases hxI : x ∈ I
      · simp [hxI]
      · simp [hxI]
    have hIq_init : IsInitialSet G M (I ∪ q.toFinset) := by
      rw [hIq_eq]
      have h1 := hpref_init pref hpref
      refine ⟨Finset.union_subset hIM h1.1, fun j hj i hiM hij => ?_⟩
      rcases Finset.mem_union.mp hj with hjI | hjP
      · exact Finset.mem_union_left _ (hI_init.2 j hjI i hiM hij)
      · exact Finset.mem_union_right _ (h1.2 j hjP i hiM hij)
    have hIq_ne : (I ∪ q.toFinset).Nonempty := ⟨x₀, Finset.mem_union_left _ hx₀I⟩
    have hle := hI_max (I ∪ q.toFinset) hIq_init hIq_ne
    have hpI : 0 < ∑ j ∈ I, p j := by
      rw [← hb_toFinset, sum_toFinset_eq_map_sum p hb_nd]
      exact map_p_sum_pos p hb_ne (fun j hj => hp j (hMN (hIM ((hb_mem j).mp hj))))
    have hpq : 0 < (q.map p).sum :=
      map_p_sum_pos p hq_ne (fun j hj =>
        hp j (hMN (Finset.sdiff_subset (hq_subD (List.mem_toFinset.mpr hj)))))
    have hpIq : 0 < (∑ j ∈ I, p j) + (q.map p).sum := by linarith
    unfold rho at hle
    rw [Finset.sum_union hdisj_Iq, Finset.sum_union hdisj_Iq,
        sum_toFinset_eq_map_sum w hq_nd, sum_toFinset_eq_map_sum p hq_nd] at hle
    rw [div_le_iff₀ hpIq] at hle
    have hmul : (∑ j ∈ I, w j) / (∑ j ∈ I, p j) * (∑ j ∈ I, p j) = ∑ j ∈ I, w j :=
      div_mul_cancel₀ _ (ne_of_gt hpI)
    have hle2 : (q.map w).sum ≤ (∑ j ∈ I, w j) / (∑ j ∈ I, p j) * (q.map p).sum := by linarith
    rw [hb_crho]
    unfold crho rho
    rwa [div_le_iff₀ hpq]
  set P₀ := Mid.map (fun x => (decide (x ∈ I), [x]))
  have hP₀_flat : (P₀.map Prod.snd).flatten = Mid := by
    simp [P₀, Function.comp_def, map_singleton_flatten]
  have hP₀_B : ((P₀.filter Prod.fst).map Prod.snd).flatten = b :=
    filter_fst_map_singleton (fun x => decide (x ∈ I)) Mid
  have hP₀_R : (P₀.filter (fun x => !x.1)).map Prod.snd =
      (Mid.filter (fun x => !decide (x ∈ I))).map (fun x => [x]) :=
    filter_not_fst_map_singleton (fun x => decide (x ∈ I)) Mid
  have hP₀_ne : ∀ x ∈ P₀, x.2 ≠ [] := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨a, _, rfl⟩
    exact List.cons_ne_nil _ _
  have hp_Mid : ∀ j ∈ Mid.toFinset, 0 < p j := fun j hj =>
    hp j (hMid_subN j (List.mem_toFinset.mp hj))
  rcases merge_one_composite p w Mid.toFinset hp_Mid P₀.length P₀ rfl
    (hP₀_flat ▸ hMid_nd) (fun j => by rw [hP₀_flat, List.mem_toFinset])
    hP₀_ne (hP₀_B ▸ hb_comp) with
    ⟨R₁, R₂, hR_eq, hR_perm, hR_wc⟩
  rw [hP₀_R] at hR_eq
  rw [hP₀_B, hP₀_flat] at hR_perm hR_wc
  set r₁ := R₁.flatten
  set r₂ := R₂.flatten
  have hR_flat_eq : (R₁ ++ [b] ++ R₂).flatten = r₁ ++ b ++ r₂ := by
    simp [r₁, r₂, List.append_assoc]
  rw [hR_flat_eq] at hR_perm hR_wc
  have hr₁₂_eq : r₁ ++ r₂ = Mid.filter (fun x => !decide (x ∈ I)) := by
    have : (R₁ ++ R₂).flatten = ((Mid.filter (fun x => !decide (x ∈ I))).map (fun x => [x])).flatten :=
      congrArg List.flatten hR_eq
    simpa [r₁, r₂, map_singleton_flatten] using this
  have hbD : b.filter (fun x => decide (x ∈ D)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro j hj
    have hjI : j ∈ I := (hb_mem j).mp hj
    simp [D, hjI]
  have hbU : b.filter (fun x => decide (x ∈ U)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro j hj
    have hjM : j ∈ M := hIM ((hb_mem j).mp hj)
    simp [U, hjM]
  set P₁ := r₁.map (fun x => (decide (x ∈ D), [x]))
  have hP₁_flat : (P₁.map Prod.snd).flatten = r₁ := by
    simp [P₁, Function.comp_def, map_singleton_flatten]
  have hP₁_B : ((P₁.filter Prod.fst).map Prod.snd).flatten = r₁.filter (fun x => decide (x ∈ D)) :=
    filter_fst_map_singleton (fun x => decide (x ∈ D)) r₁
  have hP₁_ne : ∀ x ∈ P₁, x.2 ≠ [] := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨a, _, rfl⟩
    exact List.cons_ne_nil _ _
  have hr₁_sub : ∀ j ∈ r₁, j ∈ Mid ∧ j ∉ I := by
    intro j hj
    have hj12 : j ∈ r₁ ++ r₂ := List.mem_append_left _ hj
    rw [hr₁₂_eq, List.mem_filter] at hj12
    exact ⟨hj12.1, by simpa using hj12.2⟩
  have hP₁_true : ∀ x ∈ P₁, x.1 = true → ∀ j ∈ x.2, j ∈ D ∧ j ∉ U := by
    intro x hx hx1 j hj
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    simp only [List.mem_singleton] at hj
    subst hj
    have haD : j ∈ D := of_decide_eq_true hx1
    have haM : j ∈ M := Finset.sdiff_subset haD
    exact ⟨haD, by simp [U, haM]⟩
  have hP₁_false : ∀ x ∈ P₁, x.1 = false → ∀ j ∈ x.2, j ∈ U ∧ j ∉ D := by
    intro x hx hx1 j hj
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    simp only [List.mem_singleton] at hj
    subst hj
    have hj_notD : j ∉ D := by simpa using hx1
    have ⟨hjMid, hj_notI⟩ := hr₁_sub j ha
    have hj_notM : j ∉ M := fun hjM => hj_notD (Finset.mem_sdiff.mpr ⟨hjM, hj_notI⟩)
    exact ⟨Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hjMid, hj_notM⟩, hj_notD⟩
  have hr₁₂_filtD : (r₁ ++ r₂).filter (fun x => decide (x ∈ D)) = d_seq := by
    dsimp only [d_seq]
    rw [hr₁₂_eq, List.filter_filter]
    refine List.filter_congr (fun x _ => ?_)
    by_cases hxD : x ∈ D
    · have hx_notI : x ∉ I := (Finset.mem_sdiff.mp hxD).2
      simp [hxD, hx_notI]
    · simp [hxD]
  have hr₁₂_filtU : (r₁ ++ r₂).filter (fun x => decide (x ∈ U)) =
      Mid.filter (fun x => decide (x ∈ U)) := by
    rw [hr₁₂_eq, List.filter_filter]
    refine List.filter_congr (fun x _ => ?_)
    by_cases hxU : x ∈ U
    · have hx_notM : x ∉ M := (Finset.mem_sdiff.mp hxU).2
      have hx_notI : x ∉ I := fun hxI => hx_notM (hIM hxI)
      simp [hxU, hx_notI]
    · simp [hxU]
  have hP₁_pref : ∀ q : List ι, q <+: ((P₁.filter Prod.fst).map Prod.snd).flatten →
      q ≠ [] → crho p w q ≤ crho p w b := by
    intro q hq hq_ne
    rw [hP₁_B] at hq
    refine hd_pref q (hq.trans ?_) hq_ne
    rw [← hr₁₂_filtD, List.filter_append]
    exact ⟨r₂.filter (fun x => decide (x ∈ D)), rfl⟩
  rcases push_D_right p w Mid.toFinset D U hp_Mid b hb_ne hbD hbU P₁.length P₁ r₂ rfl
    (hP₁_flat ▸ hR_perm.nodup_iff.mpr hMid_nd)
    (fun j => by rw [hP₁_flat]; exact hR_perm.mem_iff.trans List.mem_toFinset.symm)
    hP₁_ne hP₁_true hP₁_false hP₁_pref with
    ⟨u₁, r₂', hu₁, hperm_u, hfiltD_u, hfiltU_u, hwc_u⟩
  rw [hP₁_flat] at hperm_u hfiltD_u hfiltU_u hwc_u
  set Mid' := u₁ ++ b ++ r₂'
  have hMid'_perm : Mid'.Perm Mid := hperm_u.trans hR_perm
  have hMid'_nd : Mid'.Nodup := hMid'_perm.nodup_iff.mpr hMid_nd
  have hMid'_wc : SingleMachinePrec.Biclique.weightedCompletion p w Mid.toFinset Mid' ≤
      SingleMachinePrec.Biclique.weightedCompletion p w Mid.toFinset Mid :=
    le_trans hwc_u hR_wc
  have hMid'_filtI : Mid'.filter (fun x => decide (x ∈ I)) = b := by
    have hu₁I : u₁.filter (fun x => decide (x ∈ I)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro j hj
      have hj_notM : j ∉ M := (Finset.mem_sdiff.mp (hu₁ j hj)).2
      have hj_notI : j ∉ I := fun hjI => hj_notM (hIM hjI)
      simp [hj_notI]
    have hbI : b.filter (fun x => decide (x ∈ I)) = b := by
      rw [List.filter_eq_self]
      intro j hj
      simp [(hb_mem j).mp hj]
    have hr₂'I : r₂'.filter (fun x => decide (x ∈ I)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro j hj
      have hj_not_u₁b : j ∉ u₁ ++ b := fun h =>
        (List.nodup_append.mp hMid'_nd).2.2 j h j hj rfl
      have hj_notb : j ∉ b := fun hb_j => hj_not_u₁b (List.mem_append_right _ hb_j)
      have hj_notI : j ∉ I := fun hjI => hj_notb ((hb_mem j).mpr hjI)
      simp [hj_notI]
    simp [Mid', List.filter_append, hu₁I, hbI, hr₂'I]
  have hMid'_filtD : Mid'.filter (fun x => decide (x ∈ D)) = d_seq := by
    rw [hfiltD_u]
    have : (r₁ ++ b ++ r₂).filter (fun x => decide (x ∈ D)) =
        (r₁ ++ r₂).filter (fun x => decide (x ∈ D)) := by
      simp [List.filter_append, hbD]
    rw [this, hr₁₂_filtD]
  have hMid'_filtU : Mid'.filter (fun x => decide (x ∈ U)) =
      Mid.filter (fun x => decide (x ∈ U)) := by
    rw [hfiltU_u]
    have : (r₁ ++ b ++ r₂).filter (fun x => decide (x ∈ U)) =
        (r₁ ++ r₂).filter (fun x => decide (x ∈ U)) := by
      simp [List.filter_append, hbU]
    rw [this, hr₁₂_filtU]
  have hMid'_no_DI : Mid'.Pairwise (fun x y => ¬ (x ∈ D ∧ y ∈ I)) := by
    rw [show Mid' = (u₁ ++ b) ++ r₂' from rfl, List.pairwise_append]
    have h1 : (u₁ ++ b).Pairwise (fun x y => ¬ (x ∈ D ∧ y ∈ I)) := by
      refine List.pairwise_iff_getElem.mpr (fun i j hi hj _ ⟨hxiD, _⟩ => ?_)
      rcases List.mem_append.mp (List.getElem_mem hi) with hx_u₁ | hx_b
      · exact (Finset.mem_sdiff.mp (hu₁ _ hx_u₁)).2 (Finset.sdiff_subset hxiD)
      · exact (Finset.mem_sdiff.mp hxiD).2 ((hb_mem _).mp hx_b)
    have h2 : r₂'.Pairwise (fun x y => ¬ (x ∈ D ∧ y ∈ I)) := by
      refine List.pairwise_iff_getElem.mpr (fun i j hi hj _ ⟨_, hyjI⟩ => ?_)
      have hy_r₂' : r₂'[j] ∈ r₂' := List.getElem_mem hj
      have hy_b : r₂'[j] ∈ b := (hb_mem _).mpr hyjI
      exact (List.nodup_append.mp hMid'_nd).2.2 _ (List.mem_append_right _ hy_b) _ hy_r₂' rfl
    refine ⟨h1, h2, fun x hx _ _ ⟨hxD, _⟩ => ?_⟩
    rcases List.mem_append.mp hx with hx_u₁ | hx_b
    · exact (Finset.mem_sdiff.mp (hu₁ x hx_u₁)).2 (Finset.sdiff_subset hxD)
    · exact (Finset.mem_sdiff.mp hxD).2 ((hb_mem x).mp hx_b)
  have hMid'_pairI : Mid'.Pairwise (fun x y => decide (x ∈ I) = true → decide (y ∈ I) = true → ¬ G y x) := by
    refine rel_of_pairwise_filter (fun x => decide (x ∈ I)) (fun a b => ¬ G b a) Mid' ?_
    rw [hMid'_filtI]
    exact hMid_pair.filter _
  have hMid'_pairD : Mid'.Pairwise (fun x y => decide (x ∈ D) = true → decide (y ∈ D) = true → ¬ G y x) := by
    refine rel_of_pairwise_filter (fun x => decide (x ∈ D)) (fun a b => ¬ G b a) Mid' ?_
    rw [hMid'_filtD]
    exact hMid_pair.filter _
  have hMid'_pairU : Mid'.Pairwise (fun x y => decide (x ∈ U) = true → decide (y ∈ U) = true → ¬ G y x) := by
    refine rel_of_pairwise_filter (fun x => decide (x ∈ U)) (fun a b => ¬ G b a) Mid' ?_
    rw [hMid'_filtU]
    exact hMid_pair.filter _
  have hMid'_pair_all := pairwise_and hMid'_no_DI
    (pairwise_and hMid'_pairI (pairwise_and hMid'_pairD hMid'_pairU))
  have hMid'_pair : Mid'.Pairwise (fun x y => ¬ G y x) := by
    refine pairwise_imp_of_mem hMid'_pair_all (fun x hx y hy ⟨hnoDI, hpI, hpD, hpU⟩ => ?_)
    have hxMid : x ∈ Mid := hMid'_perm.subset hx
    have hyMid : y ∈ Mid := hMid'_perm.subset hy
    by_cases hxM : x ∈ M
    · by_cases hyM : y ∈ M
      · by_cases hxI : x ∈ I
        · by_cases hyI : y ∈ I
          · exact hpI (decide_eq_true hxI) (decide_eq_true hyI)
          · intro hGyx
            exact hyI (hI_init.2 x hxI y hyM (.single hGyx))
        · have hxD : x ∈ D := Finset.mem_sdiff.mpr ⟨hxM, hxI⟩
          by_cases hyI : y ∈ I
          · exact absurd ⟨hxD, hyI⟩ hnoDI
          · have hyD : y ∈ D := Finset.mem_sdiff.mpr ⟨hyM, hyI⟩
            exact hpD (decide_eq_true hxD) (decide_eq_true hyD)
      · exact (hU_no_edge y hyMid hyM x hxM).1
    · by_cases hyM : y ∈ M
      · exact (hU_no_edge x hxMid hxM y hyM).2
      · have hxU : x ∈ U := Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hxMid, hxM⟩
        have hyU : y ∈ U := Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hyMid, hyM⟩
        exact hpU (decide_eq_true hxU) (decide_eq_true hyU)
  set τ := (A ++ u₁) ++ b ++ (r₂' ++ C)
  have hτ_eq : τ = A ++ Mid' ++ C := by
    simp [τ, Mid', List.append_assoc]
  have hτ_perm : τ.Perm τ₀ := by
    rw [hτ_eq, hτ₀_eq]
    exact (hMid'_perm.append_left A).append_right C
  have hτ_feas : LawlerPrec.MinMax.IsFeasible G N τ := by
    refine ⟨⟨hτ_perm.nodup_iff.mpr hnd₀, fun j => hτ_perm.mem_iff.trans (hmem₀ j)⟩, ?_⟩
    rw [hτ_eq]
    exact pairwise_middle_perm (fun a b => ¬ G b a) A Mid' Mid C (hτ₀_eq ▸ hpair₀) hMid'_perm hMid'_pair
  have hτ_wc : SingleMachinePrec.Biclique.weightedCompletion p w N τ ≤
      SingleMachinePrec.Biclique.weightedCompletion p w N τ₀ := by
    rw [hτ_eq, hτ₀_eq]
    exact weightedCompletion_middle_le p w N A Mid' Mid C
      (hτ₀_eq ▸ hnd₀) (fun j => by rw [← hτ₀_eq]; exact hmem₀ j) hMid'_perm hMid'_wc
  refine ⟨τ, ⟨hτ_feas, fun τ' hτ' => le_trans hτ_wc (hτ₀_opt τ' hτ')⟩,
    A ++ u₁, b, r₂' ++ C, rfl, hb_mem, ?_⟩
  intro m hmM hm_notI
  have hmτ : m ∈ (A ++ u₁) ++ b ++ (r₂' ++ C) := (hτ_feas.1.2 m).mpr (hMN hmM)
  rcases List.mem_append.mp hmτ with hm_left | hm_c
  · rcases List.mem_append.mp hm_left with hm_Au₁ | hm_b
    · rcases List.mem_append.mp hm_Au₁ with hm_A | hm_u₁
      · exact absurd hmM (hA_notM m hm_A)
      · exact absurd hmM (Finset.mem_sdiff.mp (hu₁ m hm_u₁)).2
    · exact absurd ((hb_mem m).mp hm_b) hm_notI
  · exact hm_c

