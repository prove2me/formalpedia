-- Prove2me | solution 1 for LawlerWCT.SeriesPar.parallel_composition
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T10:05:39.464563+00:00
-- url     : https://prove2.me/submissions/8012e9b8-ab76-4b88-a55e-579df891e475

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
import Theorems.Thm_LawlerWCT_SeriesPar_ratio_order_optimal
import Theorems.Thm_LawlerWCT_SeriesPar_theorem_1

open LawlerWCT.SeriesPar

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
  have hnd_X : X.Nodup := (List.nodup_append.mp hnd_XA).1
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

private lemma forall_lt_of_no_consecutive_le {ι : Type*} (p w : ι → ℝ) :
    ∀ (b₀ : List ι) (bs : List (List ι)),
      (∀ B₁ b₁ b₂ B₂, b₀ :: bs = B₁ ++ [b₁, b₂] ++ B₂ → crho p w b₂ < crho p w b₁) →
      ∀ b ∈ bs, crho p w b < crho p w b₀
  | b₀, [], _, b, hb => by cases hb
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

private lemma nodup_of_flatten_nodup {α : Type*} {L : List (List α)}
    (hnd : L.flatten.Nodup) (hne : ∀ b ∈ L, b ≠ []) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons b bs ih =>
    rw [List.flatten_cons, List.nodup_append] at hnd
    rw [List.nodup_cons]
    refine ⟨fun hb => ?_, ih hnd.2.1 (fun d hd => hne d (List.mem_cons_of_mem b hd))⟩
    rcases List.exists_mem_of_ne_nil b (hne b List.mem_cons_self) with ⟨x, hx⟩
    exact hnd.2.2 x hx x (List.mem_flatten.mpr ⟨b, hb, hx⟩) rfl

private lemma disjoint_of_mem_flatten_nodup {α : Type*} {F : List (List α)}
    (hnd : F.flatten.Nodup) {c d : List α} (hc : c ∈ F) (hd : d ∈ F) (hcd : c ≠ d)
    {x : α} (hxc : x ∈ c) (hxd : x ∈ d) : False := by
  induction F with
  | nil => cases hc
  | cons a as ih =>
    rw [List.flatten_cons, List.nodup_append] at hnd
    rcases List.mem_cons.mp hc with rfl | hcas <;> rcases List.mem_cons.mp hd with rfl | hdas
    · exact hcd rfl
    · exact hnd.2.2 x hxc x (List.mem_flatten.mpr ⟨d, hdas, hxd⟩) rfl
    · exact hnd.2.2 x hxd x (List.mem_flatten.mpr ⟨c, hcas, hxc⟩) rfl
    · exact ih hnd.2.1 hcas hdas

private lemma map_tag_snd {α : Type*} (p : List α → Bool) (Q : List (List α)) :
    (Q.map (fun b => (p b, b))).map Prod.snd = Q := by
  induction Q <;> simp [*]

private lemma map_tag_filter_fst {α : Type*} (p : List α → Bool) (Q : List (List α)) :
    ((Q.map (fun b => (p b, b))).filter Prod.fst).map Prod.snd = Q.filter p := by
  induction Q with
  | nil => rfl
  | cons b bs ih =>
    cases h : p b <;> simp [h, ih]

private lemma map_tag_filter_not_fst {α : Type*} (p : List α → Bool) (Q : List (List α)) :
    ((Q.map (fun b => (p b, b))).filter (fun x => !x.1)).map Prod.snd =
      Q.filter (fun b => !p b) := by
  induction Q with
  | nil => rfl
  | cons b bs ih =>
    cases h : p b <;> simp [h, ih]

private lemma filter_not_and_filter_self {α : Type*} (p : α → Bool) (Q : List α) :
    (Q.filter (fun b => !p b)).filter p = [] := by
  rw [List.filter_filter]
  exact List.filter_eq_nil_iff.mpr (fun b _ => by simp)

private lemma filter_not_and_filter_other {α : Type*} (p q : α → Bool) (Q : List α)
    (h : ∀ b ∈ Q, q b = true → p b = false) :
    (Q.filter (fun b => !p b)).filter q = Q.filter q := by
  induction Q with
  | nil => rfl
  | cons b bs ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem b hx))
    cases hq : q b
    · cases hp : p b <;> simp [hp, hq, ih']
    · have hp : p b = false := h b List.mem_cons_self hq
      simp [hp, hq, ih']

private lemma merge_all_composites {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (J : Finset ι) (hp : ∀ j ∈ J, 0 < p j)
    (F : List (List ι)) (hF_comp : ∀ c ∈ F, IsComposite p w c)
    (hF_nd : F.flatten.Nodup) :
    ∀ (G : List (List ι)), (∀ c ∈ G, c ∈ F) →
      ∀ (Q : List (List ι)),
        Q.flatten.Nodup →
        (∀ j, j ∈ Q.flatten ↔ j ∈ J) →
        (∀ b ∈ Q, b ≠ []) →
        (∀ b ∈ Q, ∃ c ∈ F, b ⊆ c) →
        (∀ c ∈ F, (Q.filter (fun b => decide (b ⊆ c))).flatten = c) →
        (∀ c ∈ F, c ∉ G → Q.filter (fun b => decide (b ⊆ c)) = [c]) →
        ∃ P : List (List ι), P.Perm F ∧
          SingleMachinePrec.Biclique.weightedCompletion p w J P.flatten ≤
            SingleMachinePrec.Biclique.weightedCompletion p w J Q.flatten
  | [], _, Q, hQ_nd, _, hQ_ne, hQ_sub, _, hQ_done => by
    have hQ_list_nd : Q.Nodup := nodup_of_flatten_nodup hQ_nd hQ_ne
    have hF_list_nd : F.Nodup := nodup_of_flatten_nodup hF_nd (fun c hc => (hF_comp c hc).1)
    have hperm : Q.Perm F := by
      rw [List.perm_ext_iff_of_nodup hQ_list_nd hF_list_nd]
      intro b
      constructor
      · intro hb
        rcases hQ_sub b hb with ⟨c, hcF, hbc⟩
        have hmem : b ∈ Q.filter (fun b' => decide (b' ⊆ c)) :=
          List.mem_filter.mpr ⟨hb, decide_eq_true hbc⟩
        rw [hQ_done c hcF (by simp)] at hmem
        rcases List.mem_singleton.mp hmem with rfl
        exact hcF
      · intro hbF
        have hmem : b ∈ [b] := by simp
        rw [← hQ_done b hbF (by simp)] at hmem
        exact List.mem_of_mem_filter hmem
    exact ⟨Q, hperm, le_rfl⟩
  | c :: G, hGF, Q, hQ_nd, hQ_mem, hQ_ne, hQ_sub, hQ_flat, hQ_done => by
    have hcF : c ∈ F := hGF c List.mem_cons_self
    have hc_comp : IsComposite p w c := hF_comp c hcF
    let P₀ := Q.map (fun b => (decide (b ⊆ c), b))
    have hP₀_snd : P₀.map Prod.snd = Q := map_tag_snd (fun b => decide (b ⊆ c)) Q
    have hP₀_fst : (P₀.filter Prod.fst).map Prod.snd = Q.filter (fun b => decide (b ⊆ c)) :=
      map_tag_filter_fst (fun b => decide (b ⊆ c)) Q
    have hP₀_not_fst : (P₀.filter (fun x => !x.1)).map Prod.snd =
        Q.filter (fun b => !decide (b ⊆ c)) :=
      map_tag_filter_not_fst (fun b => decide (b ⊆ c)) Q
    have hP₀_B_flat : ((P₀.filter Prod.fst).map Prod.snd).flatten = c := by
      rw [hP₀_fst, hQ_flat c hcF]
    have hP₀_ne : ∀ x ∈ P₀, x.2 ≠ [] := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨b, hb, rfl⟩
      exact hQ_ne b hb
    rcases merge_one_composite p w J hp P₀.length P₀ rfl
      (hP₀_snd.symm ▸ hQ_nd) (fun j => by rw [hP₀_snd]; exact hQ_mem j)
      hP₀_ne (hP₀_B_flat.symm ▸ hc_comp) with ⟨R₁, R₂, hR_eq, hR_perm, hR_wc⟩
    rw [hP₀_not_fst] at hR_eq
    rw [hP₀_B_flat, hP₀_snd] at hR_perm hR_wc
    let Q' := R₁ ++ [c] ++ R₂
    have hMem_R : ∀ b ∈ R₁ ++ R₂, b ∈ Q := by
      intro b hb
      rw [hR_eq] at hb
      exact List.mem_of_mem_filter hb
    have hQ'_ne : ∀ b ∈ Q', b ≠ [] := by
      intro b hb
      simp only [Q', List.mem_append, List.mem_singleton] at hb
      rcases hb with (hb | rfl) | hb
      · exact hQ_ne b (hMem_R b (List.mem_append_left _ hb))
      · exact hc_comp.1
      · exact hQ_ne b (hMem_R b (List.mem_append_right _ hb))
    have hQ'_sub : ∀ b ∈ Q', ∃ d ∈ F, b ⊆ d := by
      intro b hb
      simp only [Q', List.mem_append, List.mem_singleton] at hb
      rcases hb with (hb | rfl) | hb
      · exact hQ_sub b (hMem_R b (List.mem_append_left _ hb))
      · exact ⟨b, hcF, List.Subset.refl b⟩
      · exact hQ_sub b (hMem_R b (List.mem_append_right _ hb))
    have hQ'_filt_c : Q'.filter (fun b => decide (b ⊆ c)) = [c] := by
      have hR_filt : (R₁ ++ R₂).filter (fun b => decide (b ⊆ c)) = [] := by
        rw [hR_eq]
        exact filter_not_and_filter_self (fun b => decide (b ⊆ c)) Q
      rw [List.filter_append] at hR_filt
      have hR₁_nil : R₁.filter (fun b => decide (b ⊆ c)) = [] :=
        (List.append_eq_nil_iff.mp hR_filt).1
      have hR₂_nil : R₂.filter (fun b => decide (b ⊆ c)) = [] :=
        (List.append_eq_nil_iff.mp hR_filt).2
      simp [Q', List.filter_append, hR₁_nil, hR₂_nil]
    have hQ'_filt_other : ∀ d ∈ F, d ≠ c →
        Q'.filter (fun b => decide (b ⊆ d)) = Q.filter (fun b => decide (b ⊆ d)) := by
      intro d hdF hdc
      have hc_not_d : decide (c ⊆ d) = false := by
        rw [decide_eq_false_iff_not]
        intro hcd
        rcases List.exists_mem_of_ne_nil c hc_comp.1 with ⟨x, hxc⟩
        exact disjoint_of_mem_flatten_nodup hF_nd hcF hdF hdc.symm hxc (hcd hxc)
      have hR_other : (R₁ ++ R₂).filter (fun b => decide (b ⊆ d)) =
          Q.filter (fun b => decide (b ⊆ d)) := by
        rw [hR_eq]
        refine filter_not_and_filter_other (fun b => decide (b ⊆ c)) (fun b => decide (b ⊆ d)) Q ?_
        intro b hb hbd
        rw [decide_eq_true_eq] at hbd
        rw [decide_eq_false_iff_not]
        intro hbc
        rcases List.exists_mem_of_ne_nil b (hQ_ne b hb) with ⟨x, hxb⟩
        exact disjoint_of_mem_flatten_nodup hF_nd hcF hdF hdc.symm (hbc hxb) (hbd hxb)
      rw [List.filter_append] at hR_other
      simp [Q', List.filter_append, hc_not_d, hR_other]
    have hQ'_flat : ∀ d ∈ F, (Q'.filter (fun b => decide (b ⊆ d))).flatten = d := by
      intro d hdF
      by_cases hdc : d = c
      · subst hdc
        simp [hQ'_filt_c]
      · rw [hQ'_filt_other d hdF hdc, hQ_flat d hdF]
    have hQ'_done : ∀ d ∈ F, d ∉ G → Q'.filter (fun b => decide (b ⊆ d)) = [d] := by
      intro d hdF hdG
      by_cases hdc : d = c
      · subst hdc
        exact hQ'_filt_c
      · rw [hQ'_filt_other d hdF hdc]
        exact hQ_done d hdF (fun hmem => by
          rcases List.mem_cons.mp hmem with rfl | hG
          · exact hdc rfl
          · exact hdG hG)
    rcases merge_all_composites p w J hp F hF_comp hF_nd G
      (fun d hd => hGF d (List.mem_cons_of_mem c hd)) Q'
      (hR_perm.nodup_iff.mpr hQ_nd) (fun j => hR_perm.mem_iff.trans (hQ_mem j))
      hQ'_ne hQ'_sub hQ'_flat hQ'_done with ⟨P, hP_perm, hP_wc⟩
    exact ⟨P, hP_perm, le_trans hP_wc hR_wc⟩

private lemma filter_singleton_subset {ι : Type*} [DecidableEq ι] (c : List ι) (τ : List ι) :
    ((τ.map (fun x => [x])).filter (fun b => decide (b ⊆ c))).flatten =
      τ.filter (fun x => decide (x ∈ c)) := by
  induction τ with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x ∈ c <;> simp [hx, ih]

private lemma map_singleton_flatten {ι : Type*} (τ : List ι) :
    (τ.map (fun x => [x])).flatten = τ := by
  induction τ <;> simp [*]

private lemma exists_perm_flatten_le {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (J : Finset ι) (hp : ∀ j ∈ J, 0 < p j)
    (F : List (List ι)) (hF_comp : ∀ c ∈ F, IsComposite p w c)
    (hF_nd : F.flatten.Nodup) (hF_mem : ∀ j, j ∈ F.flatten ↔ j ∈ J)
    (τ : List ι) (hτ_nd : τ.Nodup) (hτ_mem : ∀ j, j ∈ τ ↔ j ∈ J)
    (hτ_filt : ∀ c ∈ F, τ.filter (fun x => decide (x ∈ c)) = c) :
    ∃ P : List (List ι), P.Perm F ∧
      SingleMachinePrec.Biclique.weightedCompletion p w J P.flatten ≤
        SingleMachinePrec.Biclique.weightedCompletion p w J τ := by
  let Q₀ := τ.map (fun x => [x])
  have hQ₀_flat : Q₀.flatten = τ := map_singleton_flatten τ
  have hQ₀_ne : ∀ b ∈ Q₀, b ≠ [] := by
    intro b hb
    rcases List.mem_map.mp hb with ⟨x, _, rfl⟩
    simp
  have hQ₀_sub : ∀ b ∈ Q₀, ∃ c ∈ F, b ⊆ c := by
    intro b hb
    rcases List.mem_map.mp hb with ⟨x, hxτ, rfl⟩
    have hxF : x ∈ F.flatten := (hF_mem x).mpr ((hτ_mem x).mp hxτ)
    rcases List.mem_flatten.mp hxF with ⟨c, hcF, hxc⟩
    exact ⟨c, hcF, by simp [hxc]⟩
  have hQ₀_filt : ∀ c ∈ F, (Q₀.filter (fun b => decide (b ⊆ c))).flatten = c := by
    intro c hcF
    rw [filter_singleton_subset c τ, hτ_filt c hcF]
  rcases merge_all_composites p w J hp F hF_comp hF_nd F (fun c hc => hc) Q₀
    (hQ₀_flat.symm ▸ hτ_nd) (fun j => by rw [hQ₀_flat]; exact hτ_mem j)
    hQ₀_ne hQ₀_sub hQ₀_filt (fun c hc hnot => absurd hc hnot) with ⟨P, hP_perm, hP_wc⟩
  rw [hQ₀_flat] at hP_wc
  exact ⟨P, hP_perm, hP_wc⟩

private lemma filter_eq_nil_of_disjoint {α : Type*} [DecidableEq α] {a c : List α}
    (h : ∀ x ∈ a, ∀ y ∈ c, x ≠ y) :
    a.filter (fun x => decide (x ∈ c)) = [] :=
  List.filter_eq_nil_iff.mpr (fun x hxa => by
    simp only [decide_eq_true_eq]
    intro hxc
    exact h x hxa x hxc rfl)

private lemma flatten_filter_mem_of_nodup {α : Type*} [DecidableEq α] {L : List (List α)}
    (hnd : L.flatten.Nodup) {c : List α} (hc : c ∈ L) :
    L.flatten.filter (fun x => decide (x ∈ c)) = c := by
  induction L with
  | nil => cases hc
  | cons a as ih =>
    rw [List.flatten_cons, List.nodup_append] at hnd
    rw [List.flatten_cons, List.filter_append]
    rcases List.mem_cons.mp hc with rfl | hcas
    · have h1 : c.filter (fun x => decide (x ∈ c)) = c :=
        List.filter_eq_self.mpr (fun x hx => decide_eq_true hx)
      have h2 : as.flatten.filter (fun x => decide (x ∈ c)) = [] :=
        filter_eq_nil_of_disjoint (fun x hxa y hyc hxy => hnd.2.2 y hyc x hxa hxy.symm)
      rw [h1, h2, List.append_nil]
    · have h1 : a.filter (fun x => decide (x ∈ c)) = [] :=
        filter_eq_nil_of_disjoint (fun x hxa y hyc hxy =>
          hnd.2.2 x hxa y (List.mem_flatten.mpr ⟨c, hcas, hyc⟩) hxy)
      rw [h1, List.nil_append, ih hnd.2.1 hcas]

private lemma eq_of_nodup_pairwise {α : Type*} {R : α → α → Prop} :
    ∀ {l₁ l₂ : List α},
      l₁.Nodup → l₂.Nodup →
      (∀ x, x ∈ l₁ ↔ x ∈ l₂) →
      l₁.Pairwise R →
      l₂.Pairwise (fun a b => ¬ R b a) →
      l₁ = l₂
  | [], [], _, _, _, _, _ => rfl
  | a :: _, [], _, _, hmem, _, _ => by
    have := (hmem a).mp List.mem_cons_self
    simp at this
  | [], b :: _, _, _, hmem, _, _ => by
    have := (hmem b).mpr List.mem_cons_self
    simp at this
  | a :: as, b :: bs, hnd₁, hnd₂, hmem, hp₁, hp₂ => by
    rw [List.nodup_cons] at hnd₁ hnd₂
    rw [List.pairwise_cons] at hp₁ hp₂
    have hab : a = b := by
      by_contra hne
      have ha_bs : a ∈ bs := (List.mem_cons.mp ((hmem a).mp List.mem_cons_self)).resolve_left hne
      have hb_as : b ∈ as := (List.mem_cons.mp ((hmem b).mpr List.mem_cons_self)).resolve_left (Ne.symm hne)
      exact hp₂.1 a ha_bs (hp₁.1 b hb_as)
    subst hab
    congr 1
    refine eq_of_nodup_pairwise hnd₁.2 hnd₂.2 (fun x => ?_) hp₁.2 hp₂.2
    constructor <;> intro hx
    · have hx2 : x ∈ a :: bs := (hmem x).mp (List.mem_cons_of_mem a hx)
      exact (List.mem_cons.mp hx2).resolve_left (fun h => hnd₁.1 (h ▸ hx))
    · have hx1 : x ∈ a :: as := (hmem x).mpr (List.mem_cons_of_mem a hx)
      exact (List.mem_cons.mp hx1).resolve_left (fun h => hnd₂.1 (h ▸ hx))

private lemma pairwise_of_filter_union {ι : Type*} [DecidableEq ι] (G : ι → ι → Prop)
    (M₁ M₂ : Finset ι)
    (hunc : ∀ i ∈ M₁, ∀ j ∈ M₂, ¬ G i j ∧ ¬ G j i) :
    ∀ {l : List ι},
      (∀ x ∈ l, x ∈ M₁ ∪ M₂) →
      (l.filter (fun x => decide (x ∈ M₁))).Pairwise (fun a b => ¬ G b a) →
      (l.filter (fun x => decide (x ∈ M₂))).Pairwise (fun a b => ¬ G b a) →
      l.Pairwise (fun a b => ¬ G b a)
  | [], _, _, _ => List.Pairwise.nil
  | a :: as, hmem, hp₁, hp₂ => by
    rw [List.pairwise_cons]
    have hp₁_as : (as.filter (fun x => decide (x ∈ M₁))).Pairwise (fun x y => ¬ G y x) := by
      by_cases ha₁ : a ∈ M₁ <;> simp [ha₁] at hp₁
      · exact hp₁.2
      · exact hp₁
    have hp₂_as : (as.filter (fun x => decide (x ∈ M₂))).Pairwise (fun x y => ¬ G y x) := by
      by_cases ha₂ : a ∈ M₂ <;> simp [ha₂] at hp₂
      · exact hp₂.2
      · exact hp₂
    refine ⟨fun b hb => ?_,
      pairwise_of_filter_union G M₁ M₂ hunc (fun x hx => hmem x (List.mem_cons_of_mem a hx)) hp₁_as hp₂_as⟩
    rcases Finset.mem_union.mp (hmem a List.mem_cons_self) with ha₁ | ha₂ <;>
      rcases Finset.mem_union.mp (hmem b (List.mem_cons_of_mem a hb)) with hb₁ | hb₂
    · simp [ha₁] at hp₁
      exact hp₁.1 b hb hb₁
    · exact (hunc a ha₁ b hb₂).2
    · exact (hunc b hb₁ a ha₂).1
    · simp [ha₂] at hp₂
      exact hp₂.1 b hb hb₂

private lemma flatten_filter_of_blocks {ι : Type*} [DecidableEq ι] (M₁ : Finset ι)
    (F₁ : List (List ι))
    (h₁ : ∀ c ∈ F₁, ∀ x ∈ c, x ∈ M₁) :
    ∀ (L : List (List ι)),
      (∀ c ∈ L, c ∉ F₁ → ∀ x ∈ c, x ∉ M₁) →
      L.flatten.filter (fun x => decide (x ∈ M₁)) =
        (L.filter (fun c => decide (c ∈ F₁))).flatten
  | [], _ => rfl
  | c :: cs, hnot => by
    rw [List.flatten_cons, List.filter_append]
    have ih := flatten_filter_of_blocks M₁ F₁ h₁ cs (fun d hd => hnot d (List.mem_cons_of_mem c hd))
    by_cases hc : c ∈ F₁
    · have hc_filt : c.filter (fun x => decide (x ∈ M₁)) = c :=
        List.filter_eq_self.mpr (fun x hx => decide_eq_true (h₁ c hc x hx))
      simp [hc, hc_filt, ih]
    · have hc_filt : c.filter (fun x => decide (x ∈ M₁)) = [] :=
        List.filter_eq_nil_iff.mpr (fun x hx => by simp [hnot c List.mem_cons_self hc x hx])
      simp [hc, hc_filt, ih]

private lemma flatten_filter_of_not_blocks {ι : Type*} [DecidableEq ι] (M₂ : Finset ι)
    (F₁ : List (List ι))
    (h₁ : ∀ c ∈ F₁, ∀ x ∈ c, x ∉ M₂) :
    ∀ (L : List (List ι)),
      (∀ c ∈ L, c ∉ F₁ → ∀ x ∈ c, x ∈ M₂) →
      L.flatten.filter (fun x => decide (x ∈ M₂)) =
        (L.filter (fun c => !decide (c ∈ F₁))).flatten
  | [], _ => rfl
  | c :: cs, hnot => by
    rw [List.flatten_cons, List.filter_append]
    have ih := flatten_filter_of_not_blocks M₂ F₁ h₁ cs (fun d hd => hnot d (List.mem_cons_of_mem c hd))
    by_cases hc : c ∈ F₁
    · have hc_filt : c.filter (fun x => decide (x ∈ M₂)) = [] :=
        List.filter_eq_nil_iff.mpr (fun x hx => by simp [h₁ c hc x hx])
      simp [hc, hc_filt, ih]
    · have hc_filt : c.filter (fun x => decide (x ∈ M₂)) = c :=
        List.filter_eq_self.mpr (fun x hx => decide_eq_true (hnot c List.mem_cons_self hc x hx))
      simp [hc, hc_filt, ih]

private lemma feasible_restrict_iff {ι : Type*} [DecidableEq ι] (G : ι → ι → Prop)
    (M S : Finset ι) (hSM : S ⊆ M) (l : List ι) :
    LawlerPrec.MinMax.IsFeasible (fun i j => i ∈ M ∧ j ∈ M ∧ G i j) S l ↔
      LawlerPrec.MinMax.IsFeasible G S l := by
  refine ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · rw [List.pairwise_iff_getElem] at h2 ⊢
    intro i j hi hj hij hG
    have hxi : l[i] ∈ M := hSM ((h1.2 l[i]).mp (List.getElem_mem hi))
    have hyj : l[j] ∈ M := hSM ((h1.2 l[j]).mp (List.getElem_mem hj))
    exact h2 i j hi hj hij ⟨hyj, hxi, hG⟩
  · exact List.Pairwise.imp (fun h hGM => h hGM.2.2) h2

private lemma optimal_restrict_iff {ι : Type*} [DecidableEq ι] (G : ι → ι → Prop) (p w : ι → ℝ)
    (M S : Finset ι) (hSM : S ⊆ M) (l : List ι) :
    SingleMachinePrec.Biclique.IsOptimalSchedule (fun i j => i ∈ M ∧ j ∈ M ∧ G i j) p w S l ↔
      SingleMachinePrec.Biclique.IsOptimalSchedule G p w S l := by
  simp only [SingleMachinePrec.Biclique.IsOptimalSchedule, feasible_restrict_iff G M S hSM]

private lemma transGen_imp_of_edge_imp {ι : Type*} {R : ι → ι → Prop} {P : ι → Prop}
    (h : ∀ i j, R i j → P i ∧ P j) {x y : ι} (hxy : Relation.TransGen R x y) :
    P x ∧ P y := by
  induction hxy with
  | single hr => exact h _ _ hr
  | tail _ hbc ih => exact ⟨ih.1, (h _ _ hbc).2⟩

private lemma transGen_idxOf_lt {ι : Type*} [DecidableEq ι] {R : ι → ι → Prop} {l : List ι}
    (h : ∀ i j, R i j → l.idxOf i < l.idxOf j) {x y : ι} (hxy : Relation.TransGen R x y) :
    l.idxOf x < l.idxOf y := by
  induction hxy with
  | single hr => exact h _ _ hr
  | tail _ hbc ih => exact lt_trans ih (h _ _ hbc)

private lemma transGen_mono {ι : Type*} {R₁ R₂ : ι → ι → Prop}
    (h : ∀ i j, R₁ i j → R₂ i j) {x y : ι} (hxy : Relation.TransGen R₁ x y) :
    Relation.TransGen R₂ x y := by
  induction hxy with
  | single hr => exact .single (h _ _ hr)
  | tail _ hbc ih => exact .tail ih (h _ _ hbc)

private lemma transGen_iff_of_edge_iff {ι : Type*} {R : ι → ι → Prop} {P : ι → Prop}
    (h : ∀ i j, R i j → (P i ↔ P j)) {x y : ι} (hxy : Relation.TransGen R x y) :
    P x ↔ P y := by
  induction hxy with
  | single hr => exact h _ _ hr
  | tail _ hbc ih => exact ih.trans (h _ _ hbc)

private lemma perm_flatten {α : Type*} {L₁ L₂ : List (List α)} (h : L₁.Perm L₂) :
    L₁.flatten.Perm L₂.flatten := by
  induction h with
  | nil => exact List.Perm.nil
  | cons x _ ih => exact List.Perm.append_left x ih
  | swap x y l =>
    simp only [List.flatten_cons, ← List.append_assoc]
    exact List.Perm.append_right l.flatten List.perm_append_comm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private lemma filter_sub_filter {ι : Type*} [DecidableEq ι] (M : Finset ι) (c : List ι)
    (hc : ∀ x ∈ c, x ∈ M) (τ : List ι) :
    τ.filter (fun x => decide (x ∈ c)) =
      (τ.filter (fun x => decide (x ∈ M))).filter (fun x => decide (x ∈ c)) := by
  rw [List.filter_filter]
  refine List.filter_congr (fun x _ => ?_)
  by_cases hxc : x ∈ c
  · simp [hxc, hc x hxc]
  · simp [hxc]

private lemma pairwise_idxOf_lt {ι : Type*} [DecidableEq ι] {l : List ι} (hnd : l.Nodup) :
    l.Pairwise (fun a b => l.idxOf a < l.idxOf b) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [List.Nodup.idxOf_getElem hnd i hi, List.Nodup.idxOf_getElem hnd j hj]
  exact hij

theorem solution {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (M₁ M₂ : Finset ι) (hdisj : Disjoint M₁ M₂)
    (hM₁ : IsModule G N M₁) (hM₂ : IsModule G N M₂) (hM : IsModule G N (M₁ ∪ M₂))
    (hunc : ∀ i ∈ M₁, ∀ j ∈ M₂, ¬ Relation.TransGen G i j ∧ ¬ Relation.TransGen G j i)
    (F₁ F₂ : List (List ι)) (h₁ : Represents G p w M₁ F₁) (h₂ : Represents G p w M₂ F₂) :
    Represents G p w (M₁ ∪ M₂) (F₁ ++ F₂) := by
  have _ := hGN
  rcases h₁ with ⟨hcomp₁, hnd₁, hmem₁, hopt₁⟩
  rcases h₂ with ⟨hcomp₂, hnd₂, hmem₂, hopt₂⟩
  have hcomp_all : ∀ c ∈ F₁ ++ F₂, IsComposite p w c := by
    intro c hc
    rcases List.mem_append.mp hc with hc₁ | hc₂
    · exact hcomp₁ c hc₁
    · exact hcomp₂ c hc₂
  have hnd_all : (F₁ ++ F₂).flatten.Nodup := by
    rw [List.flatten_append, List.nodup_append]
    refine ⟨hnd₁, hnd₂, fun x hx₁ y hx₂ hxy => ?_⟩
    subst hxy
    exact Finset.disjoint_left.mp hdisj ((hmem₁ x).mp hx₁) ((hmem₂ x).mp hx₂)
  have hmem_all : ∀ j, j ∈ (F₁ ++ F₂).flatten ↔ j ∈ M₁ ∪ M₂ := by
    intro j
    rw [List.flatten_append, List.mem_append, hmem₁, hmem₂, Finset.mem_union]
  refine ⟨hcomp_all, hnd_all, hmem_all, fun L hL hord => ?_⟩
  have hF_disj : ∀ c ∈ F₁, c ∉ F₂ := by
    intro c hc₁ hc₂
    rcases List.exists_mem_of_ne_nil c (hcomp₁ c hc₁).1 with ⟨x, hxc⟩
    exact Finset.disjoint_left.mp hdisj
      ((hmem₁ x).mp (List.mem_flatten.mpr ⟨c, hc₁, hxc⟩))
      ((hmem₂ x).mp (List.mem_flatten.mpr ⟨c, hc₂, hxc⟩))
  let L₁ := L.filter (fun c => decide (c ∈ F₁))
  let L₂ := L.filter (fun c => !decide (c ∈ F₁))
  have hF₁_filt : (F₁ ++ F₂).filter (fun c => decide (c ∈ F₁)) = F₁ := by
    rw [List.filter_append, List.filter_eq_self.mpr (fun c hc => decide_eq_true hc),
        List.filter_eq_nil_iff.mpr (fun c hc => by
          simp [show c ∉ F₁ from fun hc₁ => hF_disj c hc₁ hc]),
        List.append_nil]
  have hF₂_filt : (F₁ ++ F₂).filter (fun c => !decide (c ∈ F₁)) = F₂ := by
    rw [List.filter_append,
        List.filter_eq_nil_iff.mpr (fun c hc => by simp [hc]),
        List.filter_eq_self.mpr (fun c hc => by
          simp [show c ∉ F₁ from fun hc₁ => hF_disj c hc₁ hc]),
        List.nil_append]
  have hL₁_perm : L₁.Perm F₁ := by
    have hp := hL.filter (fun c => decide (c ∈ F₁))
    rwa [hF₁_filt] at hp
  have hL₂_perm : L₂.Perm F₂ := by
    have hp := hL.filter (fun c => !decide (c ∈ F₁))
    rwa [hF₂_filt] at hp
  have hord₁ : IsRatioOrder p w L₁ := hord.filter _
  have hord₂ : IsRatioOrder p w L₂ := hord.filter _
  have hσ₁ := hopt₁ L₁ hL₁_perm hord₁
  have hσ₂ := hopt₂ L₂ hL₂_perm hord₂
  have hL_flat_perm : L.flatten.Perm (F₁ ++ F₂).flatten := perm_flatten hL
  have hL_nd : L.flatten.Nodup := hL_flat_perm.nodup_iff.mpr hnd_all
  have hL_mem : ∀ j, j ∈ L.flatten ↔ j ∈ M₁ ∪ M₂ :=
    fun j => hL_flat_perm.mem_iff.trans (hmem_all j)
  have hF₁_sub : ∀ c ∈ F₁, ∀ x ∈ c, x ∈ M₁ :=
    fun c hc x hx => (hmem₁ x).mp (List.mem_flatten.mpr ⟨c, hc, hx⟩)
  have hF₂_sub : ∀ c ∈ F₂, ∀ x ∈ c, x ∈ M₂ :=
    fun c hc x hx => (hmem₂ x).mp (List.mem_flatten.mpr ⟨c, hc, hx⟩)
  have hL_filt₁ : L.flatten.filter (fun x => decide (x ∈ M₁)) = L₁.flatten := by
    refine flatten_filter_of_blocks M₁ F₁ hF₁_sub L (fun c hcL hcF₁ x hxc => ?_)
    have hcF₂ : c ∈ F₂ := (List.mem_append.mp (hL.subset hcL)).resolve_left hcF₁
    exact fun hxM₁ => Finset.disjoint_left.mp hdisj hxM₁ (hF₂_sub c hcF₂ x hxc)
  have hL_filt₂ : L.flatten.filter (fun x => decide (x ∈ M₂)) = L₂.flatten := by
    refine flatten_filter_of_not_blocks M₂ F₁
      (fun c hc₁ x hx hxM₂ => Finset.disjoint_left.mp hdisj (hF₁_sub c hc₁ x hx) hxM₂)
      L (fun c hcL hcF₁ x hxc => ?_)
    have hcF₂ : c ∈ F₂ := (List.mem_append.mp (hL.subset hcL)).resolve_left hcF₁
    exact hF₂_sub c hcF₂ x hxc
  have hL_pair : L.flatten.Pairwise (fun a b => ¬ G b a) := by
    refine pairwise_of_filter_union G M₁ M₂
      (fun i hi j hj => ⟨fun h => (hunc i hi j hj).1 (.single h), fun h => (hunc i hi j hj).2 (.single h)⟩)
      (fun x hx => (hL_mem x).mp hx) ?_ ?_
    · rw [hL_filt₁]; exact hσ₁.1.2
    · rw [hL_filt₂]; exact hσ₂.1.2
  refine ⟨⟨⟨hL_nd, hL_mem⟩, hL_pair⟩, fun l' hl' => ?_⟩
  let M := M₁ ∪ M₂
  let G_M : ι → ι → Prop := fun i j => i ∈ M ∧ j ∈ M ∧ G i j
  have hpM : ∀ j ∈ M, 0 < p j := fun j hj => hp j (hM.2.1 hj)
  have hGM_M : ∀ i j, G_M i j → i ∈ M ∧ j ∈ M := fun _ _ h => ⟨h.1, h.2.1⟩
  have hGM_acyc : ∀ j, ¬ Relation.TransGen G_M j j :=
    fun j h => hacyc j (transGen_mono (fun _ _ h => h.2.2) h)
  have hM₁_mod : IsModule G_M M M₁ := by
    refine ⟨hM₁.1, Finset.subset_union_left, fun u huM huM₁ => Or.inr (Or.inr (fun m hm => ?_))⟩
    have huM₂ : u ∈ M₂ := (Finset.mem_union.mp huM).resolve_left huM₁
    exact ⟨fun h => (hunc m hm u huM₂).2 (transGen_mono (fun _ _ h => h.2.2) h),
           fun h => (hunc m hm u huM₂).1 (transGen_mono (fun _ _ h => h.2.2) h)⟩
  have hσ₁_GM : SingleMachinePrec.Biclique.IsOptimalSchedule G_M p w M₁ L₁.flatten :=
    (optimal_restrict_iff G p w M M₁ Finset.subset_union_left L₁.flatten).mpr hσ₁
  rcases theorem_1 M G_M hGM_M hGM_acyc p w hpM M₁ hM₁_mod L₁.flatten hσ₁_GM with
    ⟨τ₁, hτ₁_opt, hτ₁_filt⟩
  let G₁ : ι → ι → Prop := fun i j => G_M i j ∨ (i ∈ M₁ ∧ j ∈ M₁ ∧ τ₁.idxOf i < τ₁.idxOf j)
  have hG₁_edge : ∀ i j, G₁ i j → i ∈ M ∧ j ∈ M ∧ τ₁.idxOf i < τ₁.idxOf j := by
    intro i j h
    rcases h with hGM | ⟨hi₁, hj₁, hij⟩
    · exact ⟨hGM.1, hGM.2.1, idxOf_lt_of_edge G_M hGM_acyc hτ₁_opt.1 hGM.1 hGM.2.1 hGM⟩
    · exact ⟨Finset.mem_union_left M₂ hi₁, Finset.mem_union_left M₂ hj₁, hij⟩
  have hG₁_M : ∀ i j, G₁ i j → i ∈ M ∧ j ∈ M := fun i j h => ⟨(hG₁_edge i j h).1, (hG₁_edge i j h).2.1⟩
  have hG₁_acyc : ∀ j, ¬ Relation.TransGen G₁ j j :=
    fun j h => lt_irrefl _ (transGen_idxOf_lt (fun a b hab => (hG₁_edge a b hab).2.2) h)
  have hG₁_iff_M₁ : ∀ i j, G₁ i j → (i ∈ M₁ ↔ j ∈ M₁) := by
    intro i j h
    rcases h with ⟨hiM, hjM, hG⟩ | ⟨hi₁, hj₁, _⟩
    · constructor
      · intro hi₁
        by_contra hj₁
        have hj₂ : j ∈ M₂ := (Finset.mem_union.mp hjM).resolve_left hj₁
        exact (hunc i hi₁ j hj₂).1 (.single hG)
      · intro hj₁
        by_contra hi₁
        have hi₂ : i ∈ M₂ := (Finset.mem_union.mp hiM).resolve_left hi₁
        exact (hunc j hj₁ i hi₂).2 (.single hG)
    · exact ⟨fun _ => hj₁, fun _ => hi₁⟩
  have hM₂_mod : IsModule G₁ M M₂ := by
    refine ⟨hM₂.1, Finset.subset_union_right, fun u huM huM₂ => Or.inr (Or.inr (fun m hm => ?_))⟩
    have huM₁ : u ∈ M₁ := (Finset.mem_union.mp huM).resolve_right huM₂
    have hm_not_M₁ : m ∉ M₁ := fun hm₁ => Finset.disjoint_left.mp hdisj hm₁ hm
    exact ⟨fun h => hm_not_M₁ ((transGen_iff_of_edge_iff hG₁_iff_M₁ h).mp huM₁),
           fun h => hm_not_M₁ ((transGen_iff_of_edge_iff hG₁_iff_M₁ h).mpr huM₁)⟩
  have hFeas_G₁_M₂ : ∀ s, LawlerPrec.MinMax.IsFeasible G₁ M₂ s ↔ LawlerPrec.MinMax.IsFeasible G M₂ s := by
    intro s
    refine ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
    · rw [List.pairwise_iff_getElem] at h2 ⊢
      intro i j hi hj hij hG
      have hxi : s[i] ∈ M₂ := (h1.2 s[i]).mp (List.getElem_mem hi)
      have hyj : s[j] ∈ M₂ := (h1.2 s[j]).mp (List.getElem_mem hj)
      exact h2 i j hi hj hij (Or.inl ⟨Finset.mem_union_right M₁ hyj, Finset.mem_union_right M₁ hxi, hG⟩)
    · rw [List.pairwise_iff_getElem] at h2 ⊢
      intro i j hi hj hij hG₁
      rcases hG₁ with ⟨_, _, hG⟩ | ⟨hy₁, _, _⟩
      · exact h2 i j hi hj hij hG
      · have hy₂ : s[j] ∈ M₂ := (h1.2 s[j]).mp (List.getElem_mem hj)
        exact Finset.disjoint_left.mp hdisj hy₁ hy₂
  have hσ₂_G₁ : SingleMachinePrec.Biclique.IsOptimalSchedule G₁ p w M₂ L₂.flatten :=
    ⟨(hFeas_G₁_M₂ L₂.flatten).mpr hσ₂.1, fun s hs => hσ₂.2 s ((hFeas_G₁_M₂ s).mp hs)⟩
  rcases theorem_1 M G₁ hG₁_M hG₁_acyc p w hpM M₂ hM₂_mod L₂.flatten hσ₂_G₁ with
    ⟨τ₂, hτ₂_opt, hτ₂_filt₂⟩
  have hτ₁_feas_G₁ : LawlerPrec.MinMax.IsFeasible G₁ M τ₁ := by
    refine ⟨hτ₁_opt.1.1, ?_⟩
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij hG₁
    have hlt := (hG₁_edge τ₁[j] τ₁[i] hG₁).2.2
    rw [List.Nodup.idxOf_getElem hτ₁_opt.1.1.1 j hj, List.Nodup.idxOf_getElem hτ₁_opt.1.1.1 i hi] at hlt
    omega
  have hwc_τ₂_τ₁ : SingleMachinePrec.Biclique.weightedCompletion p w M τ₂ ≤
      SingleMachinePrec.Biclique.weightedCompletion p w M τ₁ :=
    hτ₂_opt.2 τ₁ hτ₁_feas_G₁
  have hwc_τ₁_l' : SingleMachinePrec.Biclique.weightedCompletion p w M τ₁ ≤
      SingleMachinePrec.Biclique.weightedCompletion p w M l' :=
    hτ₁_opt.2 l' ((feasible_restrict_iff G M M (Finset.Subset.refl M) l').mpr hl')
  have hτ₂_filt₁ : τ₂.filter (fun x => decide (x ∈ M₁)) = L₁.flatten := by
    rw [← hτ₁_filt]
    refine (eq_of_nodup_pairwise (R := fun a b => a ∈ M₁ ∧ b ∈ M₁ ∧ τ₁.idxOf a < τ₁.idxOf b)
      (hτ₁_opt.1.1.1.filter _) (hτ₂_opt.1.1.1.filter _) ?_ ?_ ?_).symm
    · intro x
      simp only [List.mem_filter, hτ₁_opt.1.1.2, hτ₂_opt.1.1.2, decide_eq_true_eq]
    · have hp_idx : (τ₁.filter (fun x => decide (x ∈ M₁))).Pairwise
          (fun a b => τ₁.idxOf a < τ₁.idxOf b) :=
        (pairwise_idxOf_lt hτ₁_opt.1.1.1).filter _
      refine List.Pairwise.imp_of_mem ?_ hp_idx
      intro a b ha hb hab
      simp only [List.mem_filter, decide_eq_true_eq] at ha hb
      exact ⟨ha.2, hb.2, hab⟩
    · have hp_G₁ : (τ₂.filter (fun x => decide (x ∈ M₁))).Pairwise (fun a b => ¬ G₁ b a) :=
        hτ₂_opt.1.2.filter _
      exact List.Pairwise.imp (fun h hr => h (Or.inr hr)) hp_G₁
  have hτ₂_filt_all : ∀ c ∈ F₁ ++ F₂, τ₂.filter (fun x => decide (x ∈ c)) = c := by
    intro c hc
    rcases List.mem_append.mp hc with hc₁ | hc₂
    · rw [filter_sub_filter M₁ c (hF₁_sub c hc₁) τ₂, hτ₂_filt₁]
      exact flatten_filter_mem_of_nodup (perm_flatten hL₁_perm |>.nodup_iff.mpr hnd₁)
        (hL₁_perm.mem_iff.mpr hc₁)
    · rw [filter_sub_filter M₂ c (hF₂_sub c hc₂) τ₂, hτ₂_filt₂]
      exact flatten_filter_mem_of_nodup (perm_flatten hL₂_perm |>.nodup_iff.mpr hnd₂)
        (hL₂_perm.mem_iff.mpr hc₂)
  rcases exists_perm_flatten_le p w M hpM (F₁ ++ F₂) hcomp_all hnd_all hmem_all
    τ₂ hτ₂_opt.1.1.1 hτ₂_opt.1.1.2 hτ₂_filt_all with ⟨P, hP_perm, hwc_P_τ₂⟩
  have hM_toFinset : (F₁ ++ F₂).flatten.toFinset = M := by
    ext j
    simp only [List.mem_toFinset, hmem_all, M]
  have hwc_L_P : SingleMachinePrec.Biclique.weightedCompletion p w M L.flatten ≤
      SingleMachinePrec.Biclique.weightedCompletion p w M P.flatten := by
    rw [← hM_toFinset]
    exact ratio_order_optimal p w (F₁ ++ F₂) (fun c hc => (hcomp_all c hc).1) hnd_all
      (fun j hj => hpM j ((hmem_all j).mp hj)) L P hL hord hP_perm
  linarith
