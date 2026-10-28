-- Prove2me | solution 1 for LawlerWCT.SeriesPar.series_composition_union
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T09:15:58.959014+00:00
-- url     : https://prove2.me/submissions/6eb428fc-d983-4ea9-b5b0-736db933e556

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

private lemma eq_filter_append_filter_not {α : Type*} (p : α → Bool)
    {l : List α} (h : l.Pairwise (fun a b => p b = true → p a = true)) :
    l = l.filter p ++ l.filter (fun x => !p x) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.pairwise_cons] at h
    cases hx : p x
    · have hnone : ∀ y ∈ xs, p y = false := by
        intro y hy
        cases hpy : p y
        · rfl
        · exact absurd (h.1 y hy hpy) (by simp [hx])
      have hfilt : xs.filter p = [] :=
        List.filter_eq_nil_iff.mpr (fun y hy => by simp [hnone y hy])
      have hfilt_not : xs.filter (fun y => !p y) = xs :=
        List.filter_eq_self.mpr (fun y hy => by simp [hnone y hy])
      simp [hx, hfilt, hfilt_not]
    · simp [hx, ← ih h.2]

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

private lemma idxOf_lt_of_transGen {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    {M : Finset ι} (hM : IsModule G N M) {l : List ι}
    (hl : LawlerPrec.MinMax.IsFeasible G M l) {x y : ι}
    (hx : x ∈ M) (hy : y ∈ M) (hxy : Relation.TransGen G x y) :
    l.idxOf x < l.idxOf y := by
  induction hxy with
  | single h => exact idxOf_lt_of_edge G hacyc hl hx hy h
  | @tail b c hxb hbc ih =>
    have hbN : b ∈ N := (hGN b c hbc).1
    have hbM : b ∈ M := module_convex N G hacyc hM hx hbN hy hxb (.single hbc)
    exact lt_trans (ih hbM) (idxOf_lt_of_edge G hacyc hl hbM hy hbc)

private lemma feasible_pairwise_transGen {ι : Type*} [DecidableEq ι]
    (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    {M : Finset ι} (hM : IsModule G N M) {l : List ι}
    (hl : LawlerPrec.MinMax.IsFeasible G M l) :
    l.Pairwise (fun x y => ¬ Relation.TransGen G y x) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij hji
  have hxi : l[i] ∈ M := (hl.1.2 l[i]).mp (List.getElem_mem hi)
  have hyj : l[j] ∈ M := (hl.1.2 l[j]).mp (List.getElem_mem hj)
  have hlt := idxOf_lt_of_transGen N G hGN hacyc hM hl hyj hxi hji
  rw [List.Nodup.idxOf_getElem hl.1.1 j hj, List.Nodup.idxOf_getElem hl.1.1 i hi] at hlt
  omega

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
  rw [idxOf_append_of_notMem hx, Nat.add_assoc, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
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

theorem solution {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (M₁ M₂ : Finset ι) (hdisj : Disjoint M₁ M₂)
    (hM₁ : IsModule G N M₁) (hM₂ : IsModule G N M₂) (hM : IsModule G N (M₁ ∪ M₂))
    (hser : ∀ i ∈ M₁, ∀ j ∈ M₂, Relation.TransGen G i j)
    (F₁ F₂ : List (List ι)) (h₁ : Represents G p w M₁ F₁) (h₂ : Represents G p w M₂ F₂)
    (hratio : ∀ c ∈ F₁, ∀ d ∈ F₂, crho p w d < crho p w c) :
    Represents G p w (M₁ ∪ M₂) (F₁ ++ F₂) := by
  have _ := hp; have _ := hM₁; have _ := hM₂
  rcases h₁ with ⟨hcomp₁, hnd₁, hmem₁, hopt₁⟩
  rcases h₂ with ⟨hcomp₂, hnd₂, hmem₂, hopt₂⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc₁ | hc₂
    · exact hcomp₁ c hc₁
    · exact hcomp₂ c hc₂
  · rw [List.flatten_append, List.nodup_append]
    refine ⟨hnd₁, hnd₂, fun x hx₁ y hx₂ hxy => ?_⟩
    subst hxy
    exact Finset.disjoint_left.mp hdisj ((hmem₁ x).mp hx₁) ((hmem₂ x).mp hx₂)
  · intro j
    rw [List.flatten_append, List.mem_append, hmem₁, hmem₂, Finset.mem_union]
  · intro L hL hord
    have hL_pair : L.Pairwise (fun a b => decide (b ∈ F₁) = true → decide (a ∈ F₁) = true) := by
      refine List.Pairwise.imp_of_mem ?_ hord
      intro a b ha _ hab hbF₁
      rw [decide_eq_true_eq] at hbF₁ ⊢
      by_contra haF₁
      have ha_mem : a ∈ F₁ ++ F₂ := hL.subset ha
      have haF₂ : a ∈ F₂ := (List.mem_append.mp ha_mem).resolve_left haF₁
      exact not_lt_of_ge hab (hratio b hbF₁ a haF₂)
    let L₁ := L.filter (fun c => decide (c ∈ F₁))
    let L₂ := L.filter (fun c => !decide (c ∈ F₁))
    have hL_eq : L = L₁ ++ L₂ := eq_filter_append_filter_not (fun c => decide (c ∈ F₁)) hL_pair
    have hF_disj : ∀ c ∈ F₁, c ∉ F₂ := by
      intro c hc₁ hc₂
      exact lt_irrefl _ (hratio c hc₁ c hc₂)
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
    rw [hL_eq] at hord
    have hord₁ : IsRatioOrder p w L₁ := (List.pairwise_append.mp hord).1
    have hord₂ : IsRatioOrder p w L₂ := (List.pairwise_append.mp hord).2.1
    have hσ₁ := hopt₁ L₁ hL₁_perm hord₁
    have hσ₂ := hopt₂ L₂ hL₂_perm hord₂
    rw [hL_eq, List.flatten_append]
    refine ⟨?_, ?_⟩
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hσ₁.1.1.1, hσ₂.1.1.1, fun x hx₁ y hx₂ hxy => ?_⟩
        subst hxy
        exact Finset.disjoint_left.mp hdisj ((hσ₁.1.1.2 x).mp hx₁) ((hσ₂.1.1.2 x).mp hx₂)
      · intro x
        rw [List.mem_append, hσ₁.1.1.2, hσ₂.1.1.2, Finset.mem_union]
      · rw [List.pairwise_append]
        refine ⟨hσ₁.1.2, hσ₂.1.2, fun x hx₁ y hx₂ hGyx => ?_⟩
        have hxM₁ : x ∈ M₁ := (hσ₁.1.1.2 x).mp hx₁
        have hyM₂ : y ∈ M₂ := (hσ₂.1.1.2 y).mp hx₂
        exact hacyc x (Relation.TransGen.tail (hser x hxM₁ y hyM₂) hGyx)
    · intro l' hl'
      have hl'_tg := feasible_pairwise_transGen N G hGN hacyc hM hl'
      have hl'_pair : l'.Pairwise (fun a b => decide (b ∈ M₁) = true → decide (a ∈ M₁) = true) := by
        refine List.Pairwise.imp_of_mem ?_ hl'_tg
        intro a b ha _ hab hbM₁
        rw [decide_eq_true_eq] at hbM₁ ⊢
        by_contra haM₁
        have haM : a ∈ M₁ ∪ M₂ := (hl'.1.2 a).mp ha
        have haM₂ : a ∈ M₂ := (Finset.mem_union.mp haM).resolve_left haM₁
        exact hab (hser b hbM₁ a haM₂)
      let l₁' := l'.filter (fun x => decide (x ∈ M₁))
      let l₂' := l'.filter (fun x => !decide (x ∈ M₁))
      have hl'_eq : l' = l₁' ++ l₂' := eq_filter_append_filter_not (fun x => decide (x ∈ M₁)) hl'_pair
      have hl₁'_feas : LawlerPrec.MinMax.IsFeasible G M₁ l₁' := by
        refine ⟨⟨hl'.1.1.filter _, fun x => ?_⟩, hl'.2.filter _⟩
        simp only [l₁', List.mem_filter, hl'.1.2, Finset.mem_union, decide_eq_true_eq]
        exact ⟨fun h => h.2, fun h => ⟨Or.inl h, h⟩⟩
      have hl₂'_feas : LawlerPrec.MinMax.IsFeasible G M₂ l₂' := by
        refine ⟨⟨hl'.1.1.filter _, fun x => ?_⟩, hl'.2.filter _⟩
        simp only [l₂', List.mem_filter, hl'.1.2, Finset.mem_union, Bool.not_eq_true',
          decide_eq_false_iff_not]
        exact ⟨fun ⟨h, hx₁⟩ => h.resolve_left hx₁,
               fun hx₂ => ⟨Or.inr hx₂, fun hx₁ => Finset.disjoint_left.mp hdisj hx₁ hx₂⟩⟩
      have hperm₁ : L₁.flatten.Perm l₁' := by
        rw [List.perm_ext_iff_of_nodup hσ₁.1.1.1 hl₁'_feas.1.1]
        intro x
        rw [hσ₁.1.1.2, hl₁'_feas.1.2]
      have hpsum_eq : (L₁.flatten.map p).sum = (l₁'.map p).sum := (hperm₁.map p).sum_eq
      have hle₁ := hσ₁.2 l₁' hl₁'_feas
      have hle₂ := hσ₂.2 l₂' hl₂'_feas
      rw [hl'_eq,
          weightedCompletion_append p w hdisj hσ₁.1.1.2,
          weightedCompletion_append p w hdisj hl₁'_feas.1.2,
          hpsum_eq]
      linarith
