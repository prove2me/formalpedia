-- Prove2me | solution 1 for LawlerWCT.SeriesPar.series_parallel_algorithm_optimal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:40:00.354179+00:00
-- url     : https://prove2.me/submissions/fef50def-3a97-47ac-9c13-6bdafe2b68a9

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
import Theorems.Thm_LawlerWCT_SeriesPar_subtree_isModule
import Theorems.Thm_LawlerWCT_SeriesPar_parallel_composition
import Theorems.Thm_LawlerWCT_SeriesPar_series_composition_procedure

open LawlerWCT.SeriesPar

private lemma prec_mem_leaves {ι : Type*} (T : SPTree ι) {i j : ι} (h : T.prec i j) :
    i ∈ T.leaves ∧ j ∈ T.leaves := by
  induction T with
  | leaf _ => cases h
  | series l r ihl ihr =>
    rcases h with hl | hr | ⟨hi, hj⟩
    · obtain ⟨hi, hj⟩ := ihl hl
      exact ⟨List.mem_append_left _ hi, List.mem_append_left _ hj⟩
    · obtain ⟨hi, hj⟩ := ihr hr
      exact ⟨List.mem_append_right _ hi, List.mem_append_right _ hj⟩
    · exact ⟨List.mem_append_left _ hi, List.mem_append_right _ hj⟩
  | parallel l r ihl ihr =>
    rcases h with hl | hr
    · obtain ⟨hi, hj⟩ := ihl hl
      exact ⟨List.mem_append_left _ hi, List.mem_append_left _ hj⟩
    · obtain ⟨hi, hj⟩ := ihr hr
      exact ⟨List.mem_append_right _ hi, List.mem_append_right _ hj⟩

private lemma IsSubtree.trans {ι : Type*} {A B C : SPTree ι}
    (h1 : A.IsSubtree B) (h2 : B.IsSubtree C) : A.IsSubtree C := by
  induction h2 with
  | refl => exact h1
  | series_left _ ih => exact .series_left ih
  | series_right _ ih => exact .series_right ih
  | parallel_left _ ih => exact .parallel_left ih
  | parallel_right _ ih => exact .parallel_right ih

private lemma IsSubtree.leaves_subset {ι : Type*} {S T : SPTree ι} (h : S.IsSubtree T) :
    S.leaves ⊆ T.leaves := by
  induction h with
  | refl => exact List.Subset.refl _
  | series_left _ ih => exact List.Subset.trans ih (List.subset_append_left _ _)
  | series_right _ ih => exact List.Subset.trans ih (List.subset_append_right _ _)
  | parallel_left _ ih => exact List.Subset.trans ih (List.subset_append_left _ _)
  | parallel_right _ ih => exact List.Subset.trans ih (List.subset_append_right _ _)

private lemma IsSubtree.leaves_nodup {ι : Type*} {S T : SPTree ι}
    (h : S.IsSubtree T) (hT : T.leaves.Nodup) : S.leaves.Nodup := by
  induction h with
  | refl => exact hT
  | series_left _ ih => exact ih (List.nodup_append.mp hT).1
  | series_right _ ih => exact ih (List.nodup_append.mp hT).2.1
  | parallel_left _ ih => exact ih (List.nodup_append.mp hT).1
  | parallel_right _ ih => exact ih (List.nodup_append.mp hT).2.1

private lemma IsSubtree.prec_iff {ι : Type*} {S T : SPTree ι}
    (h : S.IsSubtree T) (hT : T.leaves.Nodup) {i j : ι}
    (hi : i ∈ S.leaves) (hj : j ∈ S.leaves) : T.prec i j ↔ S.prec i j := by
  induction h with
  | refl => rfl
  | series_left hsub ih =>
    obtain ⟨hl, _, hdisj⟩ := List.nodup_append.mp hT
    have hj_l : j ∈ _ := IsSubtree.leaves_subset hsub hj
    have hj_not_r : j ∉ _ := fun hr => hdisj j hj_l j hr rfl
    rw [ ← ih hl ]
    simp only [SPTree.prec]
    constructor
    · rintro (h | h | ⟨_, h⟩)
      · exact h
      · exact absurd (prec_mem_leaves _ h).2 hj_not_r
      · exact absurd h hj_not_r
    · intro h
      exact Or.inl h
  | series_right hsub ih =>
    obtain ⟨_, hr, hdisj⟩ := List.nodup_append.mp hT
    have hi_r : i ∈ _ := IsSubtree.leaves_subset hsub hi
    have hi_not_l : i ∉ _ := fun hl => hdisj i hl i hi_r rfl
    rw [ ← ih hr ]
    simp only [SPTree.prec]
    constructor
    · rintro (h | h | ⟨h, _⟩)
      · exact absurd (prec_mem_leaves _ h).1 hi_not_l
      · exact h
      · exact absurd h hi_not_l
    · intro h
      exact Or.inr (Or.inl h)
  | parallel_left hsub ih =>
    obtain ⟨hl, _, hdisj⟩ := List.nodup_append.mp hT
    have hj_l : j ∈ _ := IsSubtree.leaves_subset hsub hj
    have hj_not_r : j ∉ _ := fun hr => hdisj j hj_l j hr rfl
    rw [ ← ih hl ]
    simp only [SPTree.prec]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd (prec_mem_leaves _ h).2 hj_not_r
    · intro h
      exact Or.inl h
  | parallel_right hsub ih =>
    obtain ⟨_, hr, hdisj⟩ := List.nodup_append.mp hT
    have hi_r : i ∈ _ := IsSubtree.leaves_subset hsub hi
    have hi_not_l : i ∉ _ := fun hl => hdisj i hl i hi_r rfl
    rw [ ← ih hr ]
    simp only [SPTree.prec]
    constructor
    · rintro (h | h)
      · exact absurd (prec_mem_leaves _ h).1 hi_not_l
      · exact h
    · intro h
      exact Or.inr h

private lemma represents_leaf {ι : Type*} [DecidableEq ι] (G : ι → ι → Prop)
    (p w : ι → ℝ) (j : ι) : Represents G p w ({j} : Finset ι) [[j]] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    refine ⟨List.cons_ne_nil j [], List.nodup_singleton j, ?_⟩
    intro q hq hqne hqne'
    rcases q with _ | ⟨a, q'⟩
    · exact absurd rfl hqne
    · rcases hq with ⟨t, ht⟩
      simp only [List.cons_append, List.cons.injEq, List.append_eq_nil_iff] at ht
      rcases ht with ⟨rfl, rfl, _⟩
      exact absurd rfl hqne'
  · simp
  · intro x
    simp
  · intro L hL _
    rw [List.perm_singleton] at hL
    subst hL
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    refine ⟨⟨⟨List.nodup_singleton j, by simp⟩, List.pairwise_singleton _ j⟩, ?_⟩
    intro l' hl'
    have h1 : l'.Nodup := hl'.1.1
    have h2 : ∀ x, x ∈ l' ↔ x = j := by
      intro x
      simpa using hl'.1.2 x
    have hl'_eq : l' = [j] := by
      rcases l' with _ | ⟨a, _ | ⟨b, tl⟩⟩
      · exfalso
        exact List.not_mem_nil ((h2 j).mpr rfl)
      · rw [List.cons.injEq]
        exact ⟨(h2 a).mp (List.mem_singleton_self a), rfl⟩
      · exfalso
        have ha : a = j := (h2 a).mp List.mem_cons_self
        have hb : b = j := (h2 b).mp (List.mem_cons_of_mem a List.mem_cons_self)
        have hnd : a ∉ b :: tl := (List.nodup_cons.mp h1).1
        exact hnd (by rw [ha, hb]; exact List.mem_cons_self)
    subst hl'_eq
    exact le_rfl

private lemma run_represents {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (T : SPTree ι) (hT : T.leaves.Nodup) (hTN : ∀ j, j ∈ T.leaves ↔ j ∈ N)
    (hTG : ∀ i ∈ N, ∀ j ∈ N, Relation.TransGen G i j ↔ T.prec i j)
    {S : SPTree ι} {F : List (List ι)} (hrun : Run p w S F) (hsub : S.IsSubtree T) :
    Represents G p w S.leaves.toFinset F := by
  induction hrun with
  | leaf j =>
    simpa [SPTree.leaves] using represents_leaf G p w j
  | @parallel l r F₁ F₂ hrun₁ hrun₂ ih₁ ih₂ =>
    have hsub_l : l.IsSubtree T := IsSubtree.trans (.parallel_left (.refl l)) hsub
    have hsub_r : r.IsSubtree T := IsSubtree.trans (.parallel_right (.refl r)) hsub
    have hnd : (l.leaves ++ r.leaves).Nodup := IsSubtree.leaves_nodup hsub hT
    obtain ⟨_, _, hdisj_list⟩ := List.nodup_append.mp hnd
    have hdisj : Disjoint l.leaves.toFinset r.leaves.toFinset := by
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      exact hdisj_list x (List.mem_toFinset.mp hx₁) x (List.mem_toFinset.mp hx₂) rfl
    have hM₁ : IsModule G N l.leaves.toFinset :=
      subtree_isModule N G hGN hacyc T hT hTN hTG l hsub_l
    have hM₂ : IsModule G N r.leaves.toFinset :=
      subtree_isModule N G hGN hacyc T hT hTN hTG r hsub_r
    have hM : IsModule G N (l.leaves.toFinset ∪ r.leaves.toFinset) := by
      rw [← List.toFinset_append]
      exact subtree_isModule N G hGN hacyc T hT hTN hTG (.parallel l r) hsub
    have hunc : ∀ i ∈ l.leaves.toFinset, ∀ j ∈ r.leaves.toFinset,
        ¬ Relation.TransGen G i j ∧ ¬ Relation.TransGen G j i := by
      intro i hi j hj
      have hi_l : i ∈ l.leaves := List.mem_toFinset.mp hi
      have hj_r : j ∈ r.leaves := List.mem_toFinset.mp hj
      have hi_S : i ∈ (SPTree.parallel l r).leaves := List.mem_append_left _ hi_l
      have hj_S : j ∈ (SPTree.parallel l r).leaves := List.mem_append_right _ hj_r
      have hi_N : i ∈ N := (hTN i).mp (IsSubtree.leaves_subset hsub hi_S)
      have hj_N : j ∈ N := (hTN j).mp (IsSubtree.leaves_subset hsub hj_S)
      rw [hTG i hi_N j hj_N, hTG j hj_N i hi_N,
          IsSubtree.prec_iff hsub hT hi_S hj_S,
          IsSubtree.prec_iff hsub hT hj_S hi_S]
      simp only [SPTree.prec]
      constructor
      · rintro (h | h)
        · exact hdisj_list j (prec_mem_leaves l h).2 j hj_r rfl
        · exact hdisj_list i hi_l i (prec_mem_leaves r h).1 rfl
      · rintro (h | h)
        · exact hdisj_list j (prec_mem_leaves l h).1 j hj_r rfl
        · exact hdisj_list i hi_l i (prec_mem_leaves r h).2 rfl
    simpa [SPTree.leaves, List.toFinset_append] using
      parallel_composition N G hGN hacyc p w hp l.leaves.toFinset r.leaves.toFinset hdisj
        hM₁ hM₂ hM hunc F₁ F₂ (ih₁ hsub_l) (ih₂ hsub_r)
  | @series l r F₁ F₂ F hrun₁ hrun₂ hmerge ih₁ ih₂ =>
    have hsub_l : l.IsSubtree T := IsSubtree.trans (.series_left (.refl l)) hsub
    have hsub_r : r.IsSubtree T := IsSubtree.trans (.series_right (.refl r)) hsub
    have hnd : (l.leaves ++ r.leaves).Nodup := IsSubtree.leaves_nodup hsub hT
    obtain ⟨_, _, hdisj_list⟩ := List.nodup_append.mp hnd
    have hdisj : Disjoint l.leaves.toFinset r.leaves.toFinset := by
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      exact hdisj_list x (List.mem_toFinset.mp hx₁) x (List.mem_toFinset.mp hx₂) rfl
    have hM₁ : IsModule G N l.leaves.toFinset :=
      subtree_isModule N G hGN hacyc T hT hTN hTG l hsub_l
    have hM₂ : IsModule G N r.leaves.toFinset :=
      subtree_isModule N G hGN hacyc T hT hTN hTG r hsub_r
    have hM : IsModule G N (l.leaves.toFinset ∪ r.leaves.toFinset) := by
      rw [← List.toFinset_append]
      exact subtree_isModule N G hGN hacyc T hT hTN hTG (.series l r) hsub
    have hser : ∀ i ∈ l.leaves.toFinset, ∀ j ∈ r.leaves.toFinset, Relation.TransGen G i j := by
      intro i hi j hj
      have hi_l : i ∈ l.leaves := List.mem_toFinset.mp hi
      have hj_r : j ∈ r.leaves := List.mem_toFinset.mp hj
      have hi_S : i ∈ (SPTree.series l r).leaves := List.mem_append_left _ hi_l
      have hj_S : j ∈ (SPTree.series l r).leaves := List.mem_append_right _ hj_r
      have hi_N : i ∈ N := (hTN i).mp (IsSubtree.leaves_subset hsub hi_S)
      have hj_N : j ∈ N := (hTN j).mp (IsSubtree.leaves_subset hsub hj_S)
      rw [hTG i hi_N j hj_N, IsSubtree.prec_iff hsub hT hi_S hj_S]
      exact Or.inr (Or.inr ⟨hi_l, hj_r⟩)
    simpa [SPTree.leaves, List.toFinset_append] using
      series_composition_procedure N G hGN hacyc p w hp l.leaves.toFinset r.leaves.toFinset hdisj
        hM₁ hM₂ hM hser F₁ F₂ (ih₁ hsub_l) (ih₂ hsub_r) F hmerge

theorem solution {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (T : SPTree ι) (hT : T.leaves.Nodup) (hTN : ∀ j, j ∈ T.leaves ↔ j ∈ N)
    (hTG : ∀ i ∈ N, ∀ j ∈ N, Relation.TransGen G i j ↔ T.prec i j)
    (F : List (List ι)) (hrun : Run p w T F)
    (L : List (List ι)) (hL : L.Perm F) (hord : IsRatioOrder p w L) :
    SingleMachinePrec.Biclique.IsOptimalSchedule G p w N L.flatten := by
  have hrep : Represents G p w T.leaves.toFinset F :=
    run_represents N G hGN hacyc p w hp T hT hTN hTG hrun (.refl T)
  have hTN_eq : T.leaves.toFinset = N := by
    ext j
    simp [hTN]
  rw [hTN_eq] at hrep
  exact hrep.2.2.2 L hL hord
