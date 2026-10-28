-- Prove2me | solution 1 for LawlerWCT.SeriesPar.series_composition_procedure
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T10:32:41.710798+00:00
-- url     : https://prove2.me/submissions/7599255c-dc85-4bd2-b5c6-db971771dd87

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
import Mathlib.Tactic.Ring
import Definitions.Def_LawlerWCT_SeriesPar_Model
import Theorems.Thm_LawlerWCT_SeriesPar_series_composition_union

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

private lemma split_perm_of_ratio_lt {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    {P₁ P₂ L : List (List ι)}
    (hL : L.Perm (P₁ ++ P₂)) (hord : IsRatioOrder p w L)
    (hratio : ∀ c ∈ P₁, ∀ d ∈ P₂, crho p w d < crho p w c) :
    ∃ L₁ L₂ : List (List ι),
      L = L₁ ++ L₂ ∧ L₁.Perm P₁ ∧ L₂.Perm P₂ ∧
      IsRatioOrder p w L₁ ∧ IsRatioOrder p w L₂ := by
  have hL_pair : L.Pairwise (fun a b => decide (b ∈ P₁) = true → decide (a ∈ P₁) = true) := by
    refine List.Pairwise.imp_of_mem ?_ hord
    intro a b ha _ hab hbP₁
    rw [decide_eq_true_eq] at hbP₁ ⊢
    by_contra haP₁
    have ha_mem : a ∈ P₁ ++ P₂ := hL.subset ha
    have haP₂ : a ∈ P₂ := (List.mem_append.mp ha_mem).resolve_left haP₁
    exact not_lt_of_ge hab (hratio b hbP₁ a haP₂)
  let L₁ := L.filter (fun c => decide (c ∈ P₁))
  let L₂ := L.filter (fun c => !decide (c ∈ P₁))
  have hL_eq : L = L₁ ++ L₂ := eq_filter_append_filter_not (fun c => decide (c ∈ P₁)) hL_pair
  have hP_disj : ∀ c ∈ P₁, c ∉ P₂ := by
    intro c hc₁ hc₂
    exact lt_irrefl _ (hratio c hc₁ c hc₂)
  have hP₁_filt : (P₁ ++ P₂).filter (fun c => decide (c ∈ P₁)) = P₁ := by
    rw [List.filter_append, List.filter_eq_self.mpr (fun c hc => decide_eq_true hc),
        List.filter_eq_nil_iff.mpr (fun c hc => by
          simp [show c ∉ P₁ from fun hc₁ => hP_disj c hc₁ hc]),
        List.append_nil]
  have hP₂_filt : (P₁ ++ P₂).filter (fun c => !decide (c ∈ P₁)) = P₂ := by
    rw [List.filter_append,
        List.filter_eq_nil_iff.mpr (fun c hc => by simp [hc]),
        List.filter_eq_self.mpr (fun c hc => by
          simp [show c ∉ P₁ from fun hc₁ => hP_disj c hc₁ hc]),
        List.nil_append]
  have hL₁_perm : L₁.Perm P₁ := by
    have hp := hL.filter (fun c => decide (c ∈ P₁))
    rwa [hP₁_filt] at hp
  have hL₂_perm : L₂.Perm P₂ := by
    have hp := hL.filter (fun c => !decide (c ∈ P₁))
    rwa [hP₂_filt] at hp
  have hord' := hord
  rw [hL_eq] at hord'
  exact ⟨L₁, L₂, hL_eq, hL₁_perm, hL₂_perm,
    (List.pairwise_append.mp hord').1, (List.pairwise_append.mp hord').2.1⟩

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

private lemma series_optimal_of_sub_optimal {ι : Type*} [DecidableEq ι]
    (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) {M₁ M₂ : Finset ι} (hdisj : Disjoint M₁ M₂)
    (hM : IsModule G N (M₁ ∪ M₂))
    (hser : ∀ i ∈ M₁, ∀ j ∈ M₂, Relation.TransGen G i j)
    {σ₁ σ₂ : List ι}
    (hσ₁ : SingleMachinePrec.Biclique.IsOptimalSchedule G p w M₁ σ₁)
    (hσ₂ : SingleMachinePrec.Biclique.IsOptimalSchedule G p w M₂ σ₂) :
    SingleMachinePrec.Biclique.IsOptimalSchedule G p w (M₁ ∪ M₂) (σ₁ ++ σ₂) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
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
    have hperm₁ : σ₁.Perm l₁' := by
      rw [List.perm_ext_iff_of_nodup hσ₁.1.1.1 hl₁'_feas.1.1]
      intro x
      rw [hσ₁.1.1.2, hl₁'_feas.1.2]
    have hpsum_eq : (σ₁.map p).sum = (l₁'.map p).sum := (hperm₁.map p).sum_eq
    have hle₁ := hσ₁.2 l₁' hl₁'_feas
    have hle₂ := hσ₂.2 l₂' hl₂'_feas
    rw [hl'_eq,
        weightedCompletion_append p w hdisj hσ₁.1.1.2,
        weightedCompletion_append p w hdisj hl₁'_feas.1.2,
        hpsum_eq]
    linarith

private lemma map_p_sum_pos {ι : Type*} (p : ι → ℝ) {l : List ι}
    (hne : l ≠ []) (hp : ∀ j ∈ l, 0 < p j) : 0 < (l.map p).sum := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a as _ =>
    rw [List.map_cons, List.sum_cons]
    have ha : 0 < p a := hp a List.mem_cons_self
    have has : 0 ≤ (as.map p).sum :=
      List.sum_nonneg (by
        intro x hx
        rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
        exact le_of_lt (hp j (List.mem_cons_of_mem a hj)))
    linarith

private lemma prefix_append_cases {α : Type*} :
    ∀ {c₁ c₂ q : List α}, q <+: c₁ ++ c₂ →
      q <+: c₁ ∨ ∃ q₂, q = c₁ ++ q₂ ∧ q₂ <+: c₂ ∧ q₂ ≠ []
  | [], c₂, q, h => by
    by_cases hq : q = []
    · subst hq; exact Or.inl List.nil_prefix
    · exact Or.inr ⟨q, by simp, by simpa using h, hq⟩
  | a :: c₁, _, [], _ => Or.inl List.nil_prefix
  | a :: c₁, c₂, b :: q, h => by
    rcases h with ⟨t, ht⟩
    simp only [List.cons_append, List.cons.injEq] at ht
    rcases ht with ⟨rfl, ht⟩
    rcases prefix_append_cases ⟨t, ht⟩ with ⟨t', ht'⟩ | ⟨q₂, rfl, hq₂, hq₂_ne⟩
    · exact Or.inl ⟨t', by simp [ht']⟩
    · exact Or.inr ⟨q₂, rfl, hq₂, hq₂_ne⟩

private lemma isComposite_append {ι : Type*} (p w : ι → ℝ) {c₁ c₂ : List ι}
    (hc₁ : IsComposite p w c₁) (hc₂ : IsComposite p w c₂)
    (hnd : (c₁ ++ c₂).Nodup)
    (hp₁ : ∀ j ∈ c₁, 0 < p j) (hp₂ : ∀ j ∈ c₂, 0 < p j)
    (hrho : crho p w c₁ ≤ crho p w c₂) :
    IsComposite p w (c₁ ++ c₂) := by
  refine ⟨List.append_ne_nil_of_left_ne_nil hc₁.1 c₂, hnd, ?_⟩
  intro q hq_pref hq_ne hq_ne_all
  let W₁ : ℝ := (c₁.map w).sum
  let P₁ : ℝ := (c₁.map p).sum
  have hP₁ : 0 < P₁ := map_p_sum_pos p hc₁.1 hp₁
  rcases prefix_append_cases hq_pref with hq₁ | ⟨q₂, rfl, hq₂, hq₂_ne⟩
  · have hq_le_c₁ : crho p w q ≤ crho p w c₁ := by
      by_cases hqc₁ : q = c₁
      · subst hqc₁; exact le_rfl
      · exact hc₁.2.2 q hq₁ hq_ne hqc₁
    refine le_trans hq_le_c₁ ?_
    let W₂ : ℝ := (c₂.map w).sum
    let P₂ : ℝ := (c₂.map p).sum
    have hP₂ : 0 < P₂ := map_p_sum_pos p hc₂.1 hp₂
    have hcross : W₁ * P₂ ≤ W₂ * P₁ := by
      unfold crho at hrho
      exact (div_le_div_iff₀ hP₁ hP₂).mp hrho
    unfold crho
    simp only [List.map_append, List.sum_append]
    change W₁ / P₁ ≤ (W₁ + W₂) / (P₁ + P₂)
    rw [div_le_div_iff₀ hP₁ (add_pos hP₁ hP₂)]
    linarith
  · have hq₂_ne_c₂ : q₂ ≠ c₂ := fun h => hq_ne_all (by rw [h])
    obtain ⟨r₂, hr₂⟩ := hq₂
    let W₂ : ℝ := (q₂.map w).sum
    let P₂ : ℝ := (q₂.map p).sum
    let W₃ : ℝ := (r₂.map w).sum
    let P₃ : ℝ := (r₂.map p).sum
    have hP₂ : 0 < P₂ := map_p_sum_pos p hq₂_ne
      (fun j hj => hp₂ j (hr₂ ▸ List.mem_append_left _ hj))
    have hP₃ : 0 ≤ P₃ := List.sum_nonneg (by
      intro x hx
      rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
      exact le_of_lt (hp₂ j (hr₂ ▸ List.mem_append_right _ hj)))
    have hP₂₃ : 0 < P₂ + P₃ := by linarith
    have hc₂_w : (c₂.map w).sum = W₂ + W₃ := by
      rw [← hr₂, List.map_append, List.sum_append]
    have hc₂_p : (c₂.map p).sum = P₂ + P₃ := by
      rw [← hr₂, List.map_append, List.sum_append]
    have h1 : W₁ * (P₂ + P₃) ≤ (W₂ + W₃) * P₁ := by
      have hrho' := hrho
      unfold crho at hrho'
      rw [hc₂_w, hc₂_p] at hrho'
      exact (div_le_div_iff₀ hP₁ hP₂₃).mp hrho'
    have h2 : W₂ * (P₂ + P₃) ≤ (W₂ + W₃) * P₂ := by
      have hq₂_c₂ := hc₂.2.2 q₂ ⟨r₂, hr₂⟩ hq₂_ne hq₂_ne_c₂
      unfold crho at hq₂_c₂
      rw [hc₂_w, hc₂_p] at hq₂_c₂
      exact (div_le_div_iff₀ hP₂ hP₂₃).mp hq₂_c₂
    unfold crho
    simp only [List.map_append, List.sum_append, hc₂_w, hc₂_p]
    change (W₁ + W₂) / (P₁ + P₂) ≤ (W₁ + (W₂ + W₃)) / (P₁ + (P₂ + P₃))
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have hid :
        ((W₁ + W₂) * (P₁ + (P₂ + P₃)) - (W₁ + (W₂ + W₃)) * (P₁ + P₂)) * (P₂ + P₃) =
          P₃ * (W₁ * (P₂ + P₃) - (W₂ + W₃) * P₁) +
            (P₁ + P₂ + P₃) * (W₂ * (P₂ + P₃) - (W₂ + W₃) * P₂) := by ring
    have ht1 : P₃ * (W₁ * (P₂ + P₃) - (W₂ + W₃) * P₁) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hP₃ (by linarith)
    have ht2 : (P₁ + P₂ + P₃) * (W₂ * (P₂ + P₃) - (W₂ + W₃) * P₂) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have h_prod :
        ((W₁ + W₂) * (P₁ + (P₂ + P₃)) - (W₁ + (W₂ + W₃)) * (P₁ + P₂)) * (P₂ + P₃) ≤ 0 := by
      linarith
    have h_diff := nonpos_of_mul_nonpos_left h_prod hP₂₃
    linarith

private lemma perm_flatten {α : Type*} {L₁ L₂ : List (List α)} (h : L₁.Perm L₂) :
    L₁.flatten.Perm L₂.flatten := by
  induction h with
  | nil => exact List.Perm.nil
  | cons x _ ih => exact List.Perm.append_left x ih
  | swap x y l =>
    simp only [List.flatten_cons, ← List.append_assoc]
    exact List.Perm.append_right l.flatten List.perm_append_comm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private lemma seriesLoop_represents {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (M₁ M₂ : Finset ι) (hdisj : Disjoint M₁ M₂)
    (hM₁ : IsModule G N M₁) (hM₂ : IsModule G N M₂) (hM : IsModule G N (M₁ ∪ M₂))
    (hser : ∀ i ∈ M₁, ∀ j ∈ M₂, Relation.TransGen G i j)
    (F₁ F₂ : List (List ι)) (h₁ : Represents G p w M₁ F₁) (h₂ : Represents G p w M₂ F₂)
    {A B : List (List ι)} {k : List ι} {F : List (List ι)}
    (hloop : SeriesLoop p w A B k F) :
    ∀ (K₁ K₂ : List (List ι)),
      (A ++ K₁).Perm F₁ →
      (K₂ ++ B).Perm F₂ →
      k = K₁.flatten ++ K₂.flatten →
      IsComposite p w k →
      IsRatioOrder p w K₁ →
      (∀ a ∈ A, ∀ x ∈ K₁, crho p w x ≤ crho p w a) →
      IsRatioOrder p w K₂ →
      (∀ y ∈ K₂, ∀ b ∈ B, crho p w b ≤ crho p w y) →
      Represents G p w (M₁ ∪ M₂) F := by
  have hnd_all : (F₁ ++ F₂).flatten.Nodup := by
    rw [List.flatten_append, List.nodup_append]
    refine ⟨h₁.2.1, h₂.2.1, fun x hx₁ y hx₂ hxy => ?_⟩
    subst hxy
    exact Finset.disjoint_left.mp hdisj ((h₁.2.2.1 x).mp hx₁) ((h₂.2.2.1 x).mp hx₂)
  have hmem_all : ∀ x, x ∈ (F₁ ++ F₂).flatten ↔ x ∈ M₁ ∪ M₂ := by
    intro x
    rw [List.flatten_append, List.mem_append, h₁.2.2.1, h₂.2.2.1, Finset.mem_union]
  induction hloop with
  | @step2_2 A B k i F hi hmin hik _ ih =>
    intro K₁ K₂ hAK₁ hK₂B hk_eq hk_comp hK₁_ord hAK₁_le hK₂_ord hK₂B_le
    have hiF₁ : i ∈ F₁ := hAK₁.subset (List.mem_append_left _ hi)
    have hi_comp : IsComposite p w i := h₁.1 i hiF₁
    have hAK₁' : (A.erase i ++ (i :: K₁)).Perm F₁ := by
      have h1 : (A.erase i ++ (i :: K₁)).Perm ((i :: A.erase i) ++ K₁) := by
        have hswap : (A.erase i ++ [i]).Perm (i :: A.erase i) :=
          List.perm_append_singleton i (A.erase i)
        have h2 := hswap.append_right K₁
        rwa [List.append_assoc] at h2
      exact h1.trans (((List.perm_cons_erase hi).symm.append_right K₁).trans hAK₁)
    have hk'_eq : i ++ k = (i :: K₁).flatten ++ K₂.flatten := by
      rw [hk_eq, List.flatten_cons, List.append_assoc]
    have hik_nd : (i ++ k).Nodup := by
      have hperm_flat : ((A.erase i ++ (i :: K₁)) ++ (K₂ ++ B)).flatten.Perm (F₁ ++ F₂).flatten :=
        perm_flatten (hAK₁'.append hK₂B)
      have hnd' : ((A.erase i ++ (i :: K₁)) ++ (K₂ ++ B)).flatten.Nodup :=
        hperm_flat.nodup_iff.mpr hnd_all
      simp only [List.flatten_append] at hnd'
      rw [hk'_eq, ← List.flatten_append]
      have hnd_mid : ((i :: K₁) ++ K₂).flatten.Nodup := by
        rw [List.flatten_append]
        have hnd₁ := (List.nodup_append.mp hnd').1
        have hnd₂ := (List.nodup_append.mp hnd').2.1
        have hdisj' := (List.nodup_append.mp hnd').2.2
        rw [List.nodup_append] at hnd₁ hnd₂ ⊢
        refine ⟨hnd₁.2.1, hnd₂.1, fun x hx₁ y hx₂ => hdisj' x (List.mem_append_right _ hx₁) y (List.mem_append_left _ hx₂)⟩
      exact hnd_mid
    have hpi : ∀ x ∈ i, 0 < p x := fun x hx =>
      hp x (hM₁.2.1 ((h₁.2.2.1 x).mp (List.mem_flatten.mpr ⟨i, hiF₁, hx⟩)))
    have hpk : ∀ x ∈ k, 0 < p x := by
      intro x hx
      rw [hk_eq, List.mem_append] at hx
      rcases hx with hx₁ | hx₂
      · have hxF₁ : x ∈ F₁.flatten :=
          (perm_flatten hAK₁).subset (by rw [List.flatten_append]; exact List.mem_append_right _ hx₁)
        exact hp x (hM₁.2.1 ((h₁.2.2.1 x).mp hxF₁))
      · have hxF₂ : x ∈ F₂.flatten :=
          (perm_flatten hK₂B).subset (by rw [List.flatten_append]; exact List.mem_append_left _ hx₂)
        exact hp x (hM₂.2.1 ((h₂.2.2.1 x).mp hxF₂))
    have hik_comp : IsComposite p w (i ++ k) :=
      isComposite_append p w hi_comp hk_comp hik_nd hpi hpk hik
    have hK₁'_ord : IsRatioOrder p w (i :: K₁) := by
      unfold IsRatioOrder at hK₁_ord ⊢
      rw [List.pairwise_cons]
      exact ⟨fun x hx => hAK₁_le i hi x hx, hK₁_ord⟩
    have hAK₁'_le : ∀ a ∈ A.erase i, ∀ x ∈ i :: K₁, crho p w x ≤ crho p w a := by
      intro a ha x hx
      have haA : a ∈ A := List.mem_of_mem_erase ha
      rcases List.mem_cons.mp hx with rfl | hxK₁
      · exact hmin a haA
      · exact hAK₁_le a haA x hxK₁
    exact ih (i :: K₁) K₂ hAK₁' hK₂B hk'_eq hik_comp hK₁'_ord hAK₁'_le hK₂_ord hK₂B_le
  | @step3_2 A B k j F _ hj hmax hkj _ ih =>
    intro K₁ K₂ hAK₁ hK₂B hk_eq hk_comp hK₁_ord hAK₁_le hK₂_ord hK₂B_le
    have hjF₂ : j ∈ F₂ := hK₂B.subset (List.mem_append_right _ hj)
    have hj_comp : IsComposite p w j := h₂.1 j hjF₂
    have hK₂B' : ((K₂ ++ [j]) ++ B.erase j).Perm F₂ := by
      have h1 : (K₂ ++ [j]) ++ B.erase j = K₂ ++ (j :: B.erase j) := by simp
      rw [h1]
      exact (List.Perm.append_left K₂ (List.perm_cons_erase hj).symm).trans hK₂B
    have hk'_eq : k ++ j = K₁.flatten ++ (K₂ ++ [j]).flatten := by
      rw [hk_eq, List.flatten_append, List.flatten_singleton, List.append_assoc]
    have hkj_nd : (k ++ j).Nodup := by
      have hperm_flat : ((A ++ K₁) ++ ((K₂ ++ [j]) ++ B.erase j)).flatten.Perm (F₁ ++ F₂).flatten :=
        perm_flatten (hAK₁.append hK₂B')
      have hnd' : ((A ++ K₁) ++ ((K₂ ++ [j]) ++ B.erase j)).flatten.Nodup :=
        hperm_flat.nodup_iff.mpr hnd_all
      rw [List.flatten_append, List.flatten_append (L₁ := A) (L₂ := K₁),
          List.flatten_append (L₁ := K₂ ++ [j]) (L₂ := B.erase j)] at hnd'
      rw [hk'_eq]
      have hnd₁ := (List.nodup_append.mp hnd').1
      have hnd₂ := (List.nodup_append.mp hnd').2.1
      have hdisj' := (List.nodup_append.mp hnd').2.2
      rw [List.nodup_append] at hnd₁ hnd₂ ⊢
      refine ⟨hnd₁.2.1, hnd₂.1, fun x hx₁ y hx₂ =>
        hdisj' x (List.mem_append_right _ hx₁) y (List.mem_append_left _ hx₂)⟩
    have hpk : ∀ x ∈ k, 0 < p x := by
      intro x hx
      rw [hk_eq, List.mem_append] at hx
      rcases hx with hx₁ | hx₂
      · have hxF₁ : x ∈ F₁.flatten :=
          (perm_flatten hAK₁).subset (by rw [List.flatten_append]; exact List.mem_append_right _ hx₁)
        exact hp x (hM₁.2.1 ((h₁.2.2.1 x).mp hxF₁))
      · have hxF₂ : x ∈ F₂.flatten :=
          (perm_flatten hK₂B).subset (by rw [List.flatten_append]; exact List.mem_append_left _ hx₂)
        exact hp x (hM₂.2.1 ((h₂.2.2.1 x).mp hxF₂))
    have hpj : ∀ x ∈ j, 0 < p x := fun x hx =>
      hp x (hM₂.2.1 ((h₂.2.2.1 x).mp (List.mem_flatten.mpr ⟨j, hjF₂, hx⟩)))
    have hkj_comp : IsComposite p w (k ++ j) :=
      isComposite_append p w hk_comp hj_comp hkj_nd hpk hpj hkj
    have hK₂'_ord : IsRatioOrder p w (K₂ ++ [j]) := by
      unfold IsRatioOrder at hK₂_ord ⊢
      rw [List.pairwise_append]
      refine ⟨hK₂_ord, List.pairwise_singleton _ j, fun y hy z hz => ?_⟩
      rw [List.mem_singleton.mp hz]
      exact hK₂B_le y hy j hj
    have hK₂B'_le : ∀ y ∈ K₂ ++ [j], ∀ b ∈ B.erase j, crho p w b ≤ crho p w y := by
      intro y hy b hb
      have hbB : b ∈ B := List.mem_of_mem_erase hb
      rcases List.mem_append.mp hy with hyK₂ | hyj
      · exact hK₂B_le y hyK₂ b hbB
      · rw [List.mem_singleton.mp hyj]
        exact hmax b hbB
    exact ih K₁ (K₂ ++ [j]) hAK₁ hK₂B' hk'_eq hkj_comp hK₁_ord hAK₁_le hK₂'_ord hK₂B'_le
  | @halt A B k hkA hkB =>
    intro K₁ K₂ hAK₁ hK₂B hk_eq hk_comp hK₁_ord hAK₁_le hK₂_ord hK₂B_le
    have hF_perm_flat : (A ++ B ++ [k]).flatten.Perm (F₁ ++ F₂).flatten := by
      have h1 : (A ++ B ++ [k]).Perm (A ++ [k] ++ B) := by
        rw [List.append_assoc, List.append_assoc]
        exact List.Perm.append_left A List.perm_append_comm
      have h2 : (A ++ [k] ++ B).flatten = ((A ++ K₁) ++ (K₂ ++ B)).flatten := by
        simp [hk_eq, List.append_assoc]
      exact (perm_flatten h1).trans (h2 ▸ perm_flatten (hAK₁.append hK₂B))
    refine ⟨?_, hF_perm_flat.nodup_iff.mpr hnd_all,
      fun x => hF_perm_flat.mem_iff.trans (hmem_all x), ?_⟩
    · intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with (hcA | hcB) | rfl
      · exact h₁.1 c (hAK₁.subset (List.mem_append_left _ hcA))
      · exact h₂.1 c (hK₂B.subset (List.mem_append_right _ hcB))
      · exact hk_comp
    · intro L hL hord
      have hL' : L.Perm (A ++ ([k] ++ B)) := by
        have h1 : (A ++ B ++ [k]).Perm (A ++ ([k] ++ B)) := by
          rw [List.append_assoc]
          exact List.Perm.append_left A List.perm_append_comm
        exact hL.trans h1
      have hratio1 : ∀ a ∈ A, ∀ d ∈ [k] ++ B, crho p w d < crho p w a := by
        intro a ha d hd
        rcases List.mem_append.mp hd with hdk | hdB
        · rcases List.mem_singleton.mp hdk with rfl
          exact hkA a ha
        · exact lt_trans (hkB d hdB) (hkA a ha)
      obtain ⟨L_A, L_rest, rfl, hLA_perm, hLrest_perm, hLA_ord, hLrest_ord⟩ :=
        split_perm_of_ratio_lt p w hL' hord hratio1
      have hratio2 : ∀ c ∈ ([k] : List (List ι)), ∀ b ∈ B, crho p w b < crho p w c := by
        intro c hc b hb
        rcases List.mem_singleton.mp hc with rfl
        exact hkB b hb
      obtain ⟨L_k, L_B, hLrest_eq, hLk_perm, hLB_perm, _, hLB_ord⟩ :=
        split_perm_of_ratio_lt p w hLrest_perm hLrest_ord hratio2
      have hLk_eq : L_k = [k] := List.perm_singleton.mp hLk_perm
      rw [hLrest_eq, hLk_eq]
      let L₁ := L_A ++ K₁
      let L₂ := K₂ ++ L_B
      have hL₁_perm : L₁.Perm F₁ := (hLA_perm.append_right K₁).trans hAK₁
      have hL₂_perm : L₂.Perm F₂ := (List.Perm.append_left K₂ hLB_perm).trans hK₂B
      have hL₁_ord : IsRatioOrder p w L₁ := by
        unfold IsRatioOrder at hLA_ord hK₁_ord ⊢
        rw [List.pairwise_append]
        refine ⟨hLA_ord, hK₁_ord, fun a ha x hx => ?_⟩
        exact hAK₁_le a (hLA_perm.subset ha) x hx
      have hL₂_ord : IsRatioOrder p w L₂ := by
        unfold IsRatioOrder at hK₂_ord hLB_ord ⊢
        rw [List.pairwise_append]
        refine ⟨hK₂_ord, hLB_ord, fun y hy b hb => ?_⟩
        exact hK₂B_le y hy b (hLB_perm.subset hb)
      have hσ₁ := h₁.2.2.2 L₁ hL₁_perm hL₁_ord
      have hσ₂ := h₂.2.2.2 L₂ hL₂_perm hL₂_ord
      have hflat_eq : (L_A ++ ([k] ++ L_B)).flatten = L₁.flatten ++ L₂.flatten := by
        simp [L₁, L₂, hk_eq, List.append_assoc]
      rw [hflat_eq]
      exact series_optimal_of_sub_optimal N G hGN hacyc p w hdisj hM hser hσ₁ hσ₂

theorem solution {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (p w : ι → ℝ) (hp : ∀ j ∈ N, 0 < p j)
    (M₁ M₂ : Finset ι) (hdisj : Disjoint M₁ M₂)
    (hM₁ : IsModule G N M₁) (hM₂ : IsModule G N M₂) (hM : IsModule G N (M₁ ∪ M₂))
    (hser : ∀ i ∈ M₁, ∀ j ∈ M₂, Relation.TransGen G i j)
    (F₁ F₂ : List (List ι)) (h₁ : Represents G p w M₁ F₁) (h₂ : Represents G p w M₂ F₂)
    (F : List (List ι)) (hmerge : SeriesMerge p w F₁ F₂ F) :
    Represents G p w (M₁ ∪ M₂) F := by
  cases hmerge with
  | halt hratio =>
    exact series_composition_union N G hGN hacyc p w hp M₁ M₂ hdisj hM₁ hM₂ hM hser F₁ F₂ h₁ h₂ hratio
  | @merge i j F hi hmin hj hmax hij hloop =>
    have hAK₁ : (F₁.erase i ++ [i]).Perm F₁ :=
      (List.perm_append_singleton i (F₁.erase i)).trans (List.perm_cons_erase hi).symm
    have hK₂B : ([j] ++ F₂.erase j).Perm F₂ :=
      (List.perm_cons_erase hj).symm
    have hk_eq : i ++ j = [i].flatten ++ [j].flatten := by simp
    have hij_nd : (i ++ j).Nodup := by
      rw [List.nodup_append]
      have hi_nd : i.Nodup := (h₁.1 i hi).2.1
      have hj_nd : j.Nodup := (h₂.1 j hj).2.1
      refine ⟨hi_nd, hj_nd, fun x hxi y hxj hxy => ?_⟩
      subst hxy
      exact Finset.disjoint_left.mp hdisj
        ((h₁.2.2.1 x).mp (List.mem_flatten.mpr ⟨i, hi, hxi⟩))
        ((h₂.2.2.1 x).mp (List.mem_flatten.mpr ⟨j, hj, hxj⟩))
    have hpi : ∀ x ∈ i, 0 < p x := fun x hx =>
      hp x (hM₁.2.1 ((h₁.2.2.1 x).mp (List.mem_flatten.mpr ⟨i, hi, hx⟩)))
    have hpj : ∀ x ∈ j, 0 < p x := fun x hx =>
      hp x (hM₂.2.1 ((h₂.2.2.1 x).mp (List.mem_flatten.mpr ⟨j, hj, hx⟩)))
    have hij_comp : IsComposite p w (i ++ j) :=
      isComposite_append p w (h₁.1 i hi) (h₂.1 j hj) hij_nd hpi hpj hij
    exact seriesLoop_represents N G hGN hacyc p w hp M₁ M₂ hdisj hM₁ hM₂ hM hser F₁ F₂ h₁ h₂ hloop
      [i] [j] hAK₁ hK₂B hk_eq hij_comp
      (List.pairwise_singleton _ i)
      (fun a ha x hx => by
        rcases List.mem_singleton.mp hx with rfl
        exact hmin a (List.mem_of_mem_erase ha))
      (List.pairwise_singleton _ j)
      (fun y hy b hb => by
        rcases List.mem_singleton.mp hy with rfl
        exact hmax b (List.mem_of_mem_erase hb))
