-- Prove2me | solution 1 for IgnallSchrage.Makespan.node_counts
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:43:37.05227+00:00
-- url     : https://prove2.me/submissions/decdeeaa-b95e-4cfb-86cb-547e28e83bd9

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound
import Definitions.Def_IgnallSchrage_Makespan_Procedure
import Definitions.Def_IgnallSchrage_Makespan_RefinedLowerBound



namespace IgnallSchrage.Makespan

section basic
variable {n : ℕ} (a b c : Fin n → ℝ)

theorem ign_fold_A (L : List (Fin n)) (t : ℝ × ℝ × ℝ) :
    (L.foldl (appendJob a b c) t).1 = t.1 + (L.map a).sum := by
  induction L generalizing t with
  | nil => simp
  | cons x L ih => rw [List.foldl_cons, ih]; simp [appendJob]; ring

theorem ign_fold_B (L : List (Fin n)) (t : ℝ × ℝ × ℝ) :
    t.2.1 + (L.map b).sum ≤ (L.foldl (appendJob a b c) t).2.1 := by
  induction L generalizing t with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons]
    refine le_trans ?_ (ih _)
    simp only [appendJob, List.map_cons, List.sum_cons]
    have := le_max_left t.2.1 (t.1 + a x)
    linarith

theorem ign_fold_C (L : List (Fin n)) (t : ℝ × ℝ × ℝ) :
    t.2.2 + (L.map c).sum ≤ (L.foldl (appendJob a b c) t).2.2 := by
  induction L generalizing t with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons]
    refine le_trans ?_ (ih _)
    simp only [appendJob, List.map_cons, List.sum_cons]
    have := le_max_left t.2.2 (max t.2.1 (t.1 + a x) + b x)
    linarith

theorem ign_fold_B_first (x : Fin n) (L : List (Fin n)) (t : ℝ × ℝ × ℝ) :
    t.1 + a x + ((x :: L).map b).sum ≤ ((x :: L).foldl (appendJob a b c) t).2.1 := by
  rw [List.foldl_cons]
  refine le_trans ?_ (ign_fold_B a b c L _)
  simp only [appendJob, List.map_cons, List.sum_cons]
  have := le_max_right t.2.1 (t.1 + a x)
  linarith

theorem ign_fold_C_first_b (x : Fin n) (L : List (Fin n)) (t : ℝ × ℝ × ℝ) :
    t.2.1 + b x + ((x :: L).map c).sum ≤ ((x :: L).foldl (appendJob a b c) t).2.2 := by
  rw [List.foldl_cons]
  refine le_trans ?_ (ign_fold_C a b c L _)
  simp only [appendJob, List.map_cons, List.sum_cons]
  have := le_max_right t.2.2 (max t.2.1 (t.1 + a x) + b x)
  have := le_max_left t.2.1 (t.1 + a x)
  linarith

theorem ign_fold_C_first_ab (x : Fin n) (L : List (Fin n)) (t : ℝ × ℝ × ℝ) :
    t.1 + (a x + b x) + ((x :: L).map c).sum ≤ ((x :: L).foldl (appendJob a b c) t).2.2 := by
  rw [List.foldl_cons]
  refine le_trans ?_ (ign_fold_C a b c L _)
  simp only [appendJob, List.map_cons, List.sum_cons]
  have := le_max_right t.2.2 (max t.2.1 (t.1 + a x) + b x)
  have := le_max_right t.2.1 (t.1 + a x)
  linarith

/-- last-element facts -/
theorem ign_fold_last (L : List (Fin n)) (l : Fin n) (t : ℝ × ℝ × ℝ) :
    let F := (L ++ [l]).foldl (appendJob a b c) t
    F.1 + b l ≤ F.2.1 ∧ F.2.1 + c l ≤ F.2.2 := by
  intro F
  simp only [F, List.foldl_append, List.foldl_cons, List.foldl_nil, appendJob]
  constructor
  · have := le_max_right (L.foldl (appendJob a b c) t).2.1 ((L.foldl (appendJob a b c) t).1 + a l)
    linarith
  · linarith [le_max_right (L.foldl (appendJob a b c) t).2.2 (max (L.foldl (appendJob a b c) t).2.1 ((L.foldl (appendJob a b c) t).1 + a l) + b l)]

theorem ign_minOver_le (s : Finset (Fin n)) (f : Fin n → ℝ) (i : Fin n) (hi : i ∈ s) :
    minOver s f ≤ f i := by
  unfold minOver
  rw [dif_pos ⟨i, hi⟩]
  exact Finset.inf'_le _ hi

theorem ign_minOver_singleton (l : Fin n) (f : Fin n → ℝ) : minOver {l} f = f l := by
  simp [minOver]

end basic


section main
variable {n : ℕ} (a b c : Fin n → ℝ)

theorem ign_lb_le_list (J R : List (Fin n)) (hR : R ≠ []) (hnd : R.Nodup)
    (hU : unscheduled J = R.toFinset) :
    lowerBound a b c J ≤ (R.foldl (appendJob a b c) (times a b c J)).2.2 := by
  obtain ⟨L, l, rfl⟩ : ∃ L l, R = L ++ [l] :=
    ⟨_, _, (List.dropLast_append_getLast hR).symm⟩
  obtain ⟨x, L', hx⟩ : ∃ x L', L ++ [l] = x :: L' := by
    cases L with
    | nil => exact ⟨l, [], rfl⟩
    | cons y L => exact ⟨y, L ++ [l], rfl⟩
  have hl : l ∈ unscheduled J := by rw [hU]; simp
  have hxm : x ∈ unscheduled J := by rw [hU, hx]; simp
  have sa : ∑ i ∈ unscheduled J, a i = ((L ++ [l]).map a).sum := by
    rw [hU, List.sum_toFinset _ hnd]
  have sb : ∑ i ∈ unscheduled J, b i = ((L ++ [l]).map b).sum := by
    rw [hU, List.sum_toFinset _ hnd]
  have sc : ∑ i ∈ unscheduled J, c i = ((L ++ [l]).map c).sum := by
    rw [hU, List.sum_toFinset _ hnd]
  have hlast := ign_fold_last a b c L l (times a b c J)
  have hA := ign_fold_A a b c (L ++ [l]) (times a b c J)
  have hB := ign_fold_B a b c (L ++ [l]) (times a b c J)
  have hC := ign_fold_C a b c (L ++ [l]) (times a b c J)
  have m1 := ign_minOver_le (unscheduled J) (fun i => b i + c i) l hl
  have m2 := ign_minOver_le (unscheduled J) c l hl
  unfold lowerBound
  simp only [sa, sb, sc]
  refine max_le ?_ (max_le ?_ ?_)
  · linarith [hlast.1, hlast.2]
  · linarith [hlast.2]
  · exact hC

theorem ign_refined_le_list (J R : List (Fin n)) (hR : R ≠ []) (hnd : R.Nodup)
    (hU : unscheduled J = R.toFinset) :
    refinedLowerBound a b c J ≤ (R.foldl (appendJob a b c) (times a b c J)).2.2 := by
  obtain ⟨L, l, rfl⟩ : ∃ L l, R = L ++ [l] :=
    ⟨_, _, (List.dropLast_append_getLast hR).symm⟩
  obtain ⟨x, L', hx⟩ : ∃ x L', L ++ [l] = x :: L' := by
    cases L with
    | nil => exact ⟨l, [], rfl⟩
    | cons y L => exact ⟨y, L ++ [l], rfl⟩
  have hl : l ∈ unscheduled J := by rw [hU]; simp
  have sa : ∑ i ∈ unscheduled J, a i = ((L ++ [l]).map a).sum := by
    rw [hU, List.sum_toFinset _ hnd]
  have sb : ∑ i ∈ unscheduled J, b i = ((L ++ [l]).map b).sum := by
    rw [hU, List.sum_toFinset _ hnd]
  have sc : ∑ i ∈ unscheduled J, c i = ((L ++ [l]).map c).sum := by
    rw [hU, List.sum_toFinset _ hnd]
  have hlast := ign_fold_last a b c L l (times a b c J)
  have hA := ign_fold_A a b c (L ++ [l]) (times a b c J)
  have hB := ign_fold_B a b c (L ++ [l]) (times a b c J)
  have hC := ign_fold_C a b c (L ++ [l]) (times a b c J)
  have hxm : x ∈ unscheduled J := by rw [hU, hx]; simp
  have hBf := ign_fold_B_first a b c x L' (times a b c J)
  have hCb := ign_fold_C_first_b a b c x L' (times a b c J)
  have hCab := ign_fold_C_first_ab a b c x L' (times a b c J)
  have m1 := ign_minOver_le (unscheduled J) (fun i => b i + c i) l hl
  have m2 := ign_minOver_le (unscheduled J) c l hl
  have ma := ign_minOver_le (unscheduled J) a x hxm
  have mb := ign_minOver_le (unscheduled J) b x hxm
  have mab := ign_minOver_le (unscheduled J) (fun i => a i + b i) x hxm
  rw [← hx] at hBf hCb hCab
  have key : ∀ p q r s X : ℝ, p + s ≤ X → q + s ≤ X → r + s ≤ X → max p (max q r) + s ≤ X := by
    intro p q r s X h1 h2 h3
    have : max p (max q r) ≤ X - s := max_le (by linarith) (max_le (by linarith) (by linarith))
    linarith
  have key2 : ∀ p q s X : ℝ, p + s ≤ X → q + s ≤ X → max p q + s ≤ X := by
    intro p q s X h1 h2
    have : max p q ≤ X - s := max_le (by linarith) (by linarith)
    linarith
  unfold refinedLowerBound
  simp only [sa, sb, sc]
  refine max_le ?_ (max_le ?_ ?_)
  · linarith [hlast.1, hlast.2]
  · have : max (times a b c J).2.1 ((times a b c J).1 + minOver (unscheduled J) a) +
        ((L ++ [l]).map b).sum + minOver (unscheduled J) c =
        max (times a b c J).2.1 ((times a b c J).1 + minOver (unscheduled J) a) +
        (((L ++ [l]).map b).sum + minOver (unscheduled J) c) := by ring
    rw [this]
    have h := key2 (times a b c J).2.1 ((times a b c J).1 + minOver (unscheduled J) a)
      (((L ++ [l]).map b).sum + minOver (unscheduled J) c)
      ((L ++ [l]).foldl (appendJob a b c) (times a b c J)).2.2
      (by linarith [hlast.2]) (by linarith [hlast.2])
    exact h
  · exact key _ _ _ _ _ (by linarith) (by linarith) (by linarith)


theorem ign_asap_eq (σ : Equiv.Perm (Fin n)) (m : ℕ) (hm : m ≤ n) :
    JohnsonFlowShop.ThreeStage.asapDone a b c σ m =
      ((List.ofFn σ).take m).foldl (appendJob a b c) (0, 0, 0) := by
  induction m with
  | zero => simp [JohnsonFlowShop.ThreeStage.asapDone]
  | succ m ih =>
    have h : m < n := hm
    rw [JohnsonFlowShop.ThreeStage.asapDone, dif_pos h, ih (by omega), List.take_add_one]
    have : (List.ofFn σ)[m]? = some (σ ⟨m, h⟩) := by simp [h]
    rw [this]
    simp [appendJob]

theorem ign_makespan_eq (σ : Equiv.Perm (Fin n)) :
    makespan a b c σ = ((List.ofFn σ).foldl (appendJob a b c) (0, 0, 0)).2.2 := by
  unfold makespan
  rw [ign_asap_eq a b c σ n le_rfl]
  rw [List.take_of_length_le (by simp)]

theorem ign_extend (J : List (Fin n)) (σ : Equiv.Perm (Fin n)) (hσ : BeginsWith σ J) :
    ∃ R, List.ofFn σ = J ++ R ∧ R.Nodup ∧ unscheduled J = R.toFinset ∧
      makespan a b c σ = (R.foldl (appendJob a b c) (times a b c J)).2.2 := by
  obtain ⟨R, hR⟩ := hσ
  have hnd : (List.ofFn σ).Nodup := List.nodup_ofFn.mpr σ.injective
  rw [← hR] at hnd
  refine ⟨R, hR.symm, (List.nodup_append.mp hnd).2.1, ?_, ?_⟩
  · ext j
    simp only [unscheduled, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    have hj : j ∈ J ++ R := by rw [hR]; exact List.mem_ofFn.mpr ⟨σ.symm j, by simp⟩
    have hd := List.disjoint_of_nodup_append hnd
    rw [List.mem_append] at hj
    constructor
    · intro h; tauto
    · intro h hJ; exact hd hJ h
  · rw [ign_makespan_eq, ← hR, times, List.foldl_append]

theorem lowerBound_le_makespan_core (J : List (Fin n)) (hJ : J.length < n) (σ : Equiv.Perm (Fin n))
    (hσ : BeginsWith σ J) : lowerBound a b c J ≤ makespan a b c σ := by
  obtain ⟨R, h1, h2, h3, h4⟩ := ign_extend a b c J σ hσ
  rw [h4]
  refine ign_lb_le_list a b c J R ?_ h2 h3
  rintro rfl
  have := congrArg List.length h1
  simp at this
  omega

theorem refined_le_makespan_core (J : List (Fin n)) (hJ : J.length < n) (σ : Equiv.Perm (Fin n))
    (hσ : BeginsWith σ J) : refinedLowerBound a b c J ≤ makespan a b c σ := by
  obtain ⟨R, h1, h2, h3, h4⟩ := ign_extend a b c J σ hσ
  rw [h4]
  refine ign_refined_le_list a b c J R ?_ h2 h3
  rintro rfl
  have := congrArg List.length h1
  simp at this
  omega

theorem lowerBound_eq_makespan_core (J : List (Fin n)) (hJ : J.length + 1 = n) (σ : Equiv.Perm (Fin n))
    (hσ : BeginsWith σ J) : lowerBound a b c J = makespan a b c σ := by
  obtain ⟨R, h1, h2, h3, h4⟩ := ign_extend a b c J σ hσ
  have hlen : R.length = 1 := by
    have := congrArg List.length h1
    simp at this
    omega
  obtain ⟨l, rfl⟩ := List.length_eq_one_iff.mp hlen
  rw [h4]
  apply le_antisymm
  · exact ign_lb_le_list a b c J [l] (by simp) h2 h3
  · have hU : unscheduled J = {l} := by rw [h3]; simp
    unfold lowerBound
    simp only [hU, Finset.sum_singleton, ign_minOver_singleton, List.foldl_cons, List.foldl_nil,
      appendJob]
    simp only [max_def]
    split_ifs <;> linarith

theorem dominance_core (J I : List (Fin n)) (hJI : J.Perm I)
    (hB : (times a b c J).2.1 ≤ (times a b c I).2.1)
    (hC : (times a b c J).2.2 ≤ (times a b c I).2.2) :
    lowerBound a b c J ≤ lowerBound a b c I := by
  have hU : unscheduled J = unscheduled I := by
    ext j; simp [unscheduled, hJI.mem_iff]
  have hA : (times a b c J).1 = (times a b c I).1 := by
    unfold times
    rw [ign_fold_A, ign_fold_A, hJI.map a |>.sum_eq]
  unfold lowerBound
  simp only [hU, hA]
  gcongr

end main

section proc
variable {n : ℕ} (LB : List (Fin n) → ℝ)

theorem ign_insert_perm (x : List (Fin n)) (L : List (List (Fin n))) :
    (insertNode LB x L).Perm (x :: L) := by
  induction L with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    unfold insertNode
    split_ifs with h
    · exact List.Perm.refl _
    · exact (ih.cons y).trans (List.Perm.swap x y ys)

theorem ign_insert_sorted (x : List (Fin n)) (L : List (List (Fin n)))
    (hL : L.Pairwise (fun p q => LB p ≤ LB q)) :
    (insertNode LB x L).Pairwise (fun p q => LB p ≤ LB q) := by
  induction L with
  | nil => simp [insertNode]
  | cons y ys ih =>
    unfold insertNode
    split_ifs with h
    · rw [List.pairwise_cons]
      refine ⟨?_, hL⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h
      · exact h.trans ((List.pairwise_cons.mp hL).1 b hb)
    · rw [List.pairwise_cons]
      have hy := List.pairwise_cons.mp hL
      refine ⟨?_, ih hy.2⟩
      intro b hb
      have := (ign_insert_perm LB x ys).mem_iff.mp hb
      rcases List.mem_cons.mp this with rfl | hb
      · exact (not_le.mp h).le
      · exact hy.1 b hb

theorem ign_foldl_perm (C L : List (List (Fin n))) :
    (C.foldl (fun L x => insertNode LB x L) L).Perm (C ++ L) := by
  induction C generalizing L with
  | nil => exact List.Perm.refl _
  | cons x C ih =>
    rw [List.foldl_cons]
    refine (ih _).trans ?_
    refine ((ign_insert_perm LB x L).append_left C).trans ?_
    exact List.perm_middle

theorem ign_foldl_sorted (C L : List (List (Fin n)))
    (hL : L.Pairwise (fun p q => LB p ≤ LB q)) :
    (C.foldl (fun L x => insertNode LB x L) L).Pairwise (fun p q => LB p ≤ LB q) := by
  induction C generalizing L with
  | nil => exact hL
  | cons x C ih =>
    rw [List.foldl_cons]
    exact ih _ (ign_insert_sorted LB x L hL)

theorem ign_step_cons (P : List (Fin n)) (rest : List (List (Fin n))) (h : ¬ IsTerminal P) :
    step LB (P :: rest) = (children P).foldl (fun L x => insertNode LB x L) rest := by
  simp [step, h]

theorem ign_step_term (P : List (Fin n)) (rest : List (List (Fin n))) (h : IsTerminal P) :
    step LB (P :: rest) = P :: rest := by
  simp [step, h]

theorem ign_mem_children (P Q : List (Fin n)) :
    Q ∈ children P ↔ ∃ j, j ∉ P ∧ Q = P ++ [j] := by
  unfold children
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

theorem ign_children_length (P : List (Fin n)) (hP : P.Nodup) :
    (children P).length = n - P.length := by
  unfold children
  rw [List.length_map]
  have h1 : ((List.finRange n).filter (fun j => decide (j ∉ P))).Nodup :=
    (List.nodup_finRange n).filter _
  have h2 : ((List.finRange n).filter (fun j => decide (j ∉ P))).toFinset =
      (P.toFinset)ᶜ := by
    ext j; simp
  rw [← List.toFinset_card_of_nodup h1, h2, Finset.card_compl, List.toFinset_card_of_nodup hP]
  simp


def IgnGood (LB : List (Fin n) → ℝ) (L : List (List (Fin n))) : Prop :=
  (∀ Q ∈ L, Q.Nodup ∧ Q.length < n) ∧ L.Pairwise (fun p q => LB p ≤ LB q) ∧
  (∀ σ : Equiv.Perm (Fin n), ∃ Q ∈ L, BeginsWith σ Q) ∧
  (L.map (fun Q => (n - Q.length).factorial)).sum = n.factorial

theorem ign_begins_extend (σ : Equiv.Perm (Fin n)) (P : List (Fin n)) (hσ : BeginsWith σ P)
    (hP : P.length < n) : ∃ j, j ∉ P ∧ BeginsWith σ (P ++ [j]) := by
  obtain ⟨R, hR⟩ := hσ
  have hnd : (List.ofFn σ).Nodup := List.nodup_ofFn.mpr σ.injective
  rw [← hR] at hnd
  have hlen := congrArg List.length hR
  simp only [List.length_append, List.length_ofFn] at hlen
  obtain ⟨x, R', rfl⟩ : ∃ x R', R = x :: R' := by
    cases R with
    | nil => simp at hlen; omega
    | cons x R' => exact ⟨x, R', rfl⟩
  refine ⟨x, ?_, R', ?_⟩
  · have := (List.nodup_append.mp hnd).2.2
    intro hx
    exact this x hx x (by simp) rfl
  · rw [← hR]; simp

theorem ign_step_good (L : List (List (Fin n))) (hn : 1 ≤ n) (h : IgnGood LB L) :
    IgnGood LB (step LB L) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases L with
  | nil =>
    obtain ⟨Q, hQ, _⟩ := h3 1
    simp at hQ
  | cons P rest =>
    by_cases ht : IsTerminal P
    · rw [ign_step_term LB P rest ht]; exact ⟨h1, h2, h3, h4⟩
    · rw [ign_step_cons LB P rest ht]
      have hP := h1 P (by simp)
      have hperm := ign_foldl_perm LB (children P) rest
      have hr := (List.pairwise_cons.mp h2).2
      have hP1 : P.length + 1 < n := by
        have := hP.2; unfold IsTerminal at ht; omega
      refine ⟨?_, ign_foldl_sorted LB _ _ hr, ?_, ?_⟩
      · intro Q hQ
        have := hperm.mem_iff.mp hQ
        rcases List.mem_append.mp this with hQ | hQ
        · obtain ⟨j, hj, rfl⟩ := (ign_mem_children P Q).mp hQ
          refine ⟨List.nodup_append.mpr ⟨hP.1, List.nodup_singleton _, ?_⟩, ?_⟩
          · intro x hx y hy; simp at hy; subst hy; intro e; subst e; exact hj hx
          · simpa using hP1
        · exact h1 Q (List.mem_cons_of_mem _ hQ)
      · intro σ
        obtain ⟨Q, hQ, hσ⟩ := h3 σ
        rcases List.mem_cons.mp hQ with rfl | hQ
        · obtain ⟨j, hj, hb⟩ := ign_begins_extend σ Q hσ hP.2
          refine ⟨Q ++ [j], hperm.mem_iff.mpr (List.mem_append_left _ ((ign_mem_children Q _).mpr ⟨j, hj, rfl⟩)), hb⟩
        · exact ⟨Q, hperm.mem_iff.mpr (List.mem_append_right _ hQ), hσ⟩
      · rw [(hperm.map _).sum_eq, List.map_append, List.sum_append]
        have hc : ((children P).map (fun Q => (n - Q.length).factorial)).sum =
            (n - P.length) * (n - (P.length + 1)).factorial := by
          have : (children P).map (fun Q => (n - Q.length).factorial) =
              (children P).map (fun _ => (n - (P.length + 1)).factorial) := by
            apply List.map_congr_left
            intro x hx
            obtain ⟨j, hj, rfl⟩ := (ign_mem_children P x).mp hx
            simp
          rw [this, List.map_const', List.sum_replicate, ign_children_length P hP.1]
          simp
        rw [hc]
        have h4' := h4
        simp only [List.map_cons, List.sum_cons] at h4'
        have hfac : (n - P.length) * (n - (P.length + 1)).factorial = (n - P.length).factorial := by
          have : n - P.length = (n - (P.length + 1)) + 1 := by omega
          rw [this, Nat.factorial_succ]
        rw [hfac]; exact h4'

theorem ign_good_init (hn : 1 ≤ n) : IgnGood LB ([[]] : List (List (Fin n))) := by
  refine ⟨?_, by simp, ?_, by simp⟩
  · intro Q hQ; simp at hQ; subst hQ; simp; omega
  · intro σ; exact ⟨[], by simp, by simp [BeginsWith]⟩

theorem ign_run_good (hn : 1 ≤ n) (k : ℕ) : IgnGood LB (run LB k) := by
  induction k with
  | zero => exact ign_good_init LB hn
  | succ k ih =>
    unfold run at *
    rw [Function.iterate_succ_apply']
    exact ign_step_good LB _ hn ih


theorem ign_run_succ (k : ℕ) : run LB (k + 1) = step LB (run LB k) := by
  unfold run; rw [Function.iterate_succ_apply']

theorem ign_run_ne_nil (hn : 1 ≤ n) (k : ℕ) : ∃ P rest, run LB k = P :: rest := by
  obtain ⟨Q, hQ, _⟩ := (ign_run_good LB hn k).2.2.1 1
  cases h : run LB k with
  | nil => rw [h] at hQ; simp at hQ
  | cons P rest => exact ⟨P, rest, rfl⟩

theorem ign_length_le (hn : 1 ≤ n) (k : ℕ) : (run LB k).length ≤ n.factorial := by
  have h := (ign_run_good LB hn k).2.2.2
  have h1 := (ign_run_good LB hn k).1
  have : (run LB k).length = ((run LB k).map (fun Q => (n - Q.length).factorial)).length := by simp
  rw [this]
  refine le_trans (List.length_le_sum_of_one_le _ ?_) h.le
  intro i hi
  obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hi
  exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)

theorem ign_weight_decrease (P : List (Fin n)) (rest : List (List (Fin n)))
    (h : IgnGood LB (P :: rest)) (ht : ¬ IsTerminal P) :
    ((step LB (P :: rest)).map (fun Q => (n + 1) ^ (n - Q.length))).sum <
      ((P :: rest).map (fun Q => (n + 1) ^ (n - Q.length))).sum := by
  have hP := h.1 P (by simp)
  have hP1 : P.length + 1 < n := by
    have := hP.2; unfold IsTerminal at ht; omega
  rw [ign_step_cons LB P rest ht]
  have hperm := ign_foldl_perm LB (children P) rest
  rw [(hperm.map _).sum_eq, List.map_append, List.sum_append]
  simp only [List.map_cons, List.sum_cons]
  have hc : ((children P).map (fun Q => (n + 1) ^ (n - Q.length))).sum =
      (n - P.length) * (n + 1) ^ (n - (P.length + 1)) := by
    have : (children P).map (fun Q => (n + 1) ^ (n - Q.length)) =
        (children P).map (fun _ => (n + 1) ^ (n - (P.length + 1))) := by
      apply List.map_congr_left
      intro x hx
      obtain ⟨j, hj, rfl⟩ := (ign_mem_children P x).mp hx
      simp
    rw [this, List.map_const', List.sum_replicate, ign_children_length P hP.1]
    simp
  rw [hc]
  have e : (n + 1) ^ (n - P.length) = (n + 1) * (n + 1) ^ (n - (P.length + 1)) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : 0 < (n + 1) ^ (n - (P.length + 1)) := by positivity
  have : (n - P.length) * (n + 1) ^ (n - (P.length + 1)) < (n + 1) ^ (n - P.length) := by
    rw [e]
    apply Nat.mul_lt_mul_of_pos_right _ hpos
    omega
  omega

theorem ign_exists_terminal (hn : 1 ≤ n) : ∃ k P, (run LB k).head? = some P ∧ IsTerminal P := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ k, ((run LB k).map (fun Q => (n + 1) ^ (n - Q.length))).sum + k ≤
      ((run LB 0).map (fun Q => (n + 1) ^ (n - Q.length))).sum := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨P, rest, hr⟩ := ign_run_ne_nil LB hn k
      have ht : ¬ IsTerminal P := hcon k P (by rw [hr]; rfl)
      have := ign_weight_decrease LB P rest (hr ▸ ign_run_good LB hn k) ht
      rw [ign_run_succ, hr]
      rw [hr] at ih
      omega
  have := key (((run LB 0).map (fun Q => (n + 1) ^ (n - Q.length))).sum + 1)
  omega

theorem ign_exists_perm_terminal (P : List (Fin n)) (hP : P.Nodup) (hl : P.length + 1 = n) :
    ∃ σ : Equiv.Perm (Fin n), BeginsWith σ P := by
  classical
  have hex : ∃ l, l ∉ P := by
    by_contra hcon
    push_neg at hcon
    have : (Finset.univ : Finset (Fin n)) ⊆ P.toFinset := fun j _ => by simpa using hcon j
    have h2 := Finset.card_le_card this
    rw [List.toFinset_card_of_nodup hP] at h2
    simp at h2; omega
  obtain ⟨l, hl'⟩ := hex
  set P' := P ++ [l] with hP'
  have hnd : P'.Nodup := List.nodup_append.mpr ⟨hP, List.nodup_singleton _, by
    intro x hx y hy; simp at hy; subst hy; intro e; subst e; exact hl' hx⟩
  have hlen : P'.length = n := by simp [hP']; omega
  let f : Fin n → Fin n := fun i => P'[i.1]'(by rw [hlen]; exact i.2)
  have hf : Function.Injective f := by
    intro i j hij
    have := (List.Nodup.getElem_inj_iff hnd).mp hij
    exact Fin.ext this
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  refine ⟨σ, [l], ?_⟩
  have : List.ofFn σ = P' := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp [σ, f]
  rw [this]

theorem ign_goal_core (a b c : Fin n → ℝ) (hn : 1 ≤ n) (hLB : ∀ J : List (Fin n), J.length < n → ∀ σ : Equiv.Perm (Fin n),
      BeginsWith σ J → LB J ≤ makespan a b c σ)
    (hEq : ∀ J : List (Fin n), J.length + 1 = n → ∀ σ : Equiv.Perm (Fin n),
      BeginsWith σ J → LB J = makespan a b c σ) :
    (∃ k P, (run LB k).head? = some P ∧ IsTerminal P) ∧
    ∀ k P, (run LB k).head? = some P → IsTerminal P →
      ∃ σstar : Equiv.Perm (Fin n), BeginsWith σstar P ∧
        ∀ σ : Equiv.Perm (Fin n), makespan a b c σstar ≤ makespan a b c σ := by
  refine ⟨ign_exists_terminal LB hn, ?_⟩
  intro k P hhead hterm
  obtain ⟨P0, rest, hr⟩ := ign_run_ne_nil LB hn k
  rw [hr] at hhead
  have hh : P0 = P := by simpa using hhead
  subst hh
  have hg := ign_run_good LB hn k
  rw [hr] at hg
  obtain ⟨σs, hσs⟩ := ign_exists_perm_terminal P0 (hg.1 P0 (by simp)).1 hterm
  refine ⟨σs, hσs, ?_⟩
  intro σ
  obtain ⟨Q, hQ, hσQ⟩ := hg.2.2.1 σ
  have hQlen := (hg.1 Q hQ).2
  have h1 : LB P0 ≤ LB Q := by
    rcases List.mem_cons.mp hQ with hQe | hQ'
    · rw [hQe]
    · exact (List.pairwise_cons.mp hg.2.1).1 Q hQ'
  rw [← hEq P0 hterm σs hσs]
  exact h1.trans (hLB Q hQlen σ hσQ)


end proc

def ignG : ℕ → ℕ
  | 0 => 0
  | m + 1 => 1 + (m + 1) * ignG m

theorem ignG_eq (m : ℕ) : ignG m = ∑ j ∈ Finset.range m, m.descFactorial j := by
  induction m with
  | zero => simp [ignG]
  | succ m ih =>
    rw [ignG, ih, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.succ_descFactorial_succ, Nat.descFactorial_zero]
    rw [add_comm]

theorem ignG_pos (m : ℕ) (h : 1 ≤ m) : 1 ≤ ignG m := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [ignG]; omega

theorem ign_S_closed (n m : ℕ) (h : m ≤ n) :
    2 * (∑ s ∈ Finset.range m, (n - s)) + m * m = 2 * m * n + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have := ih (by omega)
    obtain ⟨d, rfl⟩ : ∃ d, n = m + 1 + d := ⟨n - (m + 1), by omega⟩
    have e : m + 1 + d - m = d + 1 := by omega
    rw [e]
    nlinarith

section proc2
variable {n : ℕ} (LB : List (Fin n) → ℝ)

theorem ign_cc_succ (k : ℕ) (P : List (Fin n)) (rest : List (List (Fin n)))
    (hr : run LB k = P :: rest) :
    createdCount LB (k + 1) = createdCount LB k + (if IsTerminal P then 0 else (children P).length) := by
  simp [createdCount, hr]

theorem ign_counts_inv (hn : 1 ≤ n) (k : ℕ) :
    (createdCount LB k + ((run LB k).map (fun Q => ignG (n - Q.length))).sum =
      ignG n + (run LB k).length) ∧
    (∀ Q ∈ run LB k, 1 + ∑ s ∈ Finset.range Q.length, (n - s) ≤ createdCount LB k) := by
  induction k with
  | zero =>
    simp [createdCount, run]
    omega
  | succ k ih =>
    obtain ⟨P, rest, hr⟩ := ign_run_ne_nil LB hn k
    have hg := ign_run_good LB hn k
    rw [hr] at hg
    have hcc := ign_cc_succ LB k P rest hr
    rw [hr] at ih
    have hP := hg.1 P (by simp)
    by_cases ht : IsTerminal P
    · rw [ign_run_succ, hr, ign_step_term LB P rest ht]
      rw [hcc, if_pos ht]
      simpa using ih
    · rw [if_neg ht, ign_children_length P hP.1] at hcc
      rw [ign_run_succ, hr, ign_step_cons LB P rest ht]
      have hperm := ign_foldl_perm LB (children P) rest
      have hP1 : P.length + 1 < n := by
        have := hP.2; unfold IsTerminal at ht; omega
      constructor
      · rw [(hperm.map _).sum_eq, hperm.length_eq, hcc, List.map_append, List.sum_append,
          List.length_append, ign_children_length P hP.1]
        have hc : ((children P).map (fun Q => ignG (n - Q.length))).sum =
            (n - P.length) * ignG (n - (P.length + 1)) := by
          have : (children P).map (fun Q => ignG (n - Q.length)) =
              (children P).map (fun _ => ignG (n - (P.length + 1))) := by
            apply List.map_congr_left
            intro x hx
            obtain ⟨j, hj, rfl⟩ := (ign_mem_children P x).mp hx
            simp
          rw [this, List.map_const', List.sum_replicate, ign_children_length P hP.1]
          simp
        rw [hc]
        have e : ignG (n - P.length) = 1 + (n - P.length) * ignG (n - (P.length + 1)) := by
          have : n - P.length = (n - (P.length + 1)) + 1 := by omega
          rw [this, ignG]
        have h1 := ih.1
        simp only [List.map_cons, List.sum_cons, List.length_cons] at h1
        rw [e] at h1
        generalize (n - P.length) * ignG (n - (P.length + 1)) = X at *
        omega
      · intro Q hQ
        have := hperm.mem_iff.mp hQ
        rcases List.mem_append.mp this with hQ | hQ
        · obtain ⟨j, hj, rfl⟩ := (ign_mem_children P Q).mp hQ
          have h2 := ih.2 P (by simp)
          rw [hcc]
          simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
          omega
        · have h2 := ih.2 Q (List.mem_cons_of_mem _ hQ)
          rw [hcc]; omega

theorem ign_node_counts (hn : 1 ≤ n) :
    (∀ k P, (run LB k).head? = some P → IsTerminal P →
      n * (n + 1) ≤ 2 * createdCount LB k) ∧
    (∀ k, createdCount LB k ≤ ∑ j ∈ Finset.range n, n.descFactorial j) ∧
    (∀ k, (run LB k).length ≤ n.factorial) := by
  refine ⟨?_, ?_, ign_length_le LB hn⟩
  · intro k P hhead ht
    obtain ⟨P0, rest, hr⟩ := ign_run_ne_nil LB hn k
    rw [hr] at hhead
    have hh : P0 = P := by simpa using hhead
    subst hh
    have h2 := (ign_counts_inv LB hn k).2 P0 (by rw [hr]; simp)
    have hlen : P0.length + 1 = n := ht
    obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
    have hd : P0.length = d := by omega
    rw [hd] at h2
    have := ign_S_closed (d + 1) d (by omega)
    nlinarith
  · intro k
    rw [← ignG_eq]
    have h := (ign_counts_inv LB hn k).1
    have hg := ign_run_good LB hn k
    have : (run LB k).length ≤ ((run LB k).map (fun Q => ignG (n - Q.length))).sum := by
      have e : (run LB k).length = ((run LB k).map (fun Q => ignG (n - Q.length))).length := by simp
      rw [e]
      apply List.length_le_sum_of_one_le
      intro i hi
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hi
      exact ignG_pos _ (by have := (hg.1 Q hQ).2; omega)
    omega

end proc2

theorem branch_and_bound_core {n : ℕ} (hn : 1 ≤ n) (a b c : Fin n → ℝ) :
    (∃ k P, (run (lowerBound a b c) k).head? = some P ∧ IsTerminal P) ∧
    ∀ k P, (run (lowerBound a b c) k).head? = some P → IsTerminal P →
      ∃ σstar : Equiv.Perm (Fin n), BeginsWith σstar P ∧
        ∀ σ : Equiv.Perm (Fin n), makespan a b c σstar ≤ makespan a b c σ :=
  ign_goal_core (lowerBound a b c) a b c hn
    (fun J hJ σ hσ => lowerBound_le_makespan_core a b c J hJ σ hσ)
    (fun J hJ σ hσ => lowerBound_eq_makespan_core a b c J hJ σ hσ)

theorem node_counts_core {n : ℕ} (hn : 1 ≤ n) (a b c : Fin n → ℝ) :
    (∀ k P, (run (lowerBound a b c) k).head? = some P → IsTerminal P →
      n * (n + 1) ≤ 2 * createdCount (lowerBound a b c) k) ∧
    (∀ k, createdCount (lowerBound a b c) k ≤ ∑ j ∈ Finset.range n, n.descFactorial j) ∧
    (∀ k, (run (lowerBound a b c) k).length ≤ n.factorial) :=
  ign_node_counts (lowerBound a b c) hn

end IgnallSchrage.Makespan

open IgnallSchrage.Makespan


theorem solution {n : ℕ} (hn : 1 ≤ n) (a b c : Fin n → ℝ) :
    (∀ k P, (run (lowerBound a b c) k).head? = some P → IsTerminal P →
      n * (n + 1) ≤ 2 * createdCount (lowerBound a b c) k) ∧
    (∀ k, createdCount (lowerBound a b c) k ≤ ∑ j ∈ Finset.range n, n.descFactorial j) ∧
    (∀ k, (run (lowerBound a b c) k).length ≤ n.factorial) := by
  exact node_counts_core hn a b c
