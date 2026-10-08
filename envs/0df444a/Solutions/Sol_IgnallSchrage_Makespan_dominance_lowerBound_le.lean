-- Prove2me | solution 1 for IgnallSchrage.Makespan.dominance_lowerBound_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:37:42.126971+00:00
-- url     : https://prove2.me/submissions/c3b86173-751c-4c09-badf-660313fa5da2

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
end IgnallSchrage.Makespan

open IgnallSchrage.Makespan


theorem solution {n : ℕ} (a b c : Fin n → ℝ) (J I : List (Fin n))
    (hJI : J.Perm I) (hB : (times a b c J).2.1 ≤ (times a b c I).2.1)
    (hC : (times a b c J).2.2 ≤ (times a b c I).2.2) :
    lowerBound a b c J ≤ lowerBound a b c I := by
  exact dominance_core a b c J I hJI hB hC
