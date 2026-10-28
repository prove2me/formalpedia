-- Prove2me | solution 1 for MinLatency.Approx.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:17:23.565423+00:00
-- url     : https://prove2.me/submissions/f921b94f-af5b-46ce-be19-74996e4c0ddc

import Mathlib
import Definitions.Def_MinLatency_Approx_Setting

open MinLatency.Approx

set_option linter.unusedSectionVars false

section L5aux
variable {V : Type} [Fintype V] [DecidableEq V]

lemma l5_d_nonneg {d : V → V → ℝ} (hd : IsMetric d) (u v : V) : 0 ≤ d u v := by
  by_cases h : u = v
  · subst h; simp [hd.self]
  · exact (hd.pos u v h).le

lemma l5_pathLen_cons2 (d : V → V → ℝ) (a b : V) (t : List V) :
    pathLen d (a :: b :: t) = d a b + pathLen d (b :: t) := rfl

lemma l5_pathLen_single (d : V → V → ℝ) (a : V) : pathLen d [a] = 0 := rfl

lemma l5_pathLen_nil (d : V → V → ℝ) : pathLen d ([] : List V) = 0 := rfl

lemma l5_pathLen_nonneg {d : V → V → ℝ} (hd : IsMetric d) : ∀ l : List V, 0 ≤ pathLen d l
  | [] => le_rfl
  | [_] => le_rfl
  | u :: v :: t => by
      rw [l5_pathLen_cons2]
      have := l5_pathLen_nonneg hd (v :: t); have := l5_d_nonneg hd u v; linarith

lemma l5_dist_le_pathLen {d : V → V → ℝ} (hd : IsMetric d) (v : V) :
    ∀ (l : List V) (a : V), v ∈ l → d a v ≤ pathLen d (a :: l)
  | [], _, h => by simp at h
  | x :: t, a, h => by
      rw [l5_pathLen_cons2]
      rcases List.mem_cons.1 h with h | h
      · subst h; have := l5_pathLen_nonneg hd (v :: t); linarith
      · have := l5_dist_le_pathLen hd v t x h
        have := hd.triangle a x v; linarith

lemma l5_dist_le_pathLen' {d : V → V → ℝ} (hd : IsMetric d) (v a : V) (l : List V)
    (h : v ∈ a :: l) : d a v ≤ pathLen d (a :: l) := by
  rcases List.mem_cons.1 h with h | h
  · subst h; rw [hd.self]; exact l5_pathLen_nonneg hd _
  · exact l5_dist_le_pathLen hd v l a h

lemma l5_sublist {d : V → V → ℝ} (hd : IsMetric d) {T W : List V} (h : T.Sublist W) :
    ∀ a, pathLen d (a :: T) ≤ pathLen d (a :: W) := by
  induction h with
  | slnil => intro a; exact le_rfl
  | @cons l₁ l₂ x h ih =>
      intro a
      refine (ih a).trans ?_
      rw [l5_pathLen_cons2]
      cases l₂ with
      | nil => simp only [l5_pathLen_single]; have := l5_d_nonneg hd a x; linarith
      | cons w W' =>
          rw [l5_pathLen_cons2, l5_pathLen_cons2]
          have := hd.triangle a x w; linarith
  | @cons_cons l₁ l₂ x h ih =>
      intro a
      rw [l5_pathLen_cons2, l5_pathLen_cons2]
      have := ih x; linarith

lemma l5_prefix {d : V → V → ℝ} (hd : IsMetric d) {P W : List V} (h : P <+: W) :
    pathLen d P ≤ pathLen d W := by
  obtain ⟨r, rfl⟩ := h
  cases P with
  | nil => simp only [List.nil_append, l5_pathLen_nil]; exact l5_pathLen_nonneg hd _
  | cons a T =>
      rw [List.cons_append]
      exact l5_sublist hd (List.sublist_append_left T r) a

lemma l5_mem_take_idx (l : List V) (v : V) (h : v ∈ l) : v ∈ l.take (l.idxOf v + 1) := by
  rw [List.mem_take_iff_getElem]
  have hl := List.idxOf_lt_length_of_mem h
  exact ⟨l.idxOf v, by omega, List.getElem_idxOf hl⟩

lemma l5_firstVisit_le {d : V → V → ℝ} (hd : IsMetric d) {P W : List V} (h : P <+: W) (v : V)
    (hv : v ∈ P) : firstVisit d W v ≤ pathLen d P := by
  obtain ⟨r, rfl⟩ := h
  unfold firstVisit
  rw [List.idxOf_append_of_mem hv]
  have hl := List.idxOf_lt_length_of_mem hv
  rw [List.take_append_of_le_length (by omega)]
  exact l5_prefix hd (List.take_prefix _ _)

lemma l5_pathLen_append (d : V → V → ℝ) (y : V) (Y : List V) :
    ∀ l : List V, pathLen d (l ++ y :: Y) = pathLen d (l ++ [y]) + pathLen d (y :: Y)
  | [] => by simp [l5_pathLen_single]
  | [a] => by simp [l5_pathLen_cons2, l5_pathLen_single]
  | a :: b :: t => by
      simp only [List.cons_append]
      rw [l5_pathLen_cons2, l5_pathLen_cons2]
      have := l5_pathLen_append d y Y (b :: t)
      simp only [List.cons_append] at this
      rw [this]; ring

lemma l5_pathLen_snoc (d : V → V → ℝ) (w : V) :
    ∀ (t : List V) (u : V), pathLen d (u :: t ++ [w]) =
      pathLen d (u :: t) + d ((u :: t).getLast (List.cons_ne_nil u t)) w
  | [], u => by simp [l5_pathLen_cons2, l5_pathLen_single]
  | x :: t, u => by
      simp only [List.cons_append]
      rw [l5_pathLen_cons2, l5_pathLen_cons2]
      have := l5_pathLen_snoc d w t x
      simp only [List.cons_append] at this
      rw [this, List.getLast_cons_cons]; ring

lemma l5_tourLen_eq (d : V → V → ℝ) (u : V) (t : List V) :
    tourLen d (u :: t) = pathLen d (u :: t ++ [u]) := by
  rw [l5_pathLen_snoc]; rfl

lemma l5_tourLen_append (d : V → V → ℝ) (p : V) (X Y : List V) (hX : X.head? = some p)
    (hY : Y.head? = some p) : tourLen d (X ++ Y) = tourLen d X + tourLen d Y := by
  cases X with
  | nil => simp at hX
  | cons x X' =>
    cases Y with
    | nil => simp at hY
    | cons y Y' =>
      simp only [List.head?_cons, Option.some.injEq] at hX hY
      subst hX hY
      show tourLen d (y :: (X' ++ y :: Y')) = _
      rw [l5_tourLen_eq, l5_tourLen_eq, l5_tourLen_eq]
      have e : y :: (X' ++ y :: Y') ++ [y] = (y :: X') ++ y :: (Y' ++ [y]) := by simp
      rw [e, l5_pathLen_append]; rfl

lemma l5_pathLen_le_tourLen {d : V → V → ℝ} (hd : IsMetric d) (l : List V) :
    pathLen d l ≤ tourLen d l := by
  cases l with
  | nil => exact le_rfl
  | cons u t => simp only [tourLen]; have := l5_d_nonneg hd ((u :: t).getLast (List.cons_ne_nil u t)) u; linarith

lemma l5_nnDist_pos {d : V → V → ℝ} (hd : IsMetric d) (p : V) : 0 < nnDist d p := by
  unfold nnDist
  split_ifs with h
  · rw [Finset.lt_inf'_iff]
    intro v hv
    simp only [Finset.mem_filter] at hv
    exact hd.pos p v (Ne.symm hv.2)
  · exact one_pos

lemma l5_nnDist_le {d : V → V → ℝ} (p v : V) (hv : v ≠ p) : nnDist d p ≤ d p v := by
  unfold nnDist
  have h : (Finset.univ.filter (fun v => v ≠ p)).Nonempty := ⟨v, by simp [hv]⟩
  rw [dif_pos h]
  exact Finset.inf'_le _ (by simp [hv])

lemma l5_budget_pos {d : V → V → ℝ} (hd : IsMetric d) (p : V) (j : ℕ) : 0 < budget d p j := by
  unfold budget; have := l5_nnDist_pos hd p; positivity

lemma l5_A_basic {d : V → V → ℝ} {p : V} (hd : IsMetric d) {α β : ℝ} {A : ℝ → List V}
    (hA : IsTSPApprox d p α β A) (L : ℝ) (hL : 0 < L) :
    IsRootedTour p (A L) ∧ tourLen d (A L) ≤ β * L := by
  have := hA L hL (Fintype.card V) ⟨[p], ⟨rfl, List.nodup_singleton p⟩, by
    simp [tourLen, l5_pathLen_single, hd.self]; exact hL.le, Finset.card_filter_le _ _⟩
  exact ⟨this.1, this.2.1⟩

lemma l5_doublingWalk_succ (d : V → V → ℝ) (p : V) (A : ℝ → List V) (i : ℕ) :
    doublingWalk d p A (i + 1) = doublingWalk d p A i ++ A (budget d p (i + 1)) := by
  unfold doublingWalk
  rw [List.range_succ, List.flatMap_append]
  simp

lemma l5_doublingWalk_prefix (d : V → V → ℝ) (p : V) (A : ℝ → List V) (i : ℕ) :
    ∀ J, i ≤ J → doublingWalk d p A i <+: doublingWalk d p A J := by
  intro J hJ
  induction J with
  | zero => obtain rfl : i = 0 := by omega
            exact List.prefix_refl _
  | succ J ih =>
    rcases Nat.lt_or_ge i (J + 1) with h | h
    · rw [l5_doublingWalk_succ]
      exact (ih (by omega)).trans (List.prefix_append _ _)
    · obtain rfl : i = J + 1 := by omega
      exact List.prefix_refl _

lemma l5_doublingWalk_tour {d : V → V → ℝ} {p : V} (hd : IsMetric d) {α β : ℝ} {A : ℝ → List V}
    (hA : IsTSPApprox d p α β A) (i : ℕ) :
    (doublingWalk d p A i).head? = some p ∧
      tourLen d (doublingWalk d p A i) ≤ β * nnDist d p * (2 ^ (i + 2) - 2) := by
  induction i with
  | zero =>
    have h0 : doublingWalk d p A 0 = A (budget d p 0) := by simp [doublingWalk]
    rw [h0]
    obtain ⟨h1, h2⟩ := l5_A_basic hd hA _ (l5_budget_pos hd p 0)
    refine ⟨h1.1, ?_⟩
    simp only [budget] at h2 ⊢; norm_num at h2 ⊢; linarith
  | succ i ih =>
    rw [l5_doublingWalk_succ]
    obtain ⟨h1, h2⟩ := l5_A_basic hd hA _ (l5_budget_pos hd p (i + 1))
    obtain ⟨ih1, ih2⟩ := ih
    have hne : doublingWalk d p A i ≠ [] := by intro h; rw [h] at ih1; simp at ih1
    refine ⟨?_, ?_⟩
    · rw [List.head?_append_of_ne_nil _ hne]; exact ih1
    · rw [l5_tourLen_append d p _ _ ih1 h1.1]
      simp only [budget] at h2 ⊢
      have : β * nnDist d p * (2 ^ (i + 1 + 2) - 2) =
          β * nnDist d p * (2 ^ (i + 2) - 2) + β * (2 ^ (i + 1 + 1) * nnDist d p) := by ring
      rw [this]; linarith

lemma l5_beta_nonneg {d : V → V → ℝ} {p : V} (hd : IsMetric d) {α β : ℝ} {A : ℝ → List V}
    (hA : IsTSPApprox d p α β A) : 0 ≤ β := by
  obtain ⟨_, h2⟩ := l5_A_basic hd hA 1 one_pos
  have := l5_pathLen_le_tourLen hd (A 1)
  have := l5_pathLen_nonneg hd (A 1)
  linarith

lemma l5_part2 {d : V → V → ℝ} {p : V} (hd : IsMetric d) {α β : ℝ} {A : ℝ → List V}
    (hA : IsTSPApprox d p α β A) (j J : ℕ) (hjJ : j ≤ J) (v : V)
    (hv : ∃ i ≤ j, v ∈ A (budget d p i)) :
    firstVisit d (doublingWalk d p A J) v ≤ β * (2 : ℝ) ^ (j + 2) * nnDist d p := by
  obtain ⟨i, hij, hvi⟩ := hv
  have hmem : v ∈ doublingWalk d p A i := by
    unfold doublingWalk; rw [List.mem_flatMap]; exact ⟨i, by simp, hvi⟩
  have h1 := l5_firstVisit_le hd (l5_doublingWalk_prefix d p A i J (by omega)) v hmem
  have h2 := l5_pathLen_le_tourLen hd (doublingWalk d p A i)
  have h3 := (l5_doublingWalk_tour hd hA i).2
  have hb := l5_beta_nonneg hd hA
  have hδ := (l5_nnDist_pos hd p).le
  have h4 : (2 : ℝ) ^ (i + 2) ≤ 2 ^ (j + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h5 : β * nnDist d p * (2 ^ (i + 2) - 2) ≤ β * nnDist d p * 2 ^ (j + 2) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hb hδ)
  linarith

lemma l5_part1 {d : V → V → ℝ} {p : V} (hd : IsMetric d) {α β : ℝ} {A : ℝ → List V}
    (hA : IsTSPApprox d p α β A) (σ : List V) (hσ : IsCoveringWalk p σ) (j : ℕ) :
    (Fintype.card V : ℝ) - α * ((Finset.univ.filter
          (fun v => (2 : ℝ) ^ j * nnDist d p < firstVisit d σ v)).card : ℝ)
        ≤ ((Finset.univ.filter (fun v => ∃ i ≤ j, v ∈ A (budget d p i))).card : ℝ) := by
  set S := Finset.univ.filter (fun v => firstVisit d σ v ≤ (2 : ℝ) ^ j * nnDist d p) with hS
  obtain ⟨σ', rfl⟩ : ∃ σ', σ = p :: σ' := by
    obtain ⟨h1, _⟩ := hσ
    cases σ with
    | nil => simp at h1
    | cons a t => simp at h1; subst h1; exact ⟨t, rfl⟩
  have hpS : p ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold firstVisit; simp [l5_pathLen_single]; have := (l5_nnDist_pos hd p).le; positivity
  obtain ⟨w, hwS, hwmax⟩ := Finset.exists_max_image S (fun v => (p :: σ').idxOf v) ⟨p, hpS⟩
  set W' := σ'.take ((p :: σ').idxOf w) with hW'
  have hWeq : (p :: σ').take ((p :: σ').idxOf w + 1) = p :: W' := by simp [hW']
  have hSW : ∀ v ∈ S, v ∈ p :: W' := by
    intro v hv
    have hvm : v ∈ p :: σ' := hσ.2 v
    have := l5_mem_take_idx (p :: σ') v hvm
    rw [← hWeq]
    exact (List.take_prefix_take_left (Nat.succ_le_succ (hwmax v hv))).subset this
  set T' := (W'.dedup).filter (fun x => x ≠ p) with hT'
  have hT'sub : T'.Sublist W' := (List.filter_sublist).trans (List.dedup_sublist _)
  have hwfv : pathLen d (p :: W') ≤ (2 : ℝ) ^ j * nnDist d p := by
    rw [← hWeq]
    have := (Finset.mem_filter.1 hwS).2
    unfold firstVisit at this; exact this
  have hTpath : pathLen d (p :: T') ≤ (2 : ℝ) ^ j * nnDist d p :=
    (l5_sublist hd hT'sub p).trans hwfv
  have hTour : IsRootedTour p (p :: T') := by
    refine ⟨rfl, List.nodup_cons.2 ⟨?_, (List.nodup_dedup _).filter _⟩⟩
    simp [hT']
  have hTlen : tourLen d (p :: T') ≤ budget d p j := by
    simp only [tourLen]
    have := l5_dist_le_pathLen' hd ((p :: T').getLast (List.cons_ne_nil p T')) p T'
      (List.getLast_mem _)
    rw [hd.symm] at this
    unfold budget; rw [pow_succ]; linarith
  have hmiss : missed (p :: T') ≤ (Finset.univ.filter
          (fun v => (2 : ℝ) ^ j * nnDist d p < firstVisit d (p :: σ') v)).card := by
    unfold missed
    apply Finset.card_le_card
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    by_contra hcon
    push Not at hcon
    have hvS : v ∈ S := by simp [hS, hcon]
    have := hSW v hvS
    apply hv
    rcases List.mem_cons.1 this with h | h
    · rw [h]; exact List.mem_cons_self
    · by_cases hvp : v = p
      · rw [hvp]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (by simp [hT', List.mem_dedup, h, hvp])
  obtain ⟨_, _, hmA⟩ := hA (budget d p j) (l5_budget_pos hd p j) _ ⟨p :: T', hTour, hTlen, hmiss⟩
  have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
    (fun v => v ∈ A (budget d p j))
  have hsub : (Finset.univ.filter (fun v => v ∈ A (budget d p j))).card ≤
      (Finset.univ.filter (fun v => ∃ i ≤ j, v ∈ A (budget d p i))).card := by
    apply Finset.card_le_card
    intro v hv; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨j, le_rfl, hv⟩
  unfold missed at hmA
  rw [Finset.card_univ] at hcard
  have hc : ((Finset.univ.filter (fun v => v ∈ A (budget d p j))).card : ℝ) +
      ((Finset.univ.filter (fun v => v ∉ A (budget d p j))).card : ℝ) = Fintype.card V := by
    exact_mod_cast hcard
  have : ((Finset.univ.filter (fun v => v ∈ A (budget d p j))).card : ℝ) ≤
      ((Finset.univ.filter (fun v => ∃ i ≤ j, v ∈ A (budget d p i))).card : ℝ) := by
    exact_mod_cast hsub
  linarith


lemma l5_head_eq {T : List V} {p : V} (h : T.head? = some p) : ∃ t, T = p :: t := by
  cases T with
  | nil => simp at h
  | cons a t => simp at h; exact ⟨t, by rw [h]⟩

lemma l5_firstVisit_head (d : V → V → ℝ) {W : List V} {p : V} (h : W.head? = some p) :
    firstVisit d W p = 0 := by
  obtain ⟨t, rfl⟩ := l5_head_eq h
  unfold firstVisit; simp [l5_pathLen_single]

lemma l5_fv_ge {d : V → V → ℝ} (hd : IsMetric d) {p : V} {σ : List V} (hσ : IsCoveringWalk p σ)
    (v : V) : d p v ≤ firstVisit d σ v := by
  obtain ⟨t, ht⟩ := l5_head_eq hσ.1
  have hm := l5_mem_take_idx σ v (hσ.2 v)
  unfold firstVisit
  rw [ht] at hm ⊢
  rw [List.take_succ_cons] at hm ⊢
  exact l5_dist_le_pathLen' hd v p _ hm

lemma l5_trivial_tour {d : V → V → ℝ} (hd : IsMetric d) (p : V) (L : ℝ) (hL : 0 < L) :
    ∃ T, IsRootedTour p T ∧ tourLen d T ≤ L ∧ missed T ≤ Fintype.card V :=
  ⟨[p], ⟨rfl, List.nodup_singleton p⟩, by
    simp [tourLen, l5_pathLen_single, hd.self]; exact hL.le, Finset.card_filter_le _ _⟩

lemma l5_alpha_nonneg {d : V → V → ℝ} {p : V} (hd : IsMetric d) {α β : ℝ} {A : ℝ → List V}
    (hA : IsTSPApprox d p α β A) : 0 ≤ α := by
  have h3 := (hA 1 one_pos _ (l5_trivial_tour hd p 1 one_pos)).2.2
  have hn : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.2 ⟨p⟩
  by_contra h; push Not at h
  have : α * (Fintype.card V : ℝ) < 0 := mul_neg_of_neg_of_pos h hn
  have : (0:ℝ) ≤ missed (A 1) := Nat.cast_nonneg _
  linarith

lemma l5_mem_of_missed {T : List V} (h : (missed T : ℝ) ≤ 0) (v : V) : v ∈ T := by
  have h0 : missed T = 0 := by exact_mod_cast le_antisymm h (Nat.cast_nonneg _)
  unfold missed at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  by_contra hv; exact h0 (Finset.mem_univ v) hv

lemma l5_alpha_pos {d : V → V → ℝ} {p : V} (hd : IsMetric d) {α β : ℝ} {A : ℝ → List V}
    (hA : IsTSPApprox d p α β A) (v : V) (hv : v ≠ p) : 0 < α := by
  by_contra h; push Not at h
  have hα : α = 0 := le_antisymm h (l5_alpha_nonneg hd hA)
  have hb := l5_beta_nonneg hd hA
  have hδ := l5_nnDist_pos hd p
  have hb1 : 0 < 2 * (β + 1) := by linarith
  have hLpos : 0 < nnDist d p / (2 * (β + 1)) := div_pos hδ hb1
  obtain ⟨h1, h2, h3⟩ := hA _ hLpos _ (l5_trivial_tour hd p _ hLpos)
  rw [hα, zero_mul] at h3
  have hvm := l5_mem_of_missed h3 v
  obtain ⟨t, ht⟩ := l5_head_eq h1.1
  have e1 : d p v ≤ pathLen d (A (nnDist d p / (2 * (β + 1)))) := by
    rw [ht]; rw [ht] at hvm; exact l5_dist_le_pathLen' hd v p t hvm
  have e2 := l5_pathLen_le_tourLen hd (A (nnDist d p / (2 * (β + 1))))
  have e3 := l5_nnDist_le (d := d) p v hv
  have e4 : β * (nnDist d p / (2 * (β + 1))) < nnDist d p := by
    rw [mul_div_assoc', div_lt_iff₀ hb1]; nlinarith
  linarith

lemma l5_pointwise {d : V → V → ℝ} {p : V} (hd : IsMetric d) {α β : ℝ} {A : ℝ → List V}
    (hA : IsTSPApprox d p α β A) (J : ℕ) (v : V) :
    ∀ m, m ≤ J → (∃ i ≤ m, v ∈ A (budget d p i)) →
      firstVisit d (doublingWalk d p A J) v ≤ 4 * β * nnDist d p *
        (1 + ∑ j ∈ Finset.range m, (if (∃ i ≤ j, v ∈ A (budget d p i)) then (0:ℝ) else 2 ^ j)) := by
  have hb := l5_beta_nonneg hd hA
  have hδ := (l5_nnDist_pos hd p).le
  have h4b : 0 ≤ 4 * β * nnDist d p := mul_nonneg (mul_nonneg (by norm_num) hb) hδ
  intro m
  induction m with
  | zero =>
    intro hm hv
    have := l5_part2 hd hA 0 J hm v hv
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, mul_one]
    norm_num at this; linarith
  | succ m ih =>
    intro hm hv
    by_cases hU : ∃ i ≤ m, v ∈ A (budget d p i)
    · refine (ih (by omega) hU).trans ?_
      apply mul_le_mul_of_nonneg_left _ h4b
      rw [Finset.sum_range_succ]
      have : (0:ℝ) ≤ (if (∃ i ≤ m, v ∈ A (budget d p i)) then (0:ℝ) else 2 ^ m) := by
        split_ifs <;> positivity
      linarith
    · have hall : ∀ j ∈ Finset.range (m+1),
          (if (∃ i ≤ j, v ∈ A (budget d p i)) then (0:ℝ) else 2 ^ j) = 2 ^ j := by
        intro j hj
        rw [if_neg]
        rintro ⟨i, hi, hvi⟩
        exact hU ⟨i, by simp at hj; omega, hvi⟩
      rw [Finset.sum_congr rfl hall, geom_sum_eq (by norm_num)]
      have := l5_part2 hd hA (m+1) J hm v hv
      have e : (4:ℝ) * β * nnDist d p * (1 + ((2:ℝ) ^ (m + 1) - 1) / (2 - 1)) =
          β * 2 ^ (m + 1 + 2) * nnDist d p := by ring
      rw [e]; exact this

lemma l5_geomH (δ ℓ : ℝ) (hδ : 0 < δ) (hℓ : δ ≤ ℓ) (m : ℕ) :
    δ * ∑ j ∈ Finset.range m, (if (2:ℝ) ^ j * δ < ℓ then (2:ℝ) ^ j else 0) ≤ 2 * ℓ - δ := by
  induction m with
  | zero => simp; linarith
  | succ m ih =>
    rw [Finset.sum_range_succ]
    split_ifs with h
    · have hle : ∑ j ∈ Finset.range m, (if (2:ℝ) ^ j * δ < ℓ then (2:ℝ) ^ j else 0) ≤
          ∑ j ∈ Finset.range m, (2:ℝ) ^ j := by
        apply Finset.sum_le_sum; intro j _; split_ifs <;> first | exact le_rfl | positivity
      rw [geom_sum_eq (by norm_num)] at hle
      norm_num at hle
      have := mul_le_mul_of_nonneg_left hle hδ.le
      nlinarith
    · simpa using ih

lemma l5_main {d : V → V → ℝ} {p : V} (hd : IsMetric d) {α β : ℝ} {A : ℝ → List V}
    (hA : IsTSPApprox d p α β A) (J : ℕ) (hJ : ∀ v, v ∈ A (budget d p J))
    (σ : List V) (hσ : IsCoveringWalk p σ) :
    walkLatency d (doublingWalk d p A J) ≤ 8 * ((⌈α⌉ : ℤ) : ℝ) * β * walkLatency d σ := by
  have hb := l5_beta_nonneg hd hA
  have ha := l5_alpha_nonneg hd hA
  have hδ := l5_nnDist_pos hd p
  have h4b : 0 ≤ 4 * β * nnDist d p := mul_nonneg (mul_nonneg (by norm_num) hb) hδ.le
  have hW : ∀ v, firstVisit d (doublingWalk d p A J) v ≤ 4 * β * nnDist d p *
      (1 + ∑ j ∈ Finset.range J, (if (∃ i ≤ j, v ∈ A (budget d p i)) then (0:ℝ) else 2 ^ j)) :=
    fun v => l5_pointwise hd hA J v J le_rfl ⟨J, le_rfl, hJ v⟩
  have hWp : firstVisit d (doublingWalk d p A J) p = 0 :=
    l5_firstVisit_head d (l5_doublingWalk_tour hd hA J).1
  have hσp : firstVisit d σ p = 0 := l5_firstVisit_head d hσ.1
  have hGnn : ∀ j v, (0:ℝ) ≤ (if (∃ i ≤ j, v ∈ A (budget d p i)) then (0:ℝ) else 2 ^ j) := by
    intro j v; split_ifs <;> positivity
  have hG : ∀ j ∈ Finset.range J,
      ∑ v, (if (∃ i ≤ j, v ∈ A (budget d p i)) then (0:ℝ) else 2 ^ j) ≤
        2 ^ j * (α * ((Finset.univ.filter
          (fun v => (2 : ℝ) ^ j * nnDist d p < firstVisit d σ v)).card : ℝ)) := by
    intro j _
    have h1 := l5_part1 hd hA σ hσ j
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (fun v => ∃ i ≤ j, v ∈ A (budget d p i))
    rw [Finset.card_univ] at hc
    have hc' : ((Finset.univ.filter (fun v => ∃ i ≤ j, v ∈ A (budget d p i))).card : ℝ) +
        ((Finset.univ.filter (fun v => ¬ ∃ i ≤ j, v ∈ A (budget d p i))).card : ℝ) =
        Fintype.card V := by exact_mod_cast hc
    have hsum : ∑ v, (if (∃ i ≤ j, v ∈ A (budget d p i)) then (0:ℝ) else 2 ^ j) =
        2 ^ j * ((Finset.univ.filter (fun v => ¬ ∃ i ≤ j, v ∈ A (budget d p i))).card : ℝ) := by
      rw [Finset.sum_ite]; simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul,
        zero_add]; ring
    rw [hsum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hHnn : ∀ v, (0:ℝ) ≤ ∑ j ∈ Finset.range J,
      (if (2:ℝ) ^ j * nnDist d p < firstVisit d σ v then (2:ℝ) ^ j else 0) := by
    intro v; apply Finset.sum_nonneg; intro j _; split_ifs <;> positivity
  have hHp : ∑ j ∈ Finset.range J,
      (if (2:ℝ) ^ j * nnDist d p < firstVisit d σ p then (2:ℝ) ^ j else 0) = 0 := by
    apply Finset.sum_eq_zero; intro j _
    rw [if_neg]; rw [hσp]; exact not_lt.2 (by positivity)
  have hH : ∀ v, v ≠ p → nnDist d p * ∑ j ∈ Finset.range J,
      (if (2:ℝ) ^ j * nnDist d p < firstVisit d σ v then (2:ℝ) ^ j else 0) ≤
        2 * firstVisit d σ v - nnDist d p := by
    intro v hv
    exact l5_geomH _ _ hδ ((l5_nnDist_le p v hv).trans (l5_fv_ge hd hσ v)) J
  have hswap : ∑ j ∈ Finset.range J, (2:ℝ) ^ j * ((Finset.univ.filter
          (fun v => (2 : ℝ) ^ j * nnDist d p < firstVisit d σ v)).card : ℝ) =
      ∑ v, ∑ j ∈ Finset.range J,
        (if (2:ℝ) ^ j * nnDist d p < firstVisit d σ v then (2:ℝ) ^ j else 0) := by
    simp only [Finset.natCast_card_filter, Finset.mul_sum, mul_ite, mul_one, mul_zero]
    exact Finset.sum_comm
  -- abstract quantities
  -- W side
  have hWsum : walkLatency d (doublingWalk d p A J) ≤ 4 * β * nnDist d p * (((Finset.univ.erase p).card : ℝ) +
      α * ∑ j ∈ Finset.range J, (2:ℝ) ^ j * ((Finset.univ.filter
          (fun v => (2 : ℝ) ^ j * nnDist d p < firstVisit d σ v)).card : ℝ)) := by
    unfold walkLatency
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), hWp, zero_add]
    refine (Finset.sum_le_sum (fun v _ => hW v)).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    apply mul_le_mul_of_nonneg_left _ h4b
    have s1 : ∑ v ∈ Finset.univ.erase p, ∑ j ∈ Finset.range J,
        (if (∃ i ≤ j, v ∈ A (budget d p i)) then (0:ℝ) else 2 ^ j) ≤
        ∑ v, ∑ j ∈ Finset.range J, (if (∃ i ≤ j, v ∈ A (budget d p i)) then (0:ℝ) else 2 ^ j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun v _ _ => Finset.sum_nonneg (fun j _ => hGnn j v))
    have s1' : ∑ v, ∑ j ∈ Finset.range J,
        (if (∃ i ≤ j, v ∈ A (budget d p i)) then (0:ℝ) else 2 ^ j) =
        ∑ j ∈ Finset.range J, ∑ v, (if (∃ i ≤ j, v ∈ A (budget d p i)) then (0:ℝ) else 2 ^ j) :=
      Finset.sum_comm
    have s2 := Finset.sum_le_sum hG
    have s3 : ∑ j ∈ Finset.range J, (2:ℝ) ^ j * (α * ((Finset.univ.filter
          (fun v => (2 : ℝ) ^ j * nnDist d p < firstVisit d σ v)).card : ℝ)) =
        α * ∑ j ∈ Finset.range J, (2:ℝ) ^ j * ((Finset.univ.filter
          (fun v => (2 : ℝ) ^ j * nnDist d p < firstVisit d σ v)).card : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    linarith
  -- σ side
  have hX : nnDist d p * ∑ j ∈ Finset.range J, (2:ℝ) ^ j * ((Finset.univ.filter
          (fun v => (2 : ℝ) ^ j * nnDist d p < firstVisit d σ v)).card : ℝ) ≤
      2 * walkLatency d σ - nnDist d p * ((Finset.univ.erase p).card : ℝ) := by
    rw [hswap, ← Finset.add_sum_erase _ _ (Finset.mem_univ p), hHp, zero_add, Finset.mul_sum]
    unfold walkLatency
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), hσp, zero_add]
    have := Finset.sum_le_sum (s := Finset.univ.erase p) (fun v hv => hH v (Finset.ne_of_mem_erase hv))
    have hs1 : ∑ v ∈ Finset.univ.erase p, (2 * firstVisit d σ v - nnDist d p) =
        2 * ∑ v ∈ Finset.univ.erase p, firstVisit d σ v -
          ((Finset.univ.erase p).card : ℝ) * nnDist d p := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp
    linarith
  have hX0 : 0 ≤ ∑ j ∈ Finset.range J, (2:ℝ) ^ j * ((Finset.univ.filter
          (fun v => (2 : ℝ) ^ j * nnDist d p < firstVisit d σ v)).card : ℝ) := by
    apply Finset.sum_nonneg; intro j _; positivity
  -- generalize
  generalize ∑ j ∈ Finset.range J, (2:ℝ) ^ j * ((Finset.univ.filter
          (fun v => (2 : ℝ) ^ j * nnDist d p < firstVisit d σ v)).card : ℝ) = X at hWsum hX hX0
  have hac : α ≤ ((⌈α⌉ : ℤ) : ℝ) := Int.le_ceil α
  have hc0 : (0:ℝ) ≤ ((⌈α⌉ : ℤ) : ℝ) := ha.trans hac
  have hm : nnDist d p * ((Finset.univ.erase p).card : ℝ) ≤ ((⌈α⌉ : ℤ) : ℝ) * (nnDist d p * ((Finset.univ.erase p).card : ℝ)) := by
    by_cases hne : (Finset.univ.erase p).Nonempty
    · obtain ⟨v, hv⟩ := hne
      have hapos := l5_alpha_pos hd hA v (Finset.ne_of_mem_erase hv)
      have : (1:ℝ) ≤ ((⌈α⌉ : ℤ) : ℝ) := by exact_mod_cast Int.one_le_ceil_iff.2 hapos
      exact le_mul_of_one_le_left (by positivity) this
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp
  have hδX : 0 ≤ nnDist d p * X := mul_nonneg hδ.le hX0
  have h2 : α * (nnDist d p * X) ≤ ((⌈α⌉ : ℤ) : ℝ) * (nnDist d p * X) :=
    mul_le_mul_of_nonneg_right hac hδX
  have h3 : ((⌈α⌉ : ℤ) : ℝ) * (nnDist d p * ((Finset.univ.erase p).card : ℝ) + nnDist d p * X) ≤
      ((⌈α⌉ : ℤ) : ℝ) * (2 * walkLatency d σ) := mul_le_mul_of_nonneg_left (by linarith) hc0
  have h4 : nnDist d p * (((Finset.univ.erase p).card : ℝ) + α * X) ≤ ((⌈α⌉ : ℤ) : ℝ) * (2 * walkLatency d σ) := by
    nlinarith
  have h5 := mul_le_mul_of_nonneg_left h4 (by linarith : (0:ℝ) ≤ 4 * β)
  calc walkLatency d (doublingWalk d p A J) ≤ 4 * β * nnDist d p * (((Finset.univ.erase p).card : ℝ) + α * X) := hWsum
    _ = 4 * β * (nnDist d p * (((Finset.univ.erase p).card : ℝ) + α * X)) := by ring
    _ ≤ 4 * β * (((⌈α⌉ : ℤ) : ℝ) * (2 * walkLatency d σ)) := h5
    _ = 8 * ((⌈α⌉ : ℤ) : ℝ) * β * walkLatency d σ := by ring

lemma l5_exists_cover {d : V → V → ℝ} {p : V} (hd : IsMetric d) {α β : ℝ} {A : ℝ → List V}
    (hA : IsTSPApprox d p α β A) (j : ℕ)
    (hj : tourLen d (p :: (Finset.univ.erase p).toList) ≤ budget d p j) :
    ∀ v, v ∈ A (budget d p j) := by
  have hF : IsRootedTour p (p :: (Finset.univ.erase p).toList) := by
    refine ⟨rfl, List.nodup_cons.2 ⟨by simp, Finset.nodup_toList _⟩⟩
  have hmiss : missed (p :: (Finset.univ.erase p).toList) ≤ 0 := by
    unfold missed
    rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _
    by_cases hv : v = p
    · subst hv; simp
    · simp [hv]
  obtain ⟨_, _, h3⟩ := hA _ (l5_budget_pos hd p j) 0 ⟨_, hF, hj, hmiss⟩
  rw [Nat.cast_zero, mul_zero] at h3
  exact l5_mem_of_missed h3

lemma l5_stops {d : V → V → ℝ} {p : V} (A : ℝ → List V) (h : ∃ j, ∀ v, v ∈ A (budget d p j)) :
    StopsAt d p A (Nat.find h) :=
  ⟨Nat.find_spec h, fun j hj => Nat.find_min h hj⟩

lemma l5_partA {d : V → V → ℝ} {p : V} (hd : IsMetric d) {α β : ℝ} {A : ℝ → List V}
    (hA : IsTSPApprox d p α β A) :
    ∃ J : ℕ, StopsAt d p A J ∧ IsCoveringWalk p (doublingWalk d p A J) ∧
        ∀ σ : List V, IsCoveringWalk p σ →
          walkLatency d (doublingWalk d p A J) ≤
            8 * ((⌈α⌉ : ℤ) : ℝ) * β * walkLatency d σ := by
  have hex : ∃ j, ∀ v, v ∈ A (budget d p j) := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt
      (tourLen d (p :: (Finset.univ.erase p).toList) / nnDist d p) (by norm_num : (1:ℝ) < 2)
    refine ⟨j, l5_exists_cover hd hA j ?_⟩
    have hδ := l5_nnDist_pos hd p
    rw [div_lt_iff₀ hδ] at hj
    unfold budget
    have : (2:ℝ) ^ j ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  refine ⟨Nat.find hex, l5_stops A hex, ⟨(l5_doublingWalk_tour hd hA _).1, ?_⟩, ?_⟩
  · intro v
    unfold doublingWalk; rw [List.mem_flatMap]
    exact ⟨Nat.find hex, by simp, Nat.find_spec hex v⟩
  · intro σ hσ
    exact l5_main hd hA _ (Nat.find_spec hex) σ hσ

lemma l5_pathLen_le_len {d : V → V → ℝ} (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ u v, d u v ≤ D) :
    ∀ l : List V, pathLen d l ≤ l.length * D
  | [] => by simp [l5_pathLen_nil]
  | [a] => by simp [l5_pathLen_single]; exact hD0
  | u :: v :: t => by
      rw [l5_pathLen_cons2]
      have h1 := l5_pathLen_le_len D hD0 hD (v :: t)
      have h2 := hD u v
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h1 ⊢
      linarith

lemma l5_full_len {d : V → V → ℝ} (p : V) (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ u v, d u v ≤ D) :
    tourLen d (p :: (Finset.univ.erase p).toList) ≤ ((Fintype.card V : ℝ) + 1) * D := by
  simp only [tourLen]
  have h1 := l5_pathLen_le_len D hD0 hD (p :: (Finset.univ.erase p).toList)
  have h2 := hD ((p :: (Finset.univ.erase p).toList).getLast (List.cons_ne_nil _ _)) p
  have hl : (p :: (Finset.univ.erase p).toList).length = Fintype.card V := by
    simp [Finset.card_erase_of_mem (Finset.mem_univ p)]
    have := Fintype.card_pos_iff.2 ⟨p⟩; omega
  rw [hl] at h1
  linarith

lemma l5_size_le (d : V → V → ℚ) (u v : V) : ratSize (d u v) ≤ instSize d := by
  unfold instSize
  exact (Finset.single_le_sum (f := fun v => ratSize (d u v)) (fun v _ => Nat.zero_le _)
    (Finset.mem_univ v)).trans
    (Finset.single_le_sum (f := fun u => ∑ v, ratSize (d u v)) (fun u _ => Nat.zero_le _)
      (Finset.mem_univ u))

lemma l5_card_le_size (d : V → V → ℚ) : Fintype.card V ≤ instSize d := by
  unfold instSize
  rw [← Finset.card_univ, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro u _
  refine le_trans ?_ (Finset.single_le_sum (f := fun v => ratSize (d u v))
    (fun v _ => Nat.zero_le _) (Finset.mem_univ u))
  unfold ratSize; omega

lemma l5_rat_upper (r : ℚ) (hr : 0 ≤ r) (s : ℕ) (hs : ratSize r ≤ s) : r ≤ 2 ^ s := by
  have h1 : r ≤ (r.num : ℚ) := by
    rw [← Rat.mul_den_eq_num r]
    exact le_mul_of_one_le_right hr (by exact_mod_cast r.den_pos)
  have h2 : (r.num : ℚ) ≤ (r.num.natAbs : ℚ) := by
    rw [Nat.cast_natAbs]; exact Int.cast_le.2 (le_abs_self _)
  have h3 : r.num.natAbs < 2 ^ s := by
    have := Nat.lt_size_self r.num.natAbs
    have h4 : Nat.size r.num.natAbs ≤ s := by unfold ratSize at hs; omega
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) h4)
  have h5 : (r.num.natAbs : ℚ) ≤ 2 ^ s := by exact_mod_cast h3.le
  linarith

lemma l5_rat_lower (r : ℚ) (hr : 0 < r) (s : ℕ) (hs : ratSize r ≤ s) : 1 ≤ r * 2 ^ s := by
  have h1 : (1 : ℚ) ≤ r.num := by exact_mod_cast Rat.num_pos.2 hr
  have h3 : r.den < 2 ^ s := by
    have := Nat.lt_size_self r.den
    have h4 : Nat.size r.den ≤ s := by unfold ratSize at hs; omega
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) h4)
  have h5 : (r.den : ℚ) ≤ 2 ^ s := by exact_mod_cast h3.le
  rw [← Rat.mul_den_eq_num r] at h1
  nlinarith

lemma l5_nnDist_rat (d : V → V → ℚ) (p : V) (hd : IsMetric (fun u v => (d u v : ℝ))) :
    1 ≤ nnDist (fun u v => (d u v : ℝ)) p * 2 ^ instSize d := by
  unfold nnDist
  split_ifs with h
  · obtain ⟨v, hv, heq⟩ := Finset.exists_mem_eq_inf' h (fun v => (d p v : ℝ))
    rw [heq]
    simp only [Finset.mem_filter] at hv
    have hpos : (0:ℝ) < d p v := hd.pos p v (Ne.symm hv.2)
    have := l5_rat_lower (d p v) (by exact_mod_cast hpos) _ (l5_size_le d p v)
    exact_mod_cast this
  · rw [one_mul]; exact one_le_pow₀ (by norm_num)

lemma l5_rat_J {V : Type} [Fintype V] [DecidableEq V] (d : V → V → ℚ) (p : V)
    (hd : IsMetric (fun u v => (d u v : ℝ))) {α β : ℝ} {A : ℝ → List V}
    (hA : IsTSPApprox (fun u v => (d u v : ℝ)) p α β A) :
    ∃ J : ℕ, StopsAt (fun u v => (d u v : ℝ)) p A J ∧ J ≤ 3 * instSize d := by
  set s := instSize d with hs
  have hD : ∀ u v, (d u v : ℝ) ≤ 2 ^ s := by
    intro u v
    have h0 : (0:ℝ) ≤ d u v := l5_d_nonneg hd u v
    have := l5_rat_upper (d u v) (by exact_mod_cast h0) s (l5_size_le d u v)
    exact_mod_cast this
  have hcov := l5_exists_cover hd hA (3 * s) (by
    refine (l5_full_len p (2 ^ s) (by positivity) hD).trans ?_
    have hn : (Fintype.card V : ℝ) + 1 ≤ 2 ^ s := by
      have h1 := Nat.lt_two_pow_self (n := Fintype.card V)
      have h2 : 2 ^ Fintype.card V ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (l5_card_le_size d)
      exact_mod_cast (show Fintype.card V + 1 ≤ 2 ^ s by omega)
    have hδ : 1 ≤ nnDist (fun u v => (d u v : ℝ)) p * 2 ^ s := l5_nnDist_rat d p hd
    unfold budget
    have e : (2:ℝ) ^ (3 * s + 1) * nnDist (fun u v => (d u v : ℝ)) p =
        2 * 2 ^ s * 2 ^ s * (nnDist (fun u v => (d u v : ℝ)) p * 2 ^ s) := by ring
    rw [e]
    have hp : (0:ℝ) < 2 ^ s := by positivity
    have k1 := mul_le_mul_of_nonneg_right hn hp.le
    have k2 : (0:ℝ) ≤ 2 ^ s * 2 ^ s := by positivity
    have k3 := mul_le_mul_of_nonneg_left hδ k2
    nlinarith)
  have hex : ∃ j, ∀ v, v ∈ A (budget (fun u v => (d u v : ℝ)) p j) := ⟨_, hcov⟩
  exact ⟨Nat.find hex, l5_stops A hex, Nat.find_min' hex hcov⟩

lemma c4_pcCost_const (d : V → V → ℝ) (c : ℝ) (T : List V) :
    pcCost d (fun _ => c) T = tourLen d T + (missed T : ℝ) * c := by
  unfold pcCost missed
  rw [Finset.sum_const, nsmul_eq_mul]

lemma c4_penalty_nonneg (L : ℝ) (hL : 0 < L) (k : ℕ) : 0 ≤ penalty L k := by
  unfold penalty; split_ifs <;> positivity

lemma c4_tourLen_nonneg {d : V → V → ℝ} (hd : IsMetric d) (T : List V) : 0 ≤ tourLen d T :=
  (l5_pathLen_nonneg hd T).trans (l5_pathLen_le_tourLen hd T)

lemma c4_gw {d : V → V → ℝ} {p : V} (hd : IsMetric d) {O : (V → ℝ) → List V}
    (hO : PCAdmissible d p O) (L : ℝ) (hL : 0 < L) (k : ℕ) (Ts : List V) (hTs : IsRootedTour p Ts)
    (hlen : tourLen d Ts ≤ L) (hmiss : missed Ts ≤ k) :
    tourLen d (O (fun _ => penalty L k)) ≤ 6 * L ∧
      (missed (O (fun _ => penalty L k)) : ℝ) ≤ 3 * k := by
  obtain ⟨_, h2⟩ := hO _ (fun _ => c4_penalty_nonneg L hL k)
  have h := h2 Ts hTs
  rw [c4_pcCost_const, c4_pcCost_const] at h
  have hms : (missed Ts : ℝ) ≤ k := by exact_mod_cast hmiss
  by_cases hk : k = 0
  · subst hk
    have hpe : penalty L 0 = 4 * L := by simp [penalty]
    rw [hpe] at h ⊢
    have ht := c4_tourLen_nonneg hd (O (fun _ => 4 * L))
    have hz : missed Ts = 0 := by omega
    rw [hz, Nat.cast_zero, zero_mul, add_zero] at h
    have hm0 : (0:ℝ) ≤ missed (O (fun _ => 4 * L)) := Nat.cast_nonneg _
    refine ⟨by nlinarith, ?_⟩
    simp only [Nat.cast_zero, mul_zero]
    by_contra hc
    push Not at hc
    have h1 : (1:ℝ) ≤ missed (O (fun _ => 4 * L)) := by
      have : 1 ≤ missed (O (fun _ => 4 * L)) := by
        by_contra h0; push Not at h0
        have : missed (O (fun _ => 4 * L)) = 0 := by omega
        rw [this] at hc; simp at hc
      exact_mod_cast this
    nlinarith
  · have hpe : penalty L k = 2 * L / k := by unfold penalty; rw [if_neg hk]
    rw [hpe] at h ⊢
    have ht := c4_tourLen_nonneg hd (O (fun _ => 2 * L / k))
    have hkpos : (0:ℝ) < k := by
      have : 0 < k := Nat.pos_of_ne_zero hk
      exact_mod_cast this
    have e1 : (missed Ts : ℝ) * (2 * L / k) ≤ 2 * L := by
      rw [mul_div_assoc', div_le_iff₀ hkpos]; nlinarith
    have e3 : 0 ≤ (missed (O (fun _ => 2 * L / k)) : ℝ) * (2 * L / k) := by positivity
    have e2 : (missed (O (fun _ => 2 * L / k)) : ℝ) * (2 * L / k) ≤ 6 * L := by nlinarith
    refine ⟨by nlinarith, ?_⟩
    rw [mul_div_assoc', div_le_iff₀ hkpos] at e2
    nlinarith

lemma c4_missed_add (T : List V) : missed T + T.toFinset.card = Fintype.card V := by
  unfold missed
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (fun v => v ∈ T)
  rw [Finset.card_univ] at hc
  have : Finset.univ.filter (fun v => v ∈ T) = T.toFinset := by ext v; simp
  rw [this] at hc
  omega

lemma c4_struct {d : V → V → ℝ} {p : V} (hd : IsMetric d) {O : (V → ℝ) → List V}
    (hO : PCAdmissible d p O) (L : ℝ) (hL : 0 < L) :
    IsRootedTour p (cor4Approx d p O L) ∧ tourLen d (cor4Approx d p O L) ≤ 6 * L ∧
      ∀ k < Fintype.card V, tourLen d (O (fun _ => penalty L k)) ≤ 6 * L →
        (O (fun _ => penalty L k)).toFinset.card ≤ (cor4Approx d p O L).toFinset.card := by
  unfold cor4Approx
  split
  · next m hm =>
    have hmem := List.argmax_mem hm
    rw [List.mem_filter] at hmem
    obtain ⟨hm1, hm2⟩ := hmem
    rw [List.mem_map] at hm1
    obtain ⟨k', _, rfl⟩ := hm1
    refine ⟨(hO _ (fun _ => c4_penalty_nonneg L hL k')).1, by simpa using hm2, ?_⟩
    intro k hk hlen
    exact List.le_of_mem_argmax (f := fun T : List V => T.toFinset.card)
      (a := O (fun _ => penalty L k)) (List.mem_filter.2 ⟨List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩,
      by simpa using hlen⟩) hm
  · next hnone =>
    rw [List.argmax_eq_none] at hnone
    refine ⟨⟨rfl, List.nodup_singleton p⟩, ?_, ?_⟩
    · simp only [tourLen, l5_pathLen_single, List.getLast_singleton, hd.self, add_zero]; linarith
    · intro k hk hlen
      exfalso
      have : O (fun _ => penalty L k) ∈ ((List.range (Fintype.card V)).map
          (fun k => O (fun _ => penalty L k))).filter (fun T => decide (tourLen d T ≤ 6 * L)) :=
        List.mem_filter.2 ⟨List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩, by simpa using hlen⟩
      rw [hnone] at this; simp at this

lemma c4_main {d : V → V → ℝ} {p : V} (hd : IsMetric d) {O : (V → ℝ) → List V}
    (hO : PCAdmissible d p O) : IsTSPApprox d p 3 6 (cor4Approx d p O) := by
  intro L hL k ⟨Ts, hTs, hlen, hmiss⟩
  obtain ⟨h1, h2, h3⟩ := c4_struct hd hO L hL
  refine ⟨h1, h2, ?_⟩
  by_cases hk : k < Fintype.card V
  · obtain ⟨g1, g2⟩ := c4_gw hd hO L hL k Ts hTs hlen hmiss
    have h4 := h3 k hk g1
    have a1 := c4_missed_add (cor4Approx d p O L)
    have a2 := c4_missed_add (O (fun _ => penalty L k))
    have : missed (cor4Approx d p O L) ≤ missed (O (fun _ => penalty L k)) := by omega
    have : (missed (cor4Approx d p O L) : ℝ) ≤ missed (O (fun _ => penalty L k)) := by
      exact_mod_cast this
    linarith
  · have : missed (cor4Approx d p O L) ≤ Fintype.card V := Finset.card_filter_le _ _
    have : (missed (cor4Approx d p O L) : ℝ) ≤ k := by exact_mod_cast (show _ ≤ k by omega)
    have : (0:ℝ) ≤ k := Nat.cast_nonneg _
    linarith

lemma t6_size_mul (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

lemma t6_size_pow (M : ℕ) : Nat.size (2 ^ M) ≤ M + 1 := by
  rw [Nat.size_le]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)

lemma t6_size_self (K : ℕ) : Nat.size K ≤ K := by
  rw [Nat.size_le]; exact Nat.lt_two_pow_self

lemma t6_ratSize_div (x : ℤ) (y : ℕ) (hy : 0 < y) :
    ratSize ((x : ℚ) / (y : ℚ)) ≤ 1 + Nat.size x.natAbs + Nat.size y := by
  have e : (x : ℚ) / (y : ℚ) = Rat.divInt x y := by rw [Rat.divInt_eq_div]; push_cast; rfl
  rw [e]
  have h1 : (Rat.divInt x y).num ∣ x := Rat.num_dvd x (by exact_mod_cast hy.ne')
  have h2 : ((Rat.divInt x y).den : ℤ) ∣ (y : ℤ) := Rat.den_dvd x y
  have hn : (Rat.divInt x y).num.natAbs ≤ x.natAbs := by
    by_cases hx : x = 0
    · subst hx; simp
    · exact Nat.le_of_dvd (Int.natAbs_pos.2 hx) (Int.natAbs_dvd_natAbs.2 h1)
  have hd : (Rat.divInt x y).den ≤ y := Nat.le_of_dvd hy (Int.natCast_dvd_natCast.1 h2)
  unfold ratSize
  have := Nat.size_le_size hn
  have := Nat.size_le_size hd
  omega

lemma t6_ratSize_scaled (δ : ℚ) (M K : ℕ) (hK : 0 < K) :
    ratSize (2 ^ M * δ / K) ≤ 1 + (M + 1) + ratSize δ + Nat.size K := by
  have e : (2 ^ M * δ / K : ℚ) = (((2 ^ M * δ.num : ℤ) : ℚ)) / ((δ.den * K : ℕ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den δ]
    push_cast
    have : (δ.den : ℚ) ≠ 0 := by exact_mod_cast δ.den_pos.ne'
    have : (K : ℚ) ≠ 0 := by exact_mod_cast hK.ne'
    field_simp
  rw [e]
  refine (t6_ratSize_div _ _ (Nat.mul_pos δ.den_pos hK)).trans ?_
  rw [Int.natAbs_mul, Int.natAbs_pow]
  have h1 := t6_size_mul ((2 : ℤ).natAbs ^ M) δ.num.natAbs
  have h2 := t6_size_mul δ.den K
  have h3 : Nat.size ((2 : ℤ).natAbs ^ M) ≤ M + 1 := t6_size_pow M
  unfold ratSize
  omega

lemma t6_nnDist_rat {V : Type} [Fintype V] [DecidableEq V] (d : V → V → ℚ) (p : V) :
    ∃ δ : ℚ, (δ : ℝ) = nnDist (fun u v => (d u v : ℝ)) p ∧ ratSize δ ≤ instSize d + 3 := by
  unfold nnDist
  split_ifs with h
  · obtain ⟨v, _, heq⟩ := Finset.exists_mem_eq_inf' h (fun v => (d p v : ℝ))
    refine ⟨d p v, heq.symm, ?_⟩
    have := l5_size_le d p v; omega
  · refine ⟨1, by simp, ?_⟩
    have : ratSize 1 = 3 := by decide
    omega

lemma t6_penalty {V : Type} [Fintype V] [DecidableEq V] (d : V → V → ℚ) (p : V) (j k : ℕ)
    (hj : j ≤ 3 * instSize d) (hk : k < Fintype.card V) :
    ∃ r : ℚ, (r : ℝ) = penalty (budget (fun u v => (d u v : ℝ)) p j) k ∧
      ratSize r ≤ 5 * instSize d + 9 := by
  obtain ⟨δ, hδ, hsz⟩ := t6_nnDist_rat d p
  have hn := l5_card_le_size d
  by_cases hk0 : k = 0
  · refine ⟨2 ^ (j + 3) * δ / (1 : ℕ), ?_, ?_⟩
    · unfold penalty budget; rw [if_pos hk0, ← hδ]; push_cast; ring
    · have := t6_ratSize_scaled δ (j + 3) 1 one_pos
      have h1 : Nat.size 1 = 1 := by decide
      omega
  · refine ⟨2 ^ (j + 2) * δ / (k : ℕ), ?_, ?_⟩
    · unfold penalty budget; rw [if_neg hk0, ← hδ]; push_cast; ring
    · have := t6_ratSize_scaled δ (j + 2) k (Nat.pos_of_ne_zero hk0)
      have := t6_size_self k
      omega
end L5aux

theorem solution :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (d : V → V → ℝ) (p : V), IsMetric d →
      ∀ O : (V → ℝ) → List V, PCAdmissible d p O →
      ∃ J : ℕ, StopsAt d p (cor4Approx d p O) J ∧
        IsCoveringWalk p (doublingWalk d p (cor4Approx d p O) J) ∧
        ∀ σ : List V, IsCoveringWalk p σ →
          walkLatency d (doublingWalk d p (cor4Approx d p O) J) ≤ 144 * walkLatency d σ) ∧
    (∃ q : Polynomial ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (d : V → V → ℚ) (p : V),
      IsMetric (fun u v => (d u v : ℝ)) →
      ∀ O : (V → ℝ) → List V, PCAdmissible (fun u v => (d u v : ℝ)) p O →
      ∃ J : ℕ, StopsAt (fun u v => (d u v : ℝ)) p (cor4Approx (fun u v => (d u v : ℝ)) p O) J ∧
        (J + 1) * Fintype.card V ≤ q.eval (instSize d) ∧
        ∀ j ≤ J, ∀ k < Fintype.card V, ∃ r : ℚ,
          (r : ℝ) = penalty (budget (fun u v => (d u v : ℝ)) p j) k ∧
          ratSize r ≤ q.eval (instSize d)) := by
  refine ⟨?_, ⟨3 * Polynomial.X * Polynomial.X + 10 * Polynomial.X + 10, ?_⟩⟩
  · intro V _ _ d p hd O hO
    obtain ⟨J, h1, h2, h3⟩ := l5_partA hd (c4_main hd hO)
    refine ⟨J, h1, h2, fun σ hσ => ?_⟩
    have := h3 σ hσ
    have e : ((⌈(3:ℝ)⌉ : ℤ) : ℝ) = 3 := by norm_num
    rw [e] at this
    linarith
  · intro V _ _ d p hd O hO
    obtain ⟨J, hJ, hle⟩ := l5_rat_J d p hd (c4_main hd hO)
    have hn := l5_card_le_size d
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    refine ⟨J, hJ, ?_, ?_⟩
    · have := Nat.mul_le_mul (show J + 1 ≤ 3 * instSize d + 1 by omega) hn
      nlinarith
    · intro j hj k hk
      obtain ⟨r, hr, hs⟩ := t6_penalty d p j k (by omega) hk
      exact ⟨r, hr, by nlinarith⟩
