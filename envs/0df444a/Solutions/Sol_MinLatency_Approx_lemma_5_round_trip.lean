-- Prove2me | solution 1 for MinLatency.Approx.lemma_5_round_trip
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:59:54.809978+00:00
-- url     : https://prove2.me/submissions/4b4a0a96-882a-4ba7-81ea-ade247398682

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

end L5aux

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (d : V → V → ℝ) (p : V) (hd : IsMetric d) (α β : ℝ) (A : ℝ → List V)
    (hA : IsTSPApprox d p α β A) (σ : List V) (hσ : IsCoveringWalk p σ)
    (j J : ℕ) (hjJ : j ≤ J) :
    (Fintype.card V : ℝ) - α * ((Finset.univ.filter
          (fun v => (2 : ℝ) ^ j * nnDist d p < firstVisit d σ v)).card : ℝ)
        ≤ ((Finset.univ.filter (fun v => ∃ i ≤ j, v ∈ A (budget d p i))).card : ℝ) ∧
      ∀ v, (∃ i ≤ j, v ∈ A (budget d p i)) →
        firstVisit d (doublingWalk d p A J) v ≤ β * (2 : ℝ) ^ (j + 2) * nnDist d p :=
  ⟨l5_part1 hd hA σ hσ j, fun v hv => l5_part2 hd hA j J hjJ v hv⟩
