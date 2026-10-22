-- Prove2me | solution 1 for LeightonRao.Directed.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:16:22.275092+00:00
-- url     : https://prove2.me/submissions/a360dc33-c7e7-4fa0-819d-60a597c99fa9

import Mathlib
import Definitions.Def_LeightonRao_Directed_Setting



namespace LeightonRao.Directed

variable {V : Type} [Fintype V] [DecidableEq V]

lemma diLen_nil (d : V → V → ℝ) : diLen d [] = 0 := by simp [diLen]
lemma diLen_single (d : V → V → ℝ) (a : V) : diLen d [a] = 0 := by simp [diLen]
lemma diLen_cons2 (d : V → V → ℝ) (a b : V) (l : List V) :
    diLen d (a :: b :: l) = d a b + diLen d (b :: l) := by simp [diLen]

lemma diLen_nonneg {d : V → V → ℝ} (hd : ∀ u v, 0 ≤ d u v) (l : List V) : 0 ≤ diLen d l := by
  unfold diLen
  apply List.sum_nonneg
  intro x hx
  obtain ⟨⟨a, b⟩, -, rfl⟩ := List.mem_map.1 hx
  exact hd a b

lemma walk_single (N : DiNetwork V) (u : V) : IsDiWalk N [u] u u := by
  simp [IsDiWalk]

lemma walk_cons {N : DiNetwork V} {l : List V} {i j v : V} (hC : 0 < N.C i j)
    (h : IsDiWalk N l j v) : IsDiWalk N (i :: l) i v := by
  obtain ⟨h1, h2, h3⟩ := h
  cases l with
  | nil => simp at h1
  | cons a l =>
    simp at h1; subst h1
    refine ⟨rfl, ?_, ?_⟩
    · simpa using h2
    · exact List.IsChain.cons_cons hC h3

lemma len_cons_walk {N : DiNetwork V} (d : V → V → ℝ) {l : List V} {i j v : V}
    (h : IsDiWalk N l j v) : diLen d (i :: l) = d i j + diLen d l := by
  obtain ⟨h1, -, -⟩ := h
  cases l with
  | nil => simp at h1
  | cons a l => simp at h1; subst h1; exact diLen_cons2 d i a l

lemma walk_append {N : DiNetwork V} (d : V → V → ℝ) {l1 l2 : List V} {u v w : V}
    (h1 : IsDiWalk N l1 u v) (h2 : IsDiWalk N l2 v w) :
    IsDiWalk N (l1 ++ l2.tail) u w ∧ diLen d (l1 ++ l2.tail) = diLen d l1 + diLen d l2 := by
  induction l1 generalizing u with
  | nil => simp [IsDiWalk] at h1
  | cons a rest ih =>
    obtain ⟨ha, hl, hc⟩ := h1
    simp at ha; subst ha
    cases rest with
    | nil =>
      simp at hl; subst hl
      have h2a := h2.1
      cases l2 with
      | nil => simp at h2a
      | cons b l2 =>
        simp at h2a; subst h2a
        simp only [List.tail_cons, List.singleton_append]
        exact ⟨h2, by rw [diLen_single]; ring⟩
    | cons b rest =>
      have hab : 0 < N.C a b := (List.isChain_cons_cons.1 hc).1
      have hw : IsDiWalk N (b :: rest) b v :=
        ⟨rfl, by simpa using hl, (List.isChain_cons_cons.1 hc).2⟩
      obtain ⟨ih1, ih2⟩ := ih hw
      refine ⟨?_, ?_⟩
      · exact walk_cons hab ih1
      · rw [List.cons_append, len_cons_walk d ih1, ih2, diLen_cons2]; ring

lemma walk_snoc {N : DiNetwork V} (d : V → V → ℝ) {l : List V} {u i j : V}
    (h : IsDiWalk N l u i) (hC : 0 < N.C i j) :
    IsDiWalk N (l ++ [j]) u j ∧ diLen d (l ++ [j]) = diLen d l + d i j := by
  have h2 : IsDiWalk N [i, j] i j := walk_cons hC (walk_single N j)
  have := walk_append d h h2
  simpa [diLen_cons2, diLen_single] using this

def Reach (N : DiNetwork V) (u v : V) : Prop := ∃ l, IsDiWalk N l u v

lemma bdd_len (N : DiNetwork V) {d : V → V → ℝ} (hd : ∀ u v, 0 ≤ d u v) (u v : V) :
    BddBelow (Set.range (fun l : {l : List V // IsDiWalk N l u v} => diLen d l.1)) :=
  ⟨0, by rintro _ ⟨x, rfl⟩; exact diLen_nonneg hd _⟩

lemma diDist_nonneg (N : DiNetwork V) {d : V → V → ℝ} (hd : ∀ u v, 0 ≤ d u v) (u v : V) :
    0 ≤ diDist N d u v := Real.iInf_nonneg (fun l => diLen_nonneg hd _)

lemma diDist_le (N : DiNetwork V) {d : V → V → ℝ} (hd : ∀ u v, 0 ≤ d u v) {l : List V} {u v : V}
    (h : IsDiWalk N l u v) : diDist N d u v ≤ diLen d l :=
  ciInf_le (bdd_len N hd u v) ⟨l, h⟩

lemma diDist_self (N : DiNetwork V) {d : V → V → ℝ} (hd : ∀ u v, 0 ≤ d u v) (u : V) :
    diDist N d u u = 0 :=
  le_antisymm (by simpa [diLen_single] using diDist_le N hd (walk_single N u))
    (diDist_nonneg N hd u u)

lemma exists_walk_lt (N : DiNetwork V) (d : V → V → ℝ) {u v : V} (h : Reach N u v)
    {b : ℝ} (hb : diDist N d u v < b) : ∃ l, IsDiWalk N l u v ∧ diLen d l < b := by
  obtain ⟨l, hl⟩ := h
  haveI : Nonempty {l : List V // IsDiWalk N l u v} := ⟨⟨l, hl⟩⟩
  obtain ⟨⟨l', hl'⟩, h'⟩ := exists_lt_of_ciInf_lt hb
  exact ⟨l', hl', h'⟩

lemma diDist_tri (N : DiNetwork V) {d : V → V → ℝ} (hd : ∀ u v, 0 ≤ d u v) {u v w : V}
    (h1 : Reach N u v) (h2 : Reach N v w) :
    diDist N d u w ≤ diDist N d u v + diDist N d v w := by
  obtain ⟨l1, hl1⟩ := h1
  obtain ⟨l2, hl2⟩ := h2
  haveI : Nonempty {l : List V // IsDiWalk N l u v} := ⟨⟨l1, hl1⟩⟩
  haveI : Nonempty {l : List V // IsDiWalk N l v w} := ⟨⟨l2, hl2⟩⟩
  have key : ∀ (a : {l : List V // IsDiWalk N l u v}) (b : {l : List V // IsDiWalk N l v w}),
      diDist N d u w ≤ diLen d a.1 + diLen d b.1 := by
    intro a b
    obtain ⟨hw, hl⟩ := walk_append d a.2 b.2
    rw [← hl]; exact diDist_le N hd hw
  have : ∀ a : {l : List V // IsDiWalk N l u v}, diDist N d u w - diDist N d v w ≤ diLen d a.1 := by
    intro a
    have : diDist N d u w - diLen d a.1 ≤ diDist N d v w :=
      le_ciInf (fun b => by linarith [key a b])
    linarith
  have := le_ciInf this
  unfold diDist at *
  linarith

lemma reach_snoc {N : DiNetwork V} {u i j : V} (h : Reach N u i) (hC : 0 < N.C i j) : Reach N u j := by
  obtain ⟨l, hl⟩ := h
  exact ⟨_, (walk_snoc (fun _ _ => (0:ℝ)) hl hC).1⟩

lemma reach_cons {N : DiNetwork V} {i j v : V} (h : Reach N j v) (hC : 0 < N.C i j) : Reach N i v := by
  obtain ⟨l, hl⟩ := h
  exact ⟨_, walk_cons hC hl⟩

lemma reach_edge {N : DiNetwork V} {i j : V} (hC : 0 < N.C i j) : Reach N i j :=
  ⟨_, walk_cons hC (walk_single N j)⟩

lemma diDist_edge (N : DiNetwork V) {d : V → V → ℝ} (hd : ∀ u v, 0 ≤ d u v) {i j : V}
    (hC : 0 < N.C i j) : diDist N d i j ≤ d i j := by
  have := diDist_le N hd (walk_cons hC (walk_single N j)) (d := d)
  rwa [diLen_cons2, diLen_single, add_zero] at this

lemma reach_of_conn {N : DiNetwork V} (hconn : IsStronglyConnectedNet N) (u v : V) : Reach N u v := by
  classical
  by_contra hne
  set U : Finset V := Finset.univ.filter (fun x => Reach N u x) with hU
  have hu : u ∈ U := by simp [hU]; exact ⟨_, walk_single N u⟩
  have hv : v ∈ Uᶜ := by simp [hU]; exact hne
  have hpos := hconn U ⟨u, hu⟩ ⟨v, hv⟩
  unfold diCutCap at hpos
  have h0 : ∀ i ∈ U, ∀ j ∈ Uᶜ, N.C i j = 0 := by
    intro i hi j hj
    rcases (N.C_nonneg i j).lt_or_eq with h | h
    · exfalso
      simp [hU] at hi hj
      exact hj (reach_snoc hi h)
    · exact h.symm
  have : ∑ i ∈ U, ∑ j ∈ Uᶜ, N.C i j = 0 :=
    Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun j hj => h0 i hi j hj))
  linarith


/-! ### Breakpoints -/

noncomputable def nx (P : Finset ℝ) (b t : ℝ) : ℝ :=
  (insert b (P.filter (fun s => t < s))).min' (Finset.insert_nonempty _ _)

lemma nx_le (P : Finset ℝ) (b t : ℝ) : nx P b t ≤ b :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

lemma lt_nx {P : Finset ℝ} {b t : ℝ} (ht : t < b) : t < nx P b t := by
  unfold nx
  rw [Finset.lt_min'_iff]
  intro y hy
  rw [Finset.mem_insert, Finset.mem_filter] at hy
  rcases hy with rfl | ⟨_, h⟩
  · exact ht
  · exact h

lemma nx_le_of {P : Finset ℝ} {b t s : ℝ} (hs : s ∈ P) (hts : t < s) : nx P b t ≤ s :=
  Finset.min'_le _ _ (by simp [hs, hts])

lemma telescope (h : ℝ → ℝ) (P : Finset ℝ) : ∀ (b : ℝ), (∀ t ∈ P, t < b) → ∀ hP : P.Nonempty,
    ∑ t ∈ P, (h (nx P b t) - h t) = h b - h (P.min' hP) := by
  refine Finset.induction_on_max P ?_ ?_
  · intro b _ hP; exact absurd hP (by simp)
  · intro a s has ih b hb hP
    have hab : a < b := hb a (Finset.mem_insert_self a s)
    have has' : a ∉ s := fun h => lt_irrefl a (has a h)
    rw [Finset.sum_insert has']
    have hnxa : nx (insert a s) b a = b := by
      apply le_antisymm (nx_le _ _ _)
      unfold nx; apply Finset.le_min'; intro y hy
      rw [Finset.mem_insert, Finset.mem_filter] at hy
      rcases hy with rfl | ⟨hy1, hy2⟩
      · exact le_refl _
      · exfalso
        rw [Finset.mem_insert] at hy1
        rcases hy1 with rfl | hy1
        · exact lt_irrefl _ hy2
        · exact lt_asymm hy2 (has y hy1)
    rw [hnxa]
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs; simp
    · have heq : ∀ t ∈ s, nx (insert a s) b t = nx s a t := by
        intro t ht
        have hta : t < a := has t ht
        apply le_antisymm
        · unfold nx
          apply Finset.min'_le
          have hm := Finset.min'_mem (insert a (s.filter (fun x => t < x))) (Finset.insert_nonempty _ _)
          rw [Finset.mem_insert, Finset.mem_filter] at hm ⊢
          rcases hm with hm | ⟨hm1, hm2⟩
          · right; rw [hm]; exact ⟨Finset.mem_insert_self _ _, hta⟩
          · right; exact ⟨Finset.mem_insert_of_mem hm1, hm2⟩
        · unfold nx
          apply Finset.le_min'
          intro y hy
          rw [Finset.mem_insert, Finset.mem_filter] at hy
          rcases hy with rfl | ⟨hy1, hy2⟩
          · exact (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans hab.le
          · rw [Finset.mem_insert] at hy1
            rcases hy1 with rfl | hy1
            · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)
            · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hy1, hy2⟩))
      rw [Finset.sum_congr rfl (fun t ht => by rw [heq t ht]), ih a has hs]
      have hmin : (insert a s).min' hP = s.min' hs := by
        rw [Finset.min'_insert a s hs]
        exact min_eq_right ((Finset.min'_le _ _ hs.choose_spec).trans (has _ hs.choose_spec).le)
      rw [hmin]; ring

lemma phi_mono {a b s s' : ℝ} (h : s ≤ s') :
    max 0 (min s a - min s b) ≤ max 0 (min s' a - min s' b) := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-! ### Sweep (Lemma 15 core) -/

theorem sweep (C d : V → V → ℝ) (hC : ∀ i j, 0 ≤ C i j) (hd : ∀ i j, 0 ≤ d i j)
    (δ : V → ℝ) (hδ : ∀ u, 0 ≤ δ u) (T : Finset V) (hT0 : ∀ t ∈ T, δ t = 0)
    (hedge : ∀ i j, 0 < C i j → δ j ≤ δ i + d i j)
    (hn : 2 ≤ Fintype.card V)
    (hcard : 2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ))
    (hsum : 1 / (4 * (Fintype.card V : ℝ)) ≤ ∑ u ∈ Tᶜ, δ u) :
    ∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧
      ∑ i ∈ U, ∑ j ∈ Uᶜ, C i j ≤ 12 * (∑ i, ∑ j, C i j * d i j) * ((U.card : ℝ) * (Uᶜ.card : ℝ)) := by
  classical
  have hn0 : (0:ℝ) < (Fintype.card V : ℝ) := by
    have : (2:ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
    linarith
  set W := ∑ i, ∑ j, C i j * d i j with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (hC i j) (hd i j)))
  clear_value W
  haveI : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]
    have : (0:ℝ) < (T.card : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨um, -, hum⟩ := Finset.exists_max_image Finset.univ δ Finset.univ_nonempty
  set M := δ um with hMdef
  have hpos : 0 < ∑ u ∈ Tᶜ, δ u := lt_of_lt_of_le (by positivity) hsum
  have hM : 0 < M := by
    by_contra hc; push_neg at hc
    have : ∑ u ∈ Tᶜ, δ u ≤ 0 := Finset.sum_nonpos (fun u _ => (hum u (Finset.mem_univ _)).trans hc)
    linarith
  set P : Finset ℝ := insert 0 ((Finset.univ.image δ).filter (fun x => x < M)) with hPdef
  have hPlt : ∀ t ∈ P, t < M := by
    intro t ht
    rw [hPdef, Finset.mem_insert, Finset.mem_filter] at ht
    rcases ht with rfl | ⟨_, h⟩
    · exact hM
    · exact h
  have hP0 : (0:ℝ) ∈ P := Finset.mem_insert_self _ _
  have hPne : P.Nonempty := ⟨0, hP0⟩
  have hPnn : ∀ t ∈ P, 0 ≤ t := by
    intro t ht
    rw [hPdef, Finset.mem_insert, Finset.mem_filter, Finset.mem_image] at ht
    rcases ht with rfl | ⟨⟨u, _, rfl⟩, _⟩
    · exact le_refl _
    · exact hδ u
  have hPmin : P.min' hPne = 0 :=
    le_antisymm (Finset.min'_le _ _ hP0) (Finset.le_min' _ _ _ hPnn)
  have hgap : ∀ t ∈ P, ∀ u, t < δ u → nx P M t ≤ δ u := by
    intro t ht u hu
    by_cases hlt : δ u < M
    · exact nx_le_of (by rw [hPdef]; simp [hlt]) hu
    · exact (nx_le P M t).trans (not_lt.1 hlt)
  set Ut : ℝ → Finset V := fun t => Finset.univ.filter (fun u => δ u ≤ t) with hUt
  have hTU : ∀ t ∈ P, T ⊆ Ut t := by
    intro t ht x hx
    simp only [hUt, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hT0 x hx]; exact hPnn t ht
  have hUne : ∀ t ∈ P, (Ut t).Nonempty := fun t ht => hTne.mono (hTU t ht)
  have hUcne : ∀ t ∈ P, (Ut t)ᶜ.Nonempty := by
    intro t ht
    refine ⟨um, ?_⟩
    simp only [hUt, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact hPlt t ht
  by_contra hcon
  push_neg at hcon
  set Φ : ℝ → ℝ := fun s => ∑ i, ∑ j, C i j * max 0 (min s (δ j) - min s (δ i)) with hΦ
  set Ψ : ℝ → ℝ := fun s => ∑ u, min s (δ u) with hΨ
  have hA : ∀ t ∈ P, (nx P M t - t) * ∑ i ∈ Ut t, ∑ j ∈ (Ut t)ᶜ, C i j ≤ Φ (nx P M t) - Φ t := by
    intro t ht
    have hnx := lt_nx (P := P) (hPlt t ht)
    rw [Finset.mul_sum]
    calc ∑ i ∈ Ut t, (nx P M t - t) * ∑ j ∈ (Ut t)ᶜ, C i j
        = ∑ i ∈ Ut t, ∑ j ∈ (Ut t)ᶜ, C i j * (max 0 (min (nx P M t) (δ j) - min (nx P M t) (δ i))
            - max 0 (min t (δ j) - min t (δ i))) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [hUt, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi hj
          have hj' := hgap t ht j hj
          rw [min_eq_left hj', min_eq_right (by linarith), min_eq_left (le_of_lt hj), min_eq_right hi,
            max_eq_right (by linarith), max_eq_right (by linarith)]
          ring
      _ ≤ ∑ i ∈ Ut t, ∑ j, C i j * (max 0 (min (nx P M t) (δ j) - min (nx P M t) (δ i))
            - max 0 (min t (δ j) - min t (δ i))) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro j _ _
          exact mul_nonneg (hC i j) (sub_nonneg.2 (phi_mono hnx.le))
      _ ≤ ∑ i, ∑ j, C i j * (max 0 (min (nx P M t) (δ j) - min (nx P M t) (δ i))
            - max 0 (min t (δ j) - min t (δ i))) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro i _ _
          exact Finset.sum_nonneg (fun j _ => mul_nonneg (hC i j) (sub_nonneg.2 (phi_mono hnx.le)))
      _ = Φ (nx P M t) - Φ t := by
          simp only [hΦ, ← Finset.sum_sub_distrib, mul_sub]
  have hB : ∀ t ∈ P, Ψ (nx P M t) - Ψ t = (nx P M t - t) * ((Ut t)ᶜ.card : ℝ) := by
    intro t ht
    have hnx := lt_nx (P := P) (hPlt t ht)
    have key : ∀ u, min (nx P M t) (δ u) - min t (δ u) = if t < δ u then nx P M t - t else 0 := by
      intro u
      split_ifs with h
      · rw [min_eq_left (hgap t ht u h), min_eq_left h.le]
      · push_neg at h
        rw [min_eq_right (h.trans hnx.le), min_eq_right h]; ring
    simp only [hΨ, ← Finset.sum_sub_distrib, key, Finset.sum_ite, Finset.sum_const,
      Finset.sum_const_zero, nsmul_eq_mul, add_zero]
    rw [mul_comm]
    congr 2
    simp only [hUt, Finset.compl_filter, not_le]
    ring
  have hΦt : ∑ t ∈ P, (Φ (nx P M t) - Φ t) = Φ M - Φ 0 := by rw [telescope Φ P M hPlt hPne, hPmin]
  have hΨt : ∑ t ∈ P, (Ψ (nx P M t) - Ψ t) = Ψ M - Ψ 0 := by rw [telescope Ψ P M hPlt hPne, hPmin]
  have hΦ0 : Φ 0 = 0 := by
    simp only [hΦ]
    apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro j _
    rw [min_eq_left (hδ j), min_eq_left (hδ i)]; simp
  have hΦM : Φ M ≤ W := by
    simp only [hΦ, hW]
    apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
    rw [min_eq_right (hum j (Finset.mem_univ _)), min_eq_right (hum i (Finset.mem_univ _))]
    rcases (hC i j).lt_or_eq with h | h
    · apply mul_le_mul_of_nonneg_left _ (hC i j)
      exact max_le (hd i j) (by linarith [hedge i j h])
    · rw [← h]; simp
  have hΨ0 : Ψ 0 = 0 := by
    simp only [hΨ]; apply Finset.sum_eq_zero; intro u _; exact min_eq_left (hδ u)
  have hΨM : Ψ M = ∑ u, δ u := by
    simp only [hΨ]; apply Finset.sum_congr rfl; intro u _; exact min_eq_right (hum u (Finset.mem_univ _))
  -- upper bound
  have hup : ∑ t ∈ P, (nx P M t - t) * ∑ i ∈ Ut t, ∑ j ∈ (Ut t)ᶜ, C i j ≤ W := by
    calc _ ≤ ∑ t ∈ P, (Φ (nx P M t) - Φ t) := Finset.sum_le_sum hA
      _ ≤ W := by rw [hΦt, hΦ0]; linarith
  have hstrict : ∑ t ∈ P, (nx P M t - t) * (12 * W * (((Ut t).card : ℝ) * ((Ut t)ᶜ.card : ℝ))) <
      ∑ t ∈ P, (nx P M t - t) * ∑ i ∈ Ut t, ∑ j ∈ (Ut t)ᶜ, C i j :=
    Finset.sum_lt_sum_of_nonempty hPne (fun t ht =>
      mul_lt_mul_of_pos_left (hcon _ (hUne t ht) (hUcne t ht)) (sub_pos.2 (lt_nx (hPlt t ht))))
  have hlow : 12 * W * ((T.card : ℝ) * ∑ u, δ u) ≤
      ∑ t ∈ P, (nx P M t - t) * (12 * W * (((Ut t).card : ℝ) * ((Ut t)ᶜ.card : ℝ))) := by
    have : ∑ u, δ u = ∑ t ∈ P, (nx P M t - t) * ((Ut t)ᶜ.card : ℝ) := by
      rw [← hΨM, ← sub_zero (Ψ M), ← hΨ0, ← hΨt]
      exact Finset.sum_congr rfl hB
    rw [this, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    have hg : 0 ≤ nx P M t - t := sub_nonneg.2 (lt_nx (hPlt t ht)).le
    have hc : (T.card : ℝ) ≤ ((Ut t).card : ℝ) := by exact_mod_cast Finset.card_le_card (hTU t ht)
    have h1 : 0 ≤ 12 * W := by linarith
    have h2 : (0:ℝ) ≤ ((Ut t)ᶜ.card : ℝ) := by positivity
    calc 12 * W * ((T.card : ℝ) * ((nx P M t - t) * ((Ut t)ᶜ.card : ℝ)))
        = (nx P M t - t) * (12 * W * ((T.card : ℝ) * ((Ut t)ᶜ.card : ℝ))) := by ring
      _ ≤ (nx P M t - t) * (12 * W * (((Ut t).card : ℝ) * ((Ut t)ᶜ.card : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hg
          apply mul_le_mul_of_nonneg_left _ h1
          exact mul_le_mul_of_nonneg_right hc h2
  have hsix : (1:ℝ) / 6 ≤ (T.card : ℝ) * ∑ u, δ u := by
    have hs : ∑ u ∈ Tᶜ, δ u ≤ ∑ u, δ u :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun u _ _ => hδ u)
    have hT' : 2 * (Fintype.card V : ℝ) / 3 ≤ (T.card : ℝ) := by linarith
    calc (1:ℝ) / 6 = (2 * (Fintype.card V : ℝ) / 3) * (1 / (4 * (Fintype.card V : ℝ))) := by
            field_simp; ring
      _ ≤ (T.card : ℝ) * ∑ u, δ u := by
            apply mul_le_mul hT' (hsum.trans hs) (by positivity) (by positivity)
  have : 12 * W * (1/6) ≤ 12 * W * ((T.card : ℝ) * ∑ u, δ u) :=
    mul_le_mul_of_nonneg_left hsix (by linarith)
  linarith


lemma ratio_le_of (N : DiNetwork V) {U : Finset V} (hU : U.Nonempty) (hUc : Uᶜ.Nonempty) {K : ℝ}
    (h : diCutCap N U ≤ K * ((U.card : ℝ) * (Uᶜ.card : ℝ))) : diRatio N U ≤ K := by
  unfold diRatio
  have h1 : (0:ℝ) < U.card := by exact_mod_cast hU.card_pos
  have h2 : (0:ℝ) < Uᶜ.card := by exact_mod_cast hUc.card_pos
  rw [div_le_iff₀ (mul_pos h1 h2)]; exact h

lemma bdd_fin {ι : Type} [Finite ι] (f : ι → ℝ) : BddBelow (Set.range f) := (Set.finite_range f).bddBelow

theorem lemma_15_core (N : DiNetwork V)
    (hn : 2 ≤ Fintype.card V) (hconn : IsStronglyConnectedNet N)
    (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) (T : Finset V)
    (hT : 2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ))
    (hsum : 1 / (4 * (Fintype.card V : ℝ)) ≤ ∑ u ∈ Tᶜ, diDistFrom N d T u ∨
      1 / (4 * (Fintype.card V : ℝ)) ≤ ∑ u ∈ Tᶜ, diDistTo N d u T) :
    ∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧ diRatio N U ≤ 12 * diTotalWeight N d := by
  classical
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]
    have : (2:ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
    have : (0:ℝ) < (T.card : ℝ) := by linarith
    exact_mod_cast this
  haveI : Nonempty T := ⟨⟨hTne.choose, hTne.choose_spec⟩⟩
  rcases hsum with hs | hs
  · obtain ⟨U, hU, hUc, hcut⟩ := sweep N.C d N.C_nonneg hd (fun u => diDistFrom N d T u)
      (fun u => Real.iInf_nonneg (fun t => diDist_nonneg N hd _ _)) T
      (by
        intro t ht
        apply le_antisymm _ (Real.iInf_nonneg (fun t => diDist_nonneg N hd _ _))
        have := ciInf_le (bdd_fin (fun s : T => diDist N d s t)) ⟨t, ht⟩
        simpa [diDist_self N hd] using this)
      (by
        intro i j hC
        show diDistFrom N d T j ≤ diDistFrom N d T i + d i j
        have : ∀ t : T, diDistFrom N d T j - d i j ≤ diDist N d t i := by
          intro t
          have h1 : diDistFrom N d T j ≤ diDist N d t j := ciInf_le (bdd_fin _) t
          have h2 := diDist_tri N hd (reach_of_conn hconn t i) (reach_edge hC) (d := d)
          have h3 := diDist_edge N hd hC (d := d)
          linarith
        have := le_ciInf this
        unfold diDistFrom at this ⊢; linarith)
      hn hT hs
    exact ⟨U, hU, hUc, ratio_le_of N hU hUc (by unfold diCutCap diTotalWeight; exact hcut)⟩
  · obtain ⟨U, hU, hUc, hcut⟩ := sweep (fun i j => N.C j i) (fun i j => d j i)
      (fun i j => N.C_nonneg j i) (fun i j => hd j i) (fun u => diDistTo N d u T)
      (fun u => Real.iInf_nonneg (fun t => diDist_nonneg N hd _ _)) T
      (by
        intro t ht
        apply le_antisymm _ (Real.iInf_nonneg (fun t => diDist_nonneg N hd _ _))
        have := ciInf_le (bdd_fin (fun s : T => diDist N d t s)) ⟨t, ht⟩
        simpa [diDist_self N hd] using this)
      (by
        intro i j hC
        show diDistTo N d j T ≤ diDistTo N d i T + d j i
        have : ∀ t : T, diDistTo N d j T - d j i ≤ diDist N d i t := by
          intro t
          have h1 : diDistTo N d j T ≤ diDist N d j t := ciInf_le (bdd_fin _) t
          have h2 := diDist_tri N hd (reach_edge hC) (reach_of_conn hconn i t) (d := d)
          have h3 := diDist_edge N hd hC (d := d)
          linarith
        have := le_ciInf this
        unfold diDistTo at this ⊢; linarith)
      hn hT hs
    have hW : (∑ i, ∑ j, N.C j i * d j i) = diTotalWeight N d := by
      unfold diTotalWeight; exact Finset.sum_comm
    refine ⟨Uᶜ, hUc, by simpa using hU, ratio_le_of N hUc (by simpa using hU) ?_⟩
    unfold diCutCap
    rw [compl_compl, Finset.sum_comm, ← hW, mul_comm ((Uᶜ.card : ℝ))]
    exact hcut

end LeightonRao.Directed

open LeightonRao.Directed


theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V)
    (hn : 2 ≤ Fintype.card V) (hconn : IsStronglyConnectedNet N)
    (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) (T : Finset V)
    (hT : 2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ))
    (hsum : 1 / (4 * (Fintype.card V : ℝ)) ≤ ∑ u ∈ Tᶜ, diDistFrom N d T u ∨
      1 / (4 * (Fintype.card V : ℝ)) ≤ ∑ u ∈ Tᶜ, diDistTo N d u T) :
    ∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧ diRatio N U ≤ 12 * diTotalWeight N d := by
  exact lemma_15_core N hn hconn d hd T hT hsum
