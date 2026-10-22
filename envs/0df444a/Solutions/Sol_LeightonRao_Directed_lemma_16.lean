-- Prove2me | solution 1 for LeightonRao.Directed.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:28:57.472922+00:00
-- url     : https://prove2.me/submissions/5a7864f4-a82a-4bc4-9d17-2228be93441a

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


/-! ### Region growing (Lemma 13 core) -/

theorem carve (R : Finset V) (C d : V → V → ℝ) (hC : ∀ i j, 0 ≤ C i j) (hd : ∀ i j, 0 ≤ d i j)
    (δ : V → ℝ) (hδ : ∀ u, 0 ≤ δ u) (v : V) (hvR : v ∈ R) (hv : δ v = 0)
    (hedge : ∀ i j, 0 < C i j → δ j ≤ δ i + d i j) (Δ : ℝ) (hΔ : 0 < Δ)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ = 0 → ∀ i j, 0 < C i j → d i j = 0) (M : ℝ)
    (hM : ∑ i ∈ R, (σ + ∑ j, C i j * d i j) ≤ M) :
    0 ≤ Real.log (M / σ) ∧ ∃ t, 0 ≤ t ∧ t < Δ ∧
      ∑ i ∈ R.filter (fun x => δ x ≤ t), ∑ j ∈ R.filter (fun x => t < δ x), C i j ≤
        (Real.log (M / σ) / Δ) * ∑ i ∈ R.filter (fun x => δ x ≤ t), (σ + ∑ j, C i j * d i j) := by
  classical
  rcases hσ0.lt_or_eq with hσp | hσz
  swap
  · subst hσz
    refine ⟨by simp, 0, le_refl _, hΔ, ?_⟩
    have : ∑ i ∈ R.filter (fun x => δ x ≤ 0), ∑ j ∈ R.filter (fun x => 0 < δ x), C i j = 0 := by
      apply Finset.sum_eq_zero; intro i hi; apply Finset.sum_eq_zero; intro j hj
      simp only [Finset.mem_filter] at hi hj
      rcases (hC i j).lt_or_eq with h | h
      · exfalso; have := hedge i j h; rw [hσ rfl i j h] at this; linarith [hi.2, hj.2]
      · exact h.symm
    rw [this]; simp
  -- σ > 0
  have hFnn : ∀ i, 0 ≤ σ + ∑ j, C i j * d i j :=
    fun i => add_nonneg hσ0 (Finset.sum_nonneg (fun j _ => mul_nonneg (hC i j) (hd i j)))
  have hMσ : σ ≤ M := by
    have h1 : σ + ∑ j, C v j * d v j ≤ ∑ i ∈ R, (σ + ∑ j, C i j * d i j) :=
      Finset.single_le_sum (fun i _ => hFnn i) hvR
    have h2 : 0 ≤ ∑ j, C v j * d v j := Finset.sum_nonneg (fun j _ => mul_nonneg (hC v j) (hd v j))
    linarith
  have hMpos : 0 < M := lt_of_lt_of_le hσp hMσ
  have hlog0 : 0 ≤ Real.log (M / σ) := Real.log_nonneg (by rw [le_div_iff₀ hσp]; linarith)
  refine ⟨hlog0, ?_⟩
  set K := Real.log (M / σ) / Δ with hK
  have hK0 : 0 ≤ K := div_nonneg hlog0 hΔ.le
  set P : Finset ℝ := insert 0 ((R.image δ).filter (fun x => x < Δ)) with hPdef
  have hPlt : ∀ t ∈ P, t < Δ := by
    intro t ht
    rw [hPdef, Finset.mem_insert, Finset.mem_filter] at ht
    rcases ht with rfl | ⟨_, h⟩
    · exact hΔ
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
  have hgap : ∀ t ∈ P, ∀ u ∈ R, t < δ u → nx P Δ t ≤ δ u := by
    intro t ht u hu htu
    by_cases hlt : δ u < Δ
    · exact nx_le_of (by rw [hPdef]; simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_image]; exact Or.inr ⟨⟨u, hu, rfl⟩, hlt⟩) htu
    · exact (nx_le P Δ t).trans (not_lt.1 hlt)
  set B : ℝ → Finset V := fun t => R.filter (fun x => δ x ≤ t) with hB
  set G : ℝ → ℝ := fun s => ∑ i ∈ B s, (σ + ∑ j, C i j * min (d i j) (s - δ i)) with hG
  set Uf : ℝ → ℝ := fun t => ∑ i ∈ B t, (σ + ∑ j, C i j * min (d i j) (nx P Δ t - δ i)) with hUf
  set F : ℝ → ℝ := fun t => ∑ i ∈ B t, (σ + ∑ j, C i j * d i j) with hF
  set c : ℝ → ℝ := fun t => ∑ i ∈ B t, ∑ j ∈ R.filter (fun x => t < δ x), C i j with hc
  have hterm : ∀ s, ∀ i ∈ B s, σ ≤ σ + ∑ j, C i j * min (d i j) (s - δ i) := by
    intro s i hi
    simp only [hB, Finset.mem_filter] at hi
    have : 0 ≤ ∑ j, C i j * min (d i j) (s - δ i) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hC i j) (le_min (hd i j) (by linarith [hi.2])))
    linarith
  have hGpos : ∀ s, 0 ≤ s → σ ≤ G s := by
    intro s hs
    have hvB : v ∈ B s := by simp only [hB, Finset.mem_filter]; exact ⟨hvR, by rw [hv]; exact hs⟩
    calc σ ≤ σ + ∑ j, C v j * min (d v j) (s - δ v) := hterm s v hvB
      _ ≤ G s := Finset.single_le_sum (fun i hi => le_trans hσ0 (hterm s i hi)) hvB
  have hGM : G Δ ≤ M := by
    refine le_trans ?_ hM
    calc G Δ ≤ ∑ i ∈ B Δ, (σ + ∑ j, C i j * d i j) := by
          apply Finset.sum_le_sum; intro i _
          have : ∑ j, C i j * min (d i j) (Δ - δ i) ≤ ∑ j, C i j * d i j :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hC i j))
          linarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hFnn i)
  have hUG : ∀ t ∈ P, Uf t ≤ G (nx P Δ t) := by
    intro t ht
    have hnx := lt_nx (P := P) (hPlt t ht)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx; simp only [hB, Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by linarith [hx.2]⟩
    · intro i hi _; exact le_trans hσ0 (hterm _ i hi)
  have hUF : ∀ t ∈ P, Uf t ≤ F t := by
    intro t ht
    apply Finset.sum_le_sum; intro i _
    have : ∑ j, C i j * min (d i j) (nx P Δ t - δ i) ≤ ∑ j, C i j * d i j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hC i j))
    linarith
  have hgrow : ∀ t ∈ P, (nx P Δ t - t) * c t ≤ Uf t - G t := by
    intro t ht
    have hnx := lt_nx (P := P) (hPlt t ht)
    simp only [hUf, hG, hc]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hi' := hi
    simp only [hB, Finset.mem_filter] at hi'
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    calc ∑ j ∈ R.filter (fun x => t < δ x), (nx P Δ t - t) * C i j
        ≤ ∑ j ∈ R.filter (fun x => t < δ x),
            (C i j * min (d i j) (nx P Δ t - δ i) - C i j * min (d i j) (t - δ i)) := by
          apply Finset.sum_le_sum
          intro j hj
          simp only [Finset.mem_filter] at hj
          rcases (hC i j).lt_or_eq with h | h
          · have he := hedge i j h
            have hj' := hgap t ht j hj.1 hj.2
            rw [min_eq_right (by linarith), min_eq_right (by linarith)]
            ring_nf; exact le_refl _
          · rw [← h]; simp
      _ ≤ ∑ j, (C i j * min (d i j) (nx P Δ t - δ i) - C i j * min (d i j) (t - δ i)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro j _ _
          rw [← mul_sub]
          exact mul_nonneg (hC i j) (sub_nonneg.2 (min_le_min_left _ (by linarith)))
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ t ∈ P, (nx P Δ t - t) * K < Real.log (G (nx P Δ t)) - Real.log (G t) := by
    intro t ht
    have hnx := lt_nx (P := P) (hPlt t ht)
    have hg : 0 < nx P Δ t - t := sub_pos.2 hnx
    have hGt : 0 < G t := lt_of_lt_of_le hσp (hGpos t (hPnn t ht))
    have hct : K * F t < c t := by
      exact hcon t (hPnn t ht) (hPlt t ht)
    have hUt : G t ≤ Uf t := by
      have := hgrow t ht
      have : 0 ≤ (nx P Δ t - t) * c t := mul_nonneg hg.le (le_trans (mul_nonneg hK0 (le_trans (le_refl _) (Finset.sum_nonneg (fun i _ => hFnn i)))) hct.le)
      linarith
    have hUpos : 0 < Uf t := lt_of_lt_of_le hGt hUt
    have h1 : 1 - (Uf t / G t)⁻¹ ≤ Real.log (Uf t / G t) :=
      Real.one_sub_inv_le_log_of_pos (div_pos hUpos hGt)
    rw [Real.log_div hUpos.ne' hGt.ne', inv_div] at h1
    have h2 : Real.log (Uf t) ≤ Real.log (G (nx P Δ t)) := Real.log_le_log hUpos (hUG t ht)
    have h3 : (nx P Δ t - t) * K < 1 - G t / Uf t := by
      rw [one_sub_div hUpos.ne', lt_div_iff₀ hUpos]
      have := hgrow t ht
      have hKU : K * Uf t ≤ K * F t := mul_le_mul_of_nonneg_left (hUF t ht) hK0
      nlinarith
    linarith
  have hsum := Finset.sum_lt_sum_of_nonempty hPne hlt
  rw [telescope (fun s => Real.log (G s)) P Δ hPlt hPne, hPmin, ← Finset.sum_mul,
    telescope (fun s => s) P Δ hPlt hPne, hPmin] at hsum
  have hG0 : σ ≤ G 0 := hGpos 0 (le_refl _)
  have h1 : Real.log (G Δ) ≤ Real.log M := Real.log_le_log (lt_of_lt_of_le hσp (hGpos Δ hΔ.le)) hGM
  have h2 : Real.log σ ≤ Real.log (G 0) := Real.log_le_log hσp hG0
  have h3 : (Δ - 0) * K = Real.log M - Real.log σ := by
    rw [hK, Real.log_div hMpos.ne' hσp.ne']; field_simp; ring
  linarith


open Classical in
noncomputable def δout (N : DiNetwork V) (d : V → V → ℝ) (Δ : ℝ) (v u : V) : ℝ :=
  if Reach N v u then min (diDist N d v u) Δ else Δ

open Classical in
noncomputable def δin (N : DiNetwork V) (d : V → V → ℝ) (Δ : ℝ) (v u : V) : ℝ :=
  if Reach N u v then min (diDist N d u v) Δ else Δ

section
variable (N : DiNetwork V) {d : V → V → ℝ} (hd : ∀ u v, 0 ≤ d u v) {Δ : ℝ} (hΔ : 0 < Δ)
include hd hΔ

lemma δout_nonneg (v u : V) : 0 ≤ δout N d Δ v u := by
  unfold δout; split_ifs
  · exact le_min (diDist_nonneg N hd _ _) hΔ.le
  · exact hΔ.le

lemma δin_nonneg (v u : V) : 0 ≤ δin N d Δ v u := by
  unfold δin; split_ifs
  · exact le_min (diDist_nonneg N hd _ _) hΔ.le
  · exact hΔ.le

lemma δout_self (v : V) : δout N d Δ v v = 0 := by
  unfold δout; rw [if_pos ⟨_, walk_single N v⟩, diDist_self N hd, min_eq_left hΔ.le]

lemma δin_self (v : V) : δin N d Δ v v = 0 := by
  unfold δin; rw [if_pos ⟨_, walk_single N v⟩, diDist_self N hd, min_eq_left hΔ.le]

lemma δout_le (v u : V) : δout N d Δ v u ≤ Δ := by
  unfold δout; split_ifs
  · exact min_le_right _ _
  · exact le_refl _

lemma δin_le (v u : V) : δin N d Δ v u ≤ Δ := by
  unfold δin; split_ifs
  · exact min_le_right _ _
  · exact le_refl _

lemma δout_edge (v i j : V) (hC : 0 < N.C i j) : δout N d Δ v j ≤ δout N d Δ v i + d i j := by
  by_cases hr : Reach N v i
  · have hrj := reach_snoc hr hC
    unfold δout; rw [if_pos hr, if_pos hrj]
    have h1 := diDist_tri N hd hr (reach_edge hC) (d := d)
    have h2 := diDist_edge N hd hC (d := d)
    have h3 := hd i j
    rcases le_total (diDist N d v i) Δ with h | h
    · rw [min_eq_left h]; exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right h]; linarith [min_le_right (diDist N d v j) Δ]
  · have : δout N d Δ v i = Δ := by unfold δout; rw [if_neg hr]
    rw [this]; linarith [δout_le N hd hΔ v j, hd i j]

lemma δin_edge (v i j : V) (hC : 0 < N.C i j) : δin N d Δ v i ≤ δin N d Δ v j + d i j := by
  by_cases hr : Reach N j v
  · have hri := reach_cons hr hC
    unfold δin; rw [if_pos hr, if_pos hri]
    have h1 := diDist_tri N hd (reach_edge hC) hr (d := d)
    have h2 := diDist_edge N hd hC (d := d)
    have h3 := hd i j
    rcases le_total (diDist N d j v) Δ with h | h
    · rw [min_eq_left h]; exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right h]; linarith [min_le_right (diDist N d i v) Δ]
  · have : δin N d Δ v j = Δ := by unfold δin; rw [if_neg hr]
    rw [this]; linarith [δin_le N hd hΔ v i, hd i j]

lemma δout_ball {v u : V} {t : ℝ} (h : δout N d Δ v u ≤ t) (ht : t < Δ) : u ∈ outBall N d v Δ := by
  unfold δout at h
  split_ifs at h with hr
  · have : diDist N d v u < Δ := by
      rcases min_le_iff.1 h with h' | h'
      · linarith
      · linarith
    obtain ⟨l, hl, hlen⟩ := exists_walk_lt N d hr this
    unfold outBall
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l, hl, hlen.le⟩
  · linarith

lemma δin_ball {v u : V} {t : ℝ} (h : δin N d Δ v u ≤ t) (ht : t < Δ) : u ∈ inBall N d v Δ := by
  unfold δin at h
  split_ifs at h with hr
  · have : diDist N d u v < Δ := by
      rcases min_le_iff.1 h with h' | h'
      · linarith
      · linarith
    obtain ⟨l, hl, hlen⟩ := exists_walk_lt N d hr this
    unfold inBall
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l, hl, hlen.le⟩
  · linarith

end

lemma split4 (R S : Finset V) (hS : S ⊆ R) (f : V → V → ℝ) :
    ∑ u ∈ R, ∑ w ∈ R, f u w = ∑ u ∈ R \ S, ∑ w ∈ R \ S, f u w + ∑ u ∈ R \ S, ∑ w ∈ S, f u w +
      ∑ u ∈ S, ∑ w ∈ R \ S, f u w + ∑ u ∈ S, ∑ w ∈ S, f u w := by
  have h1 : ∀ u, ∑ w ∈ R, f u w = ∑ w ∈ R \ S, f u w + ∑ w ∈ S, f u w :=
    fun u => (Finset.sum_sdiff hS).symm
  rw [← Finset.sum_sdiff hS]
  simp only [h1, Finset.sum_add_distrib]
  ring

noncomputable def vol2 (N : DiNetwork V) (d : V → V → ℝ) (σ : ℝ) (i : V) : ℝ :=
  σ + ∑ j, (N.C i j * d i j + N.C j i * d j i)

theorem build (N : DiNetwork V) (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) (Δ : ℝ) (hΔ : 0 < Δ)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ = 0 → ∀ i j, 0 < N.C i j → d i j = 0) (R : Finset V) :
    ∃ (r : ℕ) (lab : V → ℕ), (∀ x ∈ R, lab x < r) ∧
      (∀ i < r, ∃ v ∈ R, lab v = i ∧
        (R.filter (fun x => lab x = i)).card ≤ (inBall N d v Δ).card ∧
        (R.filter (fun x => lab x = i)).card ≤ (outBall N d v Δ).card) ∧
      (∑ u ∈ R, ∑ w ∈ R, if lab w < lab u then N.C u w else 0) ≤
        (Real.log (((Fintype.card V : ℝ) * σ + diTotalWeight N d) / σ) / Δ) *
          ∑ i ∈ R, vol2 N d σ i := by
  classical
  set K := Real.log (((Fintype.card V : ℝ) * σ + diTotalWeight N d) / σ) / Δ with hK
  set M := (Fintype.card V : ℝ) * σ + diTotalWeight N d with hMdef
  have hvol : ∀ i, σ + ∑ j, N.C i j * d i j ≤ vol2 N d σ i := by
    intro i; unfold vol2
    have : ∑ j, N.C i j * d i j ≤ ∑ j, (N.C i j * d i j + N.C j i * d j i) :=
      Finset.sum_le_sum (fun j _ => le_add_of_nonneg_right (mul_nonneg (N.C_nonneg j i) (hd j i)))
    linarith
  have hvol' : ∀ i, σ + ∑ j, N.C j i * d j i ≤ vol2 N d σ i := by
    intro i; unfold vol2
    have : ∑ j, N.C j i * d j i ≤ ∑ j, (N.C i j * d i j + N.C j i * d j i) :=
      Finset.sum_le_sum (fun j _ => le_add_of_nonneg_left (mul_nonneg (N.C_nonneg i j) (hd i j)))
    linarith
  have hMout : ∀ R : Finset V, ∑ i ∈ R, (σ + ∑ j, N.C i j * d i j) ≤ M := by
    intro R
    calc ∑ i ∈ R, (σ + ∑ j, N.C i j * d i j) ≤ ∑ i, (σ + ∑ j, N.C i j * d i j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => add_nonneg hσ0 (Finset.sum_nonneg (fun j _ => mul_nonneg (N.C_nonneg i j) (hd i j))))
      _ = M := by rw [Finset.sum_add_distrib]; simp [hMdef, diTotalWeight]
  have hMin : ∀ R : Finset V, ∑ i ∈ R, (σ + ∑ j, N.C j i * d j i) ≤ M := by
    intro R
    calc ∑ i ∈ R, (σ + ∑ j, N.C j i * d j i) ≤ ∑ i, (σ + ∑ j, N.C j i * d j i) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => add_nonneg hσ0 (Finset.sum_nonneg (fun j _ => mul_nonneg (N.C_nonneg j i) (hd j i))))
      _ = M := by
          rw [Finset.sum_add_distrib]; simp only [hMdef, diTotalWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [Finset.sum_comm]
  induction R using Finset.strongInduction with
  | H R ih =>
  rcases R.eq_empty_or_nonempty with hR | ⟨v, hvR⟩
  · subst hR
    exact ⟨0, fun _ => 0, by simp, fun i hi => absurd hi (Nat.not_lt_zero _), by simp⟩
  by_cases hcmp : (outBall N d v Δ).card ≤ (inBall N d v Δ).card
  · -- carve an out-ball, placed last
    obtain ⟨hK0, t, ht0, htΔ, hcut⟩ := carve R N.C d N.C_nonneg hd (δout N d Δ v)
      (δout_nonneg N hd hΔ v) v hvR (δout_self N hd hΔ v) (fun i j h => δout_edge N hd hΔ v i j h)
      Δ hΔ σ hσ0 hσ M (hMout R)
    set S := R.filter (fun x => δout N d Δ v x ≤ t) with hS
    have hSR : S ⊆ R := Finset.filter_subset _ _
    have hvS : v ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨hvR, by rw [δout_self N hd hΔ]; exact ht0⟩
    have hRS : R \ S = R.filter (fun x => t < δout N d Δ v x) := by
      ext x; simp only [hS, Finset.mem_sdiff, Finset.mem_filter, not_and, not_le]; tauto
    have hSball : S ⊆ outBall N d v Δ := by
      intro x hx; rw [hS, Finset.mem_filter] at hx; exact δout_ball N hd hΔ hx.2 htΔ
    obtain ⟨r', lab', h1, h2, h3⟩ := ih (R \ S) (Finset.sdiff_ssubset hSR ⟨v, hvS⟩)
    refine ⟨r' + 1, fun x => if x ∈ S then r' else lab' x, ?_, ?_, ?_⟩
    · intro x hx
      by_cases hxS : x ∈ S
      · simp [hxS]
      · simp only [hxS, if_false]; have := h1 x (Finset.mem_sdiff.2 ⟨hx, hxS⟩); omega
    · intro i hi
      by_cases hir : i = r'
      · subst hir
        have hpart : R.filter (fun x => (if x ∈ S then i else lab' x) = i) = S := by
          ext x
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hx, hl⟩
            by_contra hxS
            simp only [hxS, if_false] at hl
            have := h1 x (Finset.mem_sdiff.2 ⟨hx, hxS⟩); omega
          · intro hxS; exact ⟨hSR hxS, by simp [hxS]⟩
        refine ⟨v, hvR, by simp [hvS], ?_, ?_⟩
        · rw [hpart]; exact (Finset.card_le_card hSball).trans hcmp
        · rw [hpart]; exact Finset.card_le_card hSball
      · have hi' : i < r' := by omega
        obtain ⟨w, hw, hlw, hc1, hc2⟩ := h2 i hi'
        have hwS : w ∉ S := (Finset.mem_sdiff.1 hw).2
        have hpart : R.filter (fun x => (if x ∈ S then r' else lab' x) = i) =
            (R \ S).filter (fun x => lab' x = i) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_sdiff]
          by_cases hxS : x ∈ S
          · simp only [hxS, if_true, not_true_eq_false, and_false, false_and, iff_false]
            omega
          · simp [hxS]
        refine ⟨w, (Finset.mem_sdiff.1 hw).1, by simp [hwS, hlw], ?_, ?_⟩
        · rw [hpart]; exact hc1
        · rw [hpart]; exact hc2
    · rw [split4 R S hSR]
      have e1 : ∑ u ∈ R \ S, ∑ w ∈ R \ S, (if (if w ∈ S then r' else lab' w) < (if u ∈ S then r' else lab' u)
          then N.C u w else 0) = ∑ u ∈ R \ S, ∑ w ∈ R \ S, (if lab' w < lab' u then N.C u w else 0) := by
        apply Finset.sum_congr rfl; intro u hu; apply Finset.sum_congr rfl; intro w hw
        rw [if_neg (Finset.mem_sdiff.1 hu).2, if_neg (Finset.mem_sdiff.1 hw).2]
      have e2 : ∑ u ∈ R \ S, ∑ w ∈ S, (if (if w ∈ S then r' else lab' w) < (if u ∈ S then r' else lab' u)
          then N.C u w else 0) = 0 := by
        apply Finset.sum_eq_zero; intro u hu; apply Finset.sum_eq_zero; intro w hw
        rw [if_neg (Finset.mem_sdiff.1 hu).2, if_pos hw, if_neg]
        have := h1 u hu; omega
      have e3 : ∑ u ∈ S, ∑ w ∈ R \ S, (if (if w ∈ S then r' else lab' w) < (if u ∈ S then r' else lab' u)
          then N.C u w else 0) = ∑ u ∈ S, ∑ w ∈ R.filter (fun x => t < δout N d Δ v x), N.C u w := by
        rw [← hRS]
        apply Finset.sum_congr rfl; intro u hu; apply Finset.sum_congr rfl; intro w hw
        rw [if_pos hu, if_neg (Finset.mem_sdiff.1 hw).2, if_pos (h1 w hw)]
      have e4 : ∑ u ∈ S, ∑ w ∈ S, (if (if w ∈ S then r' else lab' w) < (if u ∈ S then r' else lab' u)
          then N.C u w else 0) = 0 := by
        apply Finset.sum_eq_zero; intro u hu; apply Finset.sum_eq_zero; intro w hw
        rw [if_pos hu, if_pos hw]; simp
      rw [e1, e2, e3, e4]
      have hcut' : ∑ u ∈ S, ∑ w ∈ R.filter (fun x => t < δout N d Δ v x), N.C u w ≤ K * ∑ i ∈ S, vol2 N d σ i :=
        hcut.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hvol i)) (div_nonneg hK0 hΔ.le))
      rw [← Finset.sum_sdiff hSR, mul_add]
      linarith
  · -- carve an in-ball, placed first
    push_neg at hcmp
    obtain ⟨hK0, t, ht0, htΔ, hcut⟩ := carve R (fun a b => N.C b a) (fun a b => d b a)
      (fun a b => N.C_nonneg b a) (fun a b => hd b a) (δin N d Δ v)
      (δin_nonneg N hd hΔ v) v hvR (δin_self N hd hΔ v) (fun i j h => δin_edge N hd hΔ v j i h)
      Δ hΔ σ hσ0 (fun h0 i j h => hσ h0 j i h) M (hMin R)
    set S := R.filter (fun x => δin N d Δ v x ≤ t) with hS
    have hSR : S ⊆ R := Finset.filter_subset _ _
    have hvS : v ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨hvR, by rw [δin_self N hd hΔ]; exact ht0⟩
    have hRS : R \ S = R.filter (fun x => t < δin N d Δ v x) := by
      ext x; simp only [hS, Finset.mem_sdiff, Finset.mem_filter, not_and, not_le]; tauto
    have hSball : S ⊆ inBall N d v Δ := by
      intro x hx; rw [hS, Finset.mem_filter] at hx; exact δin_ball N hd hΔ hx.2 htΔ
    obtain ⟨r', lab', h1, h2, h3⟩ := ih (R \ S) (Finset.sdiff_ssubset hSR ⟨v, hvS⟩)
    refine ⟨r' + 1, fun x => if x ∈ S then 0 else lab' x + 1, ?_, ?_, ?_⟩
    · intro x hx
      by_cases hxS : x ∈ S
      · simp [hxS]
      · simp only [hxS, if_false]; have := h1 x (Finset.mem_sdiff.2 ⟨hx, hxS⟩); omega
    · intro i hi
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0
        have hpart : R.filter (fun x => (if x ∈ S then 0 else lab' x + 1) = 0) = S := by
          ext x
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hx, hl⟩
            by_contra hxS
            simp only [hxS, if_false] at hl
            omega
          · intro hxS; exact ⟨hSR hxS, by simp [hxS]⟩
        refine ⟨v, hvR, by simp [hvS], ?_, ?_⟩
        · rw [hpart]; exact Finset.card_le_card hSball
        · rw [hpart]; exact (Finset.card_le_card hSball).trans hcmp.le
      · obtain ⟨w, hw, hlw, hc1, hc2⟩ := h2 (i - 1) (by omega)
        have hwS : w ∉ S := (Finset.mem_sdiff.1 hw).2
        have hpart : R.filter (fun x => (if x ∈ S then 0 else lab' x + 1) = i) =
            (R \ S).filter (fun x => lab' x = i - 1) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_sdiff]
          by_cases hxS : x ∈ S
          · simp only [hxS, if_true, not_true_eq_false, and_false, false_and, iff_false]
            omega
          · simp only [hxS, if_false, not_false_eq_true, and_true]
            constructor
            · rintro ⟨h, h'⟩; exact ⟨h, by omega⟩
            · rintro ⟨h, h'⟩; exact ⟨h, by omega⟩
        refine ⟨w, (Finset.mem_sdiff.1 hw).1, by simp [hwS, hlw]; omega, ?_, ?_⟩
        · rw [hpart]; exact hc1
        · rw [hpart]; exact hc2
    · rw [split4 R S hSR]
      have e1 : ∑ u ∈ R \ S, ∑ w ∈ R \ S, (if (if w ∈ S then 0 else lab' w + 1) < (if u ∈ S then 0 else lab' u + 1)
          then N.C u w else 0) = ∑ u ∈ R \ S, ∑ w ∈ R \ S, (if lab' w < lab' u then N.C u w else 0) := by
        apply Finset.sum_congr rfl; intro u hu; apply Finset.sum_congr rfl; intro w hw
        rw [if_neg (Finset.mem_sdiff.1 hu).2, if_neg (Finset.mem_sdiff.1 hw).2]
        simp only [Nat.add_lt_add_iff_right]
      have e2 : ∑ u ∈ R \ S, ∑ w ∈ S, (if (if w ∈ S then 0 else lab' w + 1) < (if u ∈ S then 0 else lab' u + 1)
          then N.C u w else 0) = ∑ w ∈ S, ∑ u ∈ R.filter (fun x => t < δin N d Δ v x), N.C u w := by
        rw [Finset.sum_comm, ← hRS]
        apply Finset.sum_congr rfl; intro w hw; apply Finset.sum_congr rfl; intro u hu
        rw [if_neg (Finset.mem_sdiff.1 hu).2, if_pos hw, if_pos (Nat.succ_pos _)]
      have e3 : ∑ u ∈ S, ∑ w ∈ R \ S, (if (if w ∈ S then 0 else lab' w + 1) < (if u ∈ S then 0 else lab' u + 1)
          then N.C u w else 0) = 0 := by
        apply Finset.sum_eq_zero; intro u hu; apply Finset.sum_eq_zero; intro w hw
        rw [if_pos hu, if_neg (Finset.mem_sdiff.1 hw).2, if_neg (by omega)]
      have e4 : ∑ u ∈ S, ∑ w ∈ S, (if (if w ∈ S then 0 else lab' w + 1) < (if u ∈ S then 0 else lab' u + 1)
          then N.C u w else 0) = 0 := by
        apply Finset.sum_eq_zero; intro u hu; apply Finset.sum_eq_zero; intro w hw
        rw [if_pos hu, if_pos hw]; simp
      rw [e1, e2, e3, e4]
      have hcut' : ∑ w ∈ S, ∑ u ∈ R.filter (fun x => t < δin N d Δ v x), N.C u w ≤ K * ∑ i ∈ S, vol2 N d σ i :=
        hcut.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hvol' i)) (div_nonneg hK0 hΔ.le))
      rw [← Finset.sum_sdiff hSR, mul_add]
      linarith


lemma sum_vol2 (N : DiNetwork V) (d : V → V → ℝ) (σ : ℝ) :
    ∑ i, vol2 N d σ i = (Fintype.card V : ℝ) * σ + 2 * diTotalWeight N d := by
  unfold vol2 diTotalWeight
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_comm (f := fun i j => N.C j i * d j i)]
  ring

lemma log_ineq (n : ℝ) (hn : 2 ≤ n) (W : ℝ) (hW : 0 ≤ W) :
    3 * W * Real.log (2 * n) ≤ 8 * W * Real.logb 2 n := by
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha1 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hx : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  rw [Real.log_mul (by norm_num) (by linarith), Real.logb]
  rw [mul_div_assoc', le_div_iff₀ ha]
  have : 3 * (Real.log 2 + Real.log n) * Real.log 2 ≤ 8 * Real.log n := by nlinarith
  nlinarith

theorem lemma_13_core (N : DiNetwork V)
    (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ (r : ℕ) (lab : V → Fin r),
      (∑ u, ∑ v, if lab v < lab u then N.C u v else 0) ≤
        8 * diTotalWeight N d * Real.logb 2 (Fintype.card V) / Δ ∧
      ∀ i : Fin r, ∃ v, lab v = i ∧
        (Finset.univ.filter (fun x => lab x = i)).card ≤ (inBall N d v Δ).card ∧
        (Finset.univ.filter (fun x => lab x = i)).card ≤ (outBall N d v Δ).card := by
  classical
  set W := diTotalWeight N d with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (N.C_nonneg i j) (hd i j)))
  set σ := W / (Fintype.card V : ℝ) with hσdef
  have hσ0 : 0 ≤ σ := div_nonneg hW0 (Nat.cast_nonneg _)
  have hσ : σ = 0 → ∀ i j, 0 < N.C i j → d i j = 0 := by
    intro h0 i j hC
    have hn : (Fintype.card V : ℝ) ≠ 0 := by
      have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨i⟩
      exact_mod_cast this.ne'
    have hW' : W = 0 := by
      rw [hσdef, div_eq_zero_iff] at h0; tauto
    have h1 : ∀ i ∈ Finset.univ, ∑ j, N.C i j * d i j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (N.C_nonneg i j) (hd i j)))).1 hW'
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (N.C_nonneg i j) (hd i j))).1 (h1 i (Finset.mem_univ _)) j (Finset.mem_univ _)
    rcases mul_eq_zero.1 h2 with h | h
    · linarith
    · exact h
  obtain ⟨r, lab, h1, h2, h3⟩ := build N d hd Δ hΔ σ hσ0 hσ Finset.univ
  refine ⟨r, fun x => ⟨lab x, h1 x (Finset.mem_univ _)⟩, ?_, ?_⟩
  · have hsum : (∑ u, ∑ v, if (⟨lab v, h1 v (Finset.mem_univ _)⟩ : Fin r) < ⟨lab u, h1 u (Finset.mem_univ _)⟩
        then N.C u v else 0) = ∑ u, ∑ v, if lab v < lab u then N.C u v else 0 := by
      apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro v _
      simp only [Fin.mk_lt_mk]
    rw [hsum]
    rcases Nat.lt_or_ge (Fintype.card V) 2 with hn | hn
    · have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.1 (by omega)
      have hz : (∑ u, ∑ v, if lab v < lab u then N.C u v else 0) = 0 := by
        apply Finset.sum_eq_zero; intro u _; apply Finset.sum_eq_zero; intro v _
        rw [Subsingleton.elim u v]; simp
      rw [hz]
      have : Real.logb 2 (Fintype.card V) = 0 := by
        interval_cases h : Fintype.card V <;> simp
      rw [this]; simp
    · refine h3.trans ?_
      rw [sum_vol2]
      have hn' : (2:ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
      rcases hW0.lt_or_eq with hWp | hWz
      · have hσp : 0 < σ := div_pos hWp (by linarith)
        have e1 : ((Fintype.card V : ℝ) * σ + W) / σ = 2 * (Fintype.card V : ℝ) := by
          rw [hσdef]; field_simp; ring
        have e2 : (Fintype.card V : ℝ) * σ + 2 * W = 3 * W := by
          rw [hσdef]; field_simp; ring
        rw [e1, e2, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hΔ]
        have := log_ineq (Fintype.card V : ℝ) hn' W hW0
        linarith
      · have : σ = 0 := by rw [hσdef, ← hWz]; simp
        rw [this, ← hWz]; simp
  · intro i
    obtain ⟨v, -, hv, hc1, hc2⟩ := h2 i.1 i.2
    have hf : Finset.univ.filter (fun x => (⟨lab x, h1 x (Finset.mem_univ _)⟩ : Fin r) = i) =
        Finset.univ.filter (fun x => lab x = i.1) := by
      ext x; simp [Fin.ext_iff]
    refine ⟨v, Fin.ext hv, ?_, ?_⟩
    · rw [hf]; exact hc1
    · rw [hf]; exact hc2


theorem corollary_14_core (N : DiNetwork V)
    (hn : 2 ≤ Fintype.card V) (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) :
    let n : ℝ := (Fintype.card V : ℝ)
    let Δ : ℝ := 1 / (4 * n ^ 2)
    (∃ v, 2 * n ≤ 3 * ((inBall N d v Δ).card : ℝ) ∧
        2 * n ≤ 3 * ((outBall N d v Δ).card : ℝ)) ∨
    (∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧
        diRatio N U ≤ 8 * diTotalWeight N d * Real.logb 2 n / (Δ * (n / 6) * (5 * n / 6))) := by
  classical
  intro n Δ
  have hnd : n = (Fintype.card V : ℝ) := rfl
  have hn' : (2:ℝ) ≤ n := by rw [hnd]; exact_mod_cast hn
  have hΔ : 0 < Δ := by positivity
  obtain ⟨r, lab, hback, hparts⟩ := lemma_13_core N d hd Δ hΔ
  by_cases big : ∃ i : Fin r, 2 * n ≤ 3 * ((Finset.univ.filter (fun x => lab x = i)).card : ℝ)
  · left
    obtain ⟨i, hi⟩ := big
    obtain ⟨v, -, h1, h2⟩ := hparts i
    refine ⟨v, ?_, ?_⟩
    · have : ((Finset.univ.filter (fun x => lab x = i)).card : ℝ) ≤ ((inBall N d v Δ).card : ℝ) := by
        exact_mod_cast h1
      linarith
    · have : ((Finset.univ.filter (fun x => lab x = i)).card : ℝ) ≤ ((outBall N d v Δ).card : ℝ) := by
        exact_mod_cast h2
      linarith
  · right
    push_neg at big
    set S : ℕ → ℕ := fun k => (Finset.univ.filter (fun x => (lab x).val < k)).card with hS
    have hS0 : S 0 = 0 := by simp [hS]
    have hSr : ∀ k, r ≤ k → S k = Fintype.card V := by
      intro k hk
      simp only [hS]
      rw [Finset.filter_true_of_mem (fun x _ => by have := (lab x).2; omega), Finset.card_univ]
    have hSsucc : ∀ k (hk : k < r), S (k + 1) = S k + (Finset.univ.filter (fun x => lab x = ⟨k, hk⟩)).card := by
      intro k hk
      simp only [hS]
      have : Finset.univ.filter (fun x => (lab x).val < k + 1) =
          Finset.univ.filter (fun x => (lab x).val < k) ∪ Finset.univ.filter (fun x => lab x = ⟨k, hk⟩) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Fin.ext_iff]; omega
      rw [this, Finset.card_union_of_disjoint]
      rw [Finset.disjoint_filter]; intro x _ h1 h2; rw [Fin.ext_iff] at h2; simp at h2; omega
    have hex : ∃ k, Fintype.card V ≤ 6 * S k := ⟨r, by rw [hSr r le_rfl]; omega⟩
    set k0 := Nat.find hex with hk0
    have hk0spec : Fintype.card V ≤ 6 * S k0 := Nat.find_spec hex
    have hk0pos : k0 ≠ 0 := by
      intro h; rw [h, hS0] at hk0spec; omega
    have hprev : ¬ (Fintype.card V ≤ 6 * S (k0 - 1)) := Nat.find_min hex (by omega)
    have hk0r : k0 - 1 < r := by
      by_contra h; push_neg at h; rw [hSr _ h] at hprev; omega
    have hstep := hSsucc (k0 - 1) hk0r
    rw [show k0 - 1 + 1 = k0 by omega] at hstep
    have hsmall := big ⟨k0 - 1, hk0r⟩
    have hsmall' : 3 * (Finset.univ.filter (fun x => lab x = ⟨k0 - 1, hk0r⟩)).card < 2 * Fintype.card V := by
      have : (3 * (Finset.univ.filter (fun x => lab x = ⟨k0 - 1, hk0r⟩)).card : ℝ) < 2 * n := by
        push_cast; linarith
      rw [hnd] at this; exact_mod_cast this
    set E := Finset.univ.filter (fun x => (lab x).val < k0) with hE
    have hEcard : E.card = S k0 := rfl
    have hup : 6 * S k0 ≤ 5 * Fintype.card V := by omega
    set U := Eᶜ with hU
    have hUU : Uᶜ = E := by rw [hU, compl_compl]
    have hcards : E.card + U.card = Fintype.card V := Finset.card_add_card_compl E
    have hEpos : 0 < E.card := by omega
    have hUpos : 0 < U.card := by omega
    have hprod : (n / 6) * (5 * n / 6) ≤ (U.card : ℝ) * (Uᶜ.card : ℝ) := by
      rw [hUU]
      have e1 : (U.card : ℝ) = n - E.card := by
        have : ((E.card + U.card : ℕ) : ℝ) = n := by rw [hnd]; exact_mod_cast hcards
        push_cast at this; linarith
      have e2 : n ≤ 6 * (E.card : ℝ) := by rw [hEcard, hnd]; exact_mod_cast hk0spec
      have e3 : 6 * (E.card : ℝ) ≤ 5 * n := by rw [hEcard, hnd]; exact_mod_cast hup
      rw [e1]; nlinarith
    have hUne : U.Nonempty := Finset.card_pos.1 hUpos
    have hUcne : Uᶜ.Nonempty := by rw [hUU]; exact Finset.card_pos.1 hEpos
    refine ⟨U, hUne, hUcne, ?_⟩
    have hcut : diCutCap N U ≤ ∑ u, ∑ v, if lab v < lab u then N.C u v else 0 := by
      unfold diCutCap
      calc ∑ u ∈ U, ∑ v ∈ Uᶜ, N.C u v = ∑ u ∈ U, ∑ v ∈ Uᶜ, (if lab v < lab u then N.C u v else 0) := by
            apply Finset.sum_congr rfl; intro u hu; apply Finset.sum_congr rfl; intro v hv
            rw [hUU] at hv
            rw [hU, Finset.mem_compl, hE, Finset.mem_filter] at hu
            rw [hE, Finset.mem_filter] at hv
            rw [if_pos]
            rw [Fin.lt_def]; push_neg at hu; have := hu (Finset.mem_univ _); omega
        _ ≤ ∑ u, ∑ v ∈ Uᶜ, (if lab v < lab u then N.C u v else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun u _ _ => Finset.sum_nonneg (fun v _ => by split_ifs; exact N.C_nonneg u v; exact le_refl _))
        _ ≤ ∑ u, ∑ v, (if lab v < lab u then N.C u v else 0) := by
            apply Finset.sum_le_sum; intro u _
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun v _ _ => by split_ifs; exact N.C_nonneg u v; exact le_refl _)
    unfold diRatio
    have hpos : 0 < (n / 6) * (5 * n / 6) := by positivity
    have hW0 : 0 ≤ 8 * diTotalWeight N d * Real.logb 2 n / Δ := by
      have : 0 ≤ diTotalWeight N d := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (N.C_nonneg i j) (hd i j)))
      have : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) (by linarith)
      positivity
    calc diCutCap N U / ((U.card : ℝ) * (Uᶜ.card : ℝ))
        ≤ (8 * diTotalWeight N d * Real.logb 2 n / Δ) / ((n / 6) * (5 * n / 6)) :=
          div_le_div₀ hW0 (hcut.trans hback) hpos hprod
      _ = 8 * diTotalWeight N d * Real.logb 2 n / (Δ * (n / 6) * (5 * n / 6)) := by
          rw [div_div, mul_assoc Δ]


lemma one_le_logb2 {n : ℝ} (hn : 2 ≤ n) : 1 ≤ Real.logb 2 n := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hn

theorem lemma_16_core (N : DiNetwork V)
    (hn : 2 ≤ Fintype.card V) (hconn : IsStronglyConnectedNet N)
    (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) (hW : SatisfiesDiConstraint N d) :
    ∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧
      diRatio N U ≤ (1152 / 5) * diTotalWeight N d * Real.logb 2 (Fintype.card V) := by
  classical
  have hn' : (2:ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hW0 : 0 ≤ diTotalWeight N d := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (N.C_nonneg i j) (hd i j)))
  have hlog := one_le_logb2 hn'
  have h12 : 12 * diTotalWeight N d ≤ (1152 / 5) * diTotalWeight N d * Real.logb 2 (Fintype.card V) := by
    nlinarith
  rcases corollary_14_core N hn d hd with ⟨v, hin, hout⟩ | ⟨U, hU, hUc, hr⟩
  swap
  · refine ⟨U, hU, hUc, hr.trans (le_of_eq ?_)⟩
    have : (Fintype.card V : ℝ) ≠ 0 := by linarith
    field_simp; ring
  set n : ℝ := (Fintype.card V : ℝ) with hnd
  set Δ : ℝ := 1 / (4 * n ^ 2) with hΔ
  have hΔ0 : 0 < Δ := by positivity
  have hnΔ : n * Δ = 1 / (4 * n) := by rw [hΔ]; field_simp
  -- split the constraint
  have htri : ∀ u w, diDist N d u w ≤ diDist N d u v + diDist N d v w :=
    fun u w => diDist_tri N hd (reach_of_conn hconn u v) (reach_of_conn hconn v w)
  have hsplit : 1 ≤ n * (∑ u, diDist N d u v) + n * (∑ w, diDist N d v w) := by
    calc (1:ℝ) ≤ ∑ u, ∑ w, diDist N d u w := hW
      _ ≤ ∑ u, ∑ w, (diDist N d u v + diDist N d v w) :=
          Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun w _ => htri u w))
      _ = n * (∑ u, diDist N d u v) + n * (∑ w, diDist N d v w) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [Finset.mul_sum (s := Finset.univ) (a := n), Finset.mul_sum (s := Finset.univ) (a := n)]
  have hnpos : 0 < n := by linarith
  have hcase : 1 / (2 * n) ≤ ∑ w, diDist N d v w ∨ 1 / (2 * n) ≤ ∑ u, diDist N d u v := by
    by_contra hc
    push_neg at hc
    have h1 : n * (∑ w, diDist N d v w) < n * (1 / (2 * n)) := mul_lt_mul_of_pos_left hc.1 hnpos
    have h2 : n * (∑ u, diDist N d u v) < n * (1 / (2 * n)) := mul_lt_mul_of_pos_left hc.2 hnpos
    have : n * (1 / (2 * n)) = 1 / 2 := by field_simp
    linarith
  rcases hcase with hB | hA
  · set T := outBall N d v Δ with hT
    have hvT : v ∈ T := by
      rw [hT]; unfold outBall; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨[v], walk_single N v, by rw [diLen_single]; exact hΔ0.le⟩
    haveI : Nonempty T := ⟨⟨v, hvT⟩⟩
    have hTd : ∀ t ∈ T, diDist N d v t ≤ Δ := by
      intro t ht
      rw [hT] at ht; unfold outBall at ht; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      obtain ⟨l, hl, hlen⟩ := ht
      exact (diDist_le N hd hl).trans hlen
    have hfrom : ∀ w, diDist N d v w ≤ Δ + diDistFrom N d T w := by
      intro w
      have : ∀ t : T, diDist N d v w - Δ ≤ diDist N d t w := by
        intro t
        have := diDist_tri N hd (reach_of_conn hconn v t) (reach_of_conn hconn t w) (d := d)
        have := hTd t t.2
        linarith
      have := le_ciInf this
      unfold diDistFrom; linarith
    have hzero : ∀ w ∈ T, diDistFrom N d T w = 0 := by
      intro w hw
      apply le_antisymm _ (Real.iInf_nonneg (fun t => diDist_nonneg N hd _ _))
      have := ciInf_le (bdd_fin (fun s : T => diDist N d s w)) ⟨w, hw⟩
      simpa [diDist_self N hd] using this
    have hsum : 1 / (4 * n) ≤ ∑ u ∈ Tᶜ, diDistFrom N d T u := by
      have e : ∑ w, diDistFrom N d T w = ∑ u ∈ Tᶜ, diDistFrom N d T u := by
        rw [← Finset.sum_compl_add_sum T, Finset.sum_eq_zero hzero, add_zero]
      have : ∑ w, diDist N d v w ≤ n * Δ + ∑ w, diDistFrom N d T w := by
        calc ∑ w, diDist N d v w ≤ ∑ w, (Δ + diDistFrom N d T w) := Finset.sum_le_sum (fun w _ => hfrom w)
          _ = n * Δ + ∑ w, diDistFrom N d T w := by
              rw [Finset.sum_add_distrib]; simp [hnd]
      have h2 : 1 / (2 * n) - 1 / (4 * n) = 1 / (4 * n) := by field_simp; ring
      rw [← e]; linarith
    obtain ⟨U, hU, hUc, hr⟩ := lemma_15_core N hn hconn d hd T hout (Or.inl hsum)
    exact ⟨U, hU, hUc, hr.trans h12⟩
  · set T := inBall N d v Δ with hT
    have hvT : v ∈ T := by
      rw [hT]; unfold inBall; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨[v], walk_single N v, by rw [diLen_single]; exact hΔ0.le⟩
    haveI : Nonempty T := ⟨⟨v, hvT⟩⟩
    have hTd : ∀ t ∈ T, diDist N d t v ≤ Δ := by
      intro t ht
      rw [hT] at ht; unfold inBall at ht; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      obtain ⟨l, hl, hlen⟩ := ht
      exact (diDist_le N hd hl).trans hlen
    have hto : ∀ u, diDist N d u v ≤ Δ + diDistTo N d u T := by
      intro u
      have : ∀ t : T, diDist N d u v - Δ ≤ diDist N d u t := by
        intro t
        have := diDist_tri N hd (reach_of_conn hconn u t) (reach_of_conn hconn t v) (d := d)
        have := hTd t t.2
        linarith
      have := le_ciInf this
      unfold diDistTo; linarith
    have hzero : ∀ w ∈ T, diDistTo N d w T = 0 := by
      intro w hw
      apply le_antisymm _ (Real.iInf_nonneg (fun t => diDist_nonneg N hd _ _))
      have := ciInf_le (bdd_fin (fun s : T => diDist N d w s)) ⟨w, hw⟩
      simpa [diDist_self N hd] using this
    have hsum : 1 / (4 * n) ≤ ∑ u ∈ Tᶜ, diDistTo N d u T := by
      have e : ∑ w, diDistTo N d w T = ∑ u ∈ Tᶜ, diDistTo N d u T := by
        rw [← Finset.sum_compl_add_sum T, Finset.sum_eq_zero hzero, add_zero]
      have : ∑ u, diDist N d u v ≤ n * Δ + ∑ w, diDistTo N d w T := by
        calc ∑ u, diDist N d u v ≤ ∑ u, (Δ + diDistTo N d u T) := Finset.sum_le_sum (fun u _ => hto u)
          _ = n * Δ + ∑ w, diDistTo N d w T := by
              rw [Finset.sum_add_distrib]; simp [hnd]
      have h2 : 1 / (2 * n) - 1 / (4 * n) = 1 / (4 * n) := by field_simp; ring
      rw [← e]; linarith
    obtain ⟨U, hU, hUc, hr⟩ := lemma_15_core N hn hconn d hd T hin (Or.inr hsum)
    exact ⟨U, hU, hUc, hr.trans h12⟩

end LeightonRao.Directed

open LeightonRao.Directed


theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V)
    (hn : 2 ≤ Fintype.card V) (hconn : IsStronglyConnectedNet N)
    (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) (hW : SatisfiesDiConstraint N d) :
    ∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧
      diRatio N U ≤ (1152 / 5) * diTotalWeight N d * Real.logb 2 (Fintype.card V) := by
  exact lemma_16_core N hn hconn d hd hW
