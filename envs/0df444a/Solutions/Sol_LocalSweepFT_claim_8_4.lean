-- Prove2me | solution 1 for LocalSweepFT.claim_8_4
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T01:00:18.022225+00:00
-- url     : https://prove2.me/submissions/dbd04473-2a99-4e73-b267-f3141f374f4f

import Mathlib

open SimpleGraph

lemma lsw_closed_walk {V : Type} [Fintype V] {T : SimpleGraph V} (hc : T.Connected) :
    ∀ k, k + 1 ≤ Fintype.card V → ∃ S : Finset V, S.card = k + 1 ∧
      ∃ (u : V) (p : T.Walk u u), p.length = 2 * k ∧ ∀ v ∈ S, v ∈ p.support := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    obtain ⟨v⟩ := hc.nonempty
    exact ⟨{v}, by simp, v, Walk.nil, by simp, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨S, hS, u, p, hp, hsub⟩ := ih (by omega)
    obtain ⟨y, hy⟩ : ∃ y, y ∉ S := by
      by_contra h
      push Not at h
      have : S = Finset.univ := Finset.eq_univ_of_forall h
      rw [this, Finset.card_univ] at hS
      omega
    have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨s, hs⟩ := hne
    obtain ⟨d, -, hd1, hd2⟩ := (hc.preconnected s y).some.exists_boundary_dart (↑S : Set V) hs hy
    have hadj : T.Adj d.fst d.snd := d.adj
    have hmem : d.fst ∈ p.support := hsub _ (by simpa using hd1)
    refine ⟨insert d.snd S, ?_, u, (p.takeUntil d.fst hmem).append
      ((Walk.cons hadj (Walk.cons hadj.symm Walk.nil)).append (p.dropUntil d.fst hmem)), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (by simpa using hd2)]; omega
    · have h1 := congrArg Walk.length (p.take_spec hmem)
      simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at h1 ⊢
      omega
    · intro v hv
      rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · right; left; simp
      · have h3 : v ∈ ((p.takeUntil d.fst hmem).append (p.dropUntil d.fst hmem)).support := by
          rw [p.take_spec hmem]; exact hsub v hv
        rw [Walk.mem_support_append_iff] at h3
        tauto

def lswSeqWalk {V : Type} {T : SimpleGraph V} (wk : ℕ → V) (h : ∀ j, T.Adj (wk j) (wk (j+1)))
    (i : ℕ) : (ℓ : ℕ) → T.Walk (wk i) (wk (i+ℓ))
  | 0 => Walk.nil
  | ℓ+1 => (lswSeqWalk wk h i ℓ).concat (h (i+ℓ))

lemma lswSeqWalk_length {V : Type} {T : SimpleGraph V} (wk : ℕ → V)
    (h : ∀ j, T.Adj (wk j) (wk (j+1))) (i ℓ : ℕ) : (lswSeqWalk wk h i ℓ).length = ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => simp [lswSeqWalk, ih]

lemma lswSeqWalk_mem {V : Type} {T : SimpleGraph V} (wk : ℕ → V)
    (h : ∀ j, T.Adj (wk j) (wk (j+1))) (i ℓ : ℕ) (v : V) :
    v ∈ (lswSeqWalk wk h i ℓ).support ↔ ∃ j ≤ ℓ, v = wk (i+j) := by
  induction ℓ with
  | zero => simp [lswSeqWalk]
  | succ ℓ ih =>
    simp only [lswSeqWalk, Walk.support_concat, List.concat_eq_append, List.mem_append, ih,
      List.mem_singleton]
    constructor
    · rintro (⟨j, hj, rfl⟩ | rfl)
      · exact ⟨j, by omega, rfl⟩
      · exact ⟨ℓ+1, le_rfl, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      by_cases hjl : j = ℓ + 1
      · right; subst hjl; rfl
      · left; exact ⟨j, by omega, rfl⟩

lemma lsw_cover {V : Type} [DecidableEq V] (wk : ℕ → V) (N ℓ : ℕ) (hℓ : ℓ + 1 ≤ N)
    (hper : ∀ i, wk (i + N) = wk i) (x : V) (t : ℕ) (hx : x = wk t) :
    ℓ + 1 ≤ ((Finset.range N).filter (fun i => ∃ j ≤ ℓ, x = wk (i + j))).card := by
  classical
  have hperk : ∀ k i, wk (i + N * k) = wk i := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih => intro i; rw [Nat.mul_succ, ← add_assoc, hper, ih]
  have ht : ∃ t' < N, x = wk t' := by
    refine ⟨t % N, Nat.mod_lt _ (by omega), ?_⟩
    have := hperk (t / N) (t % N)
    rw [Nat.mod_add_div] at this
    rw [hx, this]
  obtain ⟨t, htN, hx⟩ := ht
  have := Finset.card_le_card_of_injOn (s := Finset.range (ℓ + 1))
    (t := (Finset.range N).filter (fun i => ∃ j ≤ ℓ, x = wk (i + j)))
    (fun j => if j ≤ t then t - j else t + N - j) ?_ ?_
  · simpa using this
  · intro j hj
    simp only [Finset.coe_range, Set.mem_Iio] at hj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    by_cases hjt : j ≤ t
    · refine ⟨by simp only [if_pos hjt]; omega, j, by omega, ?_⟩
      simp only [if_pos hjt]
      rw [hx]; congr 1; omega
    · refine ⟨by simp only [if_neg hjt]; omega, j, by omega, ?_⟩
      simp only [if_neg hjt]
      have : t + N - j + j = t + N := by omega
      rw [this, hper, hx]
  · intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at hab
    split_ifs at hab <;> omega

lemma lsw_window {V : Type} [DecidableEq V] (wk : ℕ → V) (N ℓ : ℕ) (hN : 0 < N) (hℓ : ℓ + 1 ≤ N)
    (hper : ∀ i, wk (i + N) = wk i) (M : Finset V) (hM : ∀ x ∈ M, ∃ t, x = wk t) :
    ∃ i, M.card * (ℓ + 1) ≤ N * (M.filter (fun x => ∃ j ≤ ℓ, x = wk (i + j))).card := by
  classical
  by_contra hcon
  push Not at hcon
  have hsum : M.card * (ℓ + 1) ≤ ∑ i ∈ Finset.range N,
      (M.filter (fun x => ∃ j ≤ ℓ, x = wk (i + j))).card := by
    have h1 : ∑ i ∈ Finset.range N, (M.filter (fun x => ∃ j ≤ ℓ, x = wk (i + j))).card
        = ∑ x ∈ M, ((Finset.range N).filter (fun i => ∃ j ≤ ℓ, x = wk (i + j))).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [h1, mul_comm]
    calc (ℓ + 1) * M.card = ∑ _x ∈ M, (ℓ + 1) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun x hx => by
          obtain ⟨t, ht⟩ := hM x hx
          exact lsw_cover wk N ℓ hℓ hper x t ht)
  have hlt : ∑ i ∈ Finset.range N, N * (M.filter (fun x => ∃ j ≤ ℓ, x = wk (i + j))).card
      < ∑ _i ∈ Finset.range N, M.card * (ℓ + 1) :=
    Finset.sum_lt_sum_of_nonempty (by simp; omega) (fun i _ => hcon i)
  rw [← Finset.mul_sum] at hlt
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hlt
  nlinarith

theorem solution (γ β : ℝ) (hγ : 0 < γ) (hβ : 0 < β) (n : ℕ) (hn : 1 ≤ n) {V : Type}
    [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    (hτ : β * n ≤ T.edgeFinset.card)
    (hτm : (T.edgeFinset.card : ℝ) ≤ γ * (Finset.univ.filter (fun v => T.degree v = 1)).card) :
    ∃ T' : T.Subgraph, T'.Connected ∧ (T'.edgeSet.ncard : ℝ) < β / 2 * n ∧
      β / (4 * γ) * n ≤ ({v | v ∈ T'.verts ∧ T.degree v = 1} : Set V).ncard := by
  classical
  set τ := T.edgeFinset.card with hτdef
  have hcard : τ + 1 = Fintype.card V := hT.card_edgeFinset
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set b : ℝ := β * n with hb
  have hbpos : 0 < b := mul_pos hβ hnpos
  have hτpos : 1 ≤ τ := by
    have : (0 : ℝ) < τ := lt_of_lt_of_le hbpos hτ
    exact_mod_cast this
  obtain ⟨S, hS, u, p, hp, hsub⟩ := lsw_closed_walk hT.isConnected τ (by omega)
  have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S (by omega)
  have hall : ∀ v, v ∈ p.support := fun v => hsub v (by rw [hSuniv]; exact Finset.mem_univ v)
  set N := 2 * τ with hN
  have hNpos : 0 < N := by omega
  set wk : ℕ → V := fun i => p.getVert (i % N) with hwk
  have hper : ∀ i, wk (i + N) = wk i := by
    intro i; simp [hwk]
  have hadj : ∀ j, T.Adj (wk j) (wk (j+1)) := by
    intro j
    have hr := Nat.mod_lt j hNpos
    have h1 : (j + 1) % N = (j % N + 1) % N := by
      rw [Nat.add_mod j 1 N, Nat.mod_eq_of_lt (show 1 < N by omega)]
    simp only [hwk]
    rw [h1]
    by_cases hlt : j % N + 1 < N
    · rw [Nat.mod_eq_of_lt hlt]
      exact p.adj_getVert_succ (by omega)
    · have heq : j % N + 1 = N := by omega
      rw [heq, Nat.mod_self, Walk.getVert_zero]
      have := p.adj_getVert_succ (i := j % N) (by omega)
      have h2 := Walk.getVert_length p
      rw [hp] at h2
      rwa [heq, h2] at this
  have hℓdef : ∃ ℓ : ℕ, ℓ + 1 = ⌈b / 2⌉₊ := ⟨⌈b / 2⌉₊ - 1, by
    have : 0 < ⌈b / 2⌉₊ := Nat.ceil_pos.2 (by positivity)
    omega⟩
  obtain ⟨ℓ, hℓ⟩ := hℓdef
  have hℓr : (ℓ : ℝ) + 1 = ⌈b / 2⌉₊ := by exact_mod_cast hℓ
  have hceil_lt : (⌈b / 2⌉₊ : ℝ) < b / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hceil_ge : b / 2 ≤ ⌈b / 2⌉₊ := Nat.le_ceil _
  have hℓlt : (ℓ : ℝ) < b / 2 := by linarith
  have hℓN : ℓ + 1 ≤ N := by
    have : ⌈b / 2⌉₊ ≤ τ := Nat.ceil_le.2 (by linarith)
    omega
  set M := Finset.univ.filter (fun v => T.degree v = 1) with hMdef
  have hM : ∀ x ∈ M, ∃ t, x = wk t := by
    intro x _
    obtain ⟨t, ht, htl⟩ := Walk.mem_support_iff_exists_getVert.1 (hall x)
    rw [hp] at htl
    by_cases htN : t = N
    · refine ⟨0, ?_⟩
      have h2 := Walk.getVert_length p
      rw [hp] at h2
      simp only [hwk, Nat.zero_mod, Walk.getVert_zero]
      rw [← ht, htN, h2]
    · refine ⟨t, ?_⟩
      simp only [hwk, Nat.mod_eq_of_lt (show t < N by omega)]
      exact ht.symm
  obtain ⟨i, hi⟩ := lsw_window wk N ℓ hNpos hℓN hper M hM
  refine ⟨(lswSeqWalk wk hadj i ℓ).toSubgraph, Walk.toSubgraph_connected _, ?_, ?_⟩
  · have h1 : ((lswSeqWalk wk hadj i ℓ).toSubgraph.edgeSet.ncard) ≤ ℓ := by
      rw [Walk.edgeSet_toSubgraph]
      have hs : (lswSeqWalk wk hadj i ℓ).edgeSet ⊆ ↑((lswSeqWalk wk hadj i ℓ).edges.toFinset) := by
        intro e he
        simpa using he
      calc _ ≤ (↑((lswSeqWalk wk hadj i ℓ).edges.toFinset) : Set (Sym2 V)).ncard :=
            Set.ncard_le_ncard hs (Finset.finite_toSet _)
        _ = (lswSeqWalk wk hadj i ℓ).edges.toFinset.card := Set.ncard_coe_finset _
        _ ≤ (lswSeqWalk wk hadj i ℓ).edges.length := List.toFinset_card_le _
        _ = ℓ := by rw [Walk.length_edges, lswSeqWalk_length]
    have : ((lswSeqWalk wk hadj i ℓ).toSubgraph.edgeSet.ncard : ℝ) ≤ ℓ := by exact_mod_cast h1
    have : b / 2 = β / 2 * n := by rw [hb]; ring
    linarith
  · have hset : ({v | v ∈ (lswSeqWalk wk hadj i ℓ).toSubgraph.verts ∧ T.degree v = 1} : Set V)
        = ↑(M.filter (fun x => ∃ j ≤ ℓ, x = wk (i + j))) := by
      ext v
      simp only [Set.mem_setOf_eq, Walk.mem_verts_toSubgraph, lswSeqWalk_mem, Finset.coe_filter,
        hMdef, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [hset, Set.ncard_coe_finset]
    set k := (M.filter (fun x => ∃ j ≤ ℓ, x = wk (i + j))).card with hk
    have hi' : (M.card : ℝ) * ((ℓ : ℝ) + 1) ≤ (N : ℝ) * k := by exact_mod_cast hi
    have hNr : (N : ℝ) = 2 * τ := by rw [hN]; push_cast; ring
    have hτr : (0 : ℝ) < τ := by exact_mod_cast hτpos
    have hm0 : (0 : ℝ) ≤ M.card := Nat.cast_nonneg _
    have key : b * τ ≤ 4 * γ * k * τ := by
      have e1 : (M.card : ℝ) * (b / 2) ≤ 2 * τ * k := by
        calc (M.card : ℝ) * (b / 2) ≤ M.card * ((ℓ : ℝ) + 1) := by
              apply mul_le_mul_of_nonneg_left _ hm0; linarith
          _ ≤ _ := by rw [← hNr]; exact hi'
      have e2 : (τ : ℝ) * b ≤ γ * M.card * b := mul_le_mul_of_nonneg_right hτm hbpos.le
      nlinarith
    have key2 : b ≤ 4 * γ * k := le_of_mul_le_mul_right key hτr
    have : β / (4 * γ) * n = b / (4 * γ) := by rw [hb]; ring
    rw [this, div_le_iff₀ (by positivity)]
    linarith
