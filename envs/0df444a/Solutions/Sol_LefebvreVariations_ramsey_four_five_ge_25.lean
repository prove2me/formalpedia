-- Prove2me | solution 1 for LefebvreVariations.ramsey_four_five_ge_25
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-25T23:07:04.367645+00:00
-- url     : https://prove2.me/submissions/fee0fe04-c2af-47fd-ab56-d309653ce773

import Mathlib
import Definitions.Def_Erdos77_asymmetric_ramsey

set_option autoImplicit false


/-- The Ramsey property, for every finite vertex type with at least `n` vertices. -/
private def RP (a b n : ℕ) : Prop :=
  ∀ (α : Type) [Fintype α], n ≤ Fintype.card α → ∀ G : SimpleGraph α,
    (∃ s : Finset α, G.IsNClique a s) ∨ (∃ s : Finset α, Gᶜ.IsNClique b s)

private lemma RP_mono {a b n n' : ℕ} (h : RP a b n) (hn : n ≤ n') : RP a b n' :=
  fun α _ hc G => h α (hn.trans hc) G

private lemma RP_iff_mem (a b n : ℕ) :
    RP a b n ↔ n ∈ {n : ℕ | ∀ G : SimpleGraph (Fin n),
      (∃ s : Finset (Fin n), G.IsNClique a s) ∨ (∃ s : Finset (Fin n), Gᶜ.IsNClique b s)} := by
  constructor
  · intro h G
    exact h (Fin n) (by simp) G
  · intro h α _ hc G
    let f : Fin n ↪ α := (Fin.castLEEmb hc).trans (Fintype.equivFin α).symm.toEmbedding
    have hcomp : (G.comap f)ᶜ = Gᶜ.comap f := by
      ext u v; simp [f.injective.ne_iff]
    rcases h (G.comap f) with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact Or.inl ⟨s.map f, (hs.map).mono (SimpleGraph.map_comap_le _ _)⟩
    · rw [hcomp] at hs
      exact Or.inr ⟨s.map f, (hs.map).mono (SimpleGraph.map_comap_le _ _)⟩

/-- Swapping the roles of cliques and independent sets (pass to the complement). -/
private lemma RP_symm {a b n : ℕ} (h : RP a b n) : RP b a n := by
  intro α _ hc G
  rcases h α hc Gᶜ with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact Or.inr ⟨s, hs⟩
  · rw [compl_compl] at hs
    exact Or.inl ⟨s, hs⟩

/-- `R(2, b) ≤ b`: an edge, or the whole vertex set is independent. -/
private lemma RP_two (b : ℕ) : RP 2 b b := by
  classical
  intro α _ hc G
  by_cases h : ∃ u v, G.Adj u v
  · obtain ⟨u, v, huv⟩ := h
    left
    refine ⟨{u, v}, ⟨?_, ?_⟩⟩
    · rw [Finset.coe_pair]; exact SimpleGraph.isClique_pair.mpr (fun _ => huv)
    · exact Finset.card_pair huv.ne
  · push Not at h
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset α))
      (by simpa using hc)
    right
    refine ⟨s, ⟨?_, hs⟩⟩
    intro x _ y _ hxy
    exact (SimpleGraph.compl_adj G x y).mpr ⟨hxy, h x y⟩

/-- Lift a clique of the neighbourhood of `v` in `H` to a clique of `H` containing `v`. -/
private lemma lift_insert {α : Type} [DecidableEq α] (H : SimpleGraph α) (v : α) (c : ℕ)
    (s : Finset (H.neighborSet v))
    (h : (H.comap (Function.Embedding.subtype _)).IsNClique c s) :
    H.IsNClique (c + 1) (insert v (s.map (Function.Embedding.subtype _))) := by
  refine ((h.map).mono (SimpleGraph.map_comap_le _ _)).insert ?_
  intro b hb
  simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
  obtain ⟨w, -, rfl⟩ := hb
  exact w.2

/-- Lift a clique of the complement of an induced subgraph. -/
private lemma lift_compl {α : Type} (H : SimpleGraph α) (S : Set α) (c : ℕ)
    (s : Finset S)
    (h : (H.comap (Function.Embedding.subtype (· ∈ S)))ᶜ.IsNClique c s) :
    Hᶜ.IsNClique c (s.map (Function.Embedding.subtype _)) := by
  have hcomp : (H.comap (Function.Embedding.subtype (· ∈ S)))ᶜ
      = Hᶜ.comap (Function.Embedding.subtype (· ∈ S)) := by
    ext u v; simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj,
      Function.Embedding.coe_subtype, ne_eq, Subtype.ext_iff]
  rw [hcomp] at h
  exact (h.map).mono (SimpleGraph.map_comap_le _ _)

/-- The pigeonhole step (Erdős–Szekeres). -/
private lemma RP_step {a b n1 n2 : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h1 : RP (a - 1) b n1) (h2 : RP a (b - 1) n2) (hpos : 0 < n1 + n2) :
    RP a b (n1 + n2) := by
  classical
  intro α _ hc G
  have hcard : 0 < Fintype.card α := lt_of_lt_of_le hpos hc
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hcard
  have hdeg := SimpleGraph.degree_compl G v
  by_cases hN : n1 ≤ G.degree v
  · have hN' : n1 ≤ Fintype.card (G.neighborSet v) := by
      rwa [SimpleGraph.card_neighborSet_eq_degree]
    rcases h1 (G.neighborSet v) hN' (G.comap (Function.Embedding.subtype _)) with
      ⟨s, hs⟩ | ⟨s, hs⟩
    · left
      have := lift_insert G v (a - 1) s hs
      rw [Nat.sub_add_cancel ha] at this
      exact ⟨_, this⟩
    · right
      exact ⟨_, lift_compl G (G.neighborSet v) b s hs⟩
  · have hM : n2 ≤ Gᶜ.degree v := by omega
    have hM' : n2 ≤ Fintype.card (Gᶜ.neighborSet v) := by
      rwa [SimpleGraph.card_neighborSet_eq_degree]
    rcases h2 (Gᶜ.neighborSet v) hM' (Gᶜ.comap (Function.Embedding.subtype _))ᶜ with
      ⟨s, hs⟩ | ⟨s, hs⟩
    · left
      have := lift_compl Gᶜ (Gᶜ.neighborSet v) a s hs
      rw [compl_compl] at this
      exact ⟨_, this⟩
    · right
      rw [compl_compl] at hs
      have := lift_insert Gᶜ v (b - 1) s hs
      rw [Nat.sub_add_cancel hb] at this
      exact ⟨_, this⟩

/-- Plain Erdős–Szekeres bounds, enough to make the defining set of `R(4,5)` nonempty. -/
private lemma RP33 : RP 3 3 6 := RP_step (n1 := 3) (n2 := 3) (by norm_num) (by norm_num)
  (RP_two 3) (RP_symm (RP_two 3)) (by norm_num)

private lemma RP34 : RP 3 4 10 := RP_step (n1 := 4) (n2 := 6) (by norm_num) (by norm_num)
  (RP_two 4) RP33 (by norm_num)

private lemma RP44 : RP 4 4 20 := RP_step (n1 := 10) (n2 := 10) (by norm_num) (by norm_num)
  RP34 (RP_symm RP34) (by norm_num)

private lemma RP35 : RP 3 5 15 := RP_step (n1 := 5) (n2 := 10) (by norm_num) (by norm_num)
  (RP_two 5) RP34 (by norm_num)

private lemma RP45 : RP 4 5 35 := RP_step (n1 := 15) (n2 := 20) (by norm_num) (by norm_num)
  RP35 RP44 (by norm_num)

/-- A lower bound: if `RP a b N` fails while some `RP a b M` holds, then `N < R(a,b)`. -/
private lemma lt_ramsey {a b N M : ℕ} (hN : ¬ RP a b N) (hM : RP a b M) :
    N < Erdos77.asymmetricRamsey a b := by
  have hR : RP a b (Erdos77.asymmetricRamsey a b) := by
    rw [RP_iff_mem]
    exact Nat.sInf_mem ⟨M, (RP_iff_mem a b M).mp hM⟩
  by_contra hle
  push Not at hle
  exact hN (RP_mono hR hle)

private lemma four_of_clique {α : Type} [DecidableEq α] {H : SimpleGraph α} {s : Finset α}
    (h : H.IsNClique 4 s) : ∃ a b c d, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧ H.Adj a b ∧
      H.Adj a c ∧ H.Adj b c ∧ H.Adj a d ∧ H.Adj b d ∧ H.Adj c d := by
  have hc := h.card_eq
  obtain ⟨d, hd⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have h3 : (s.erase d).card = 3 := by rw [Finset.card_erase_of_mem hd]; omega
  obtain ⟨a, b, c, hab, hac, hbc, he⟩ := Finset.card_eq_three.mp h3
  have ha : a ∈ s.erase d := by rw [he]; simp
  have hb : b ∈ s.erase d := by rw [he]; simp
  have hc' : c ∈ s.erase d := by rw [he]; simp
  rw [Finset.mem_erase] at ha hb hc'
  exact ⟨a, b, c, d, ha.2, hb.2, hc'.2, hd, h.1 ha.2 hb.2 hab, h.1 ha.2 hc'.2 hac,
    h.1 hb.2 hc'.2 hbc, h.1 ha.2 hd ha.1, h.1 hb.2 hd hb.1, h.1 hc'.2 hd hc'.1⟩

private lemma five_of_clique {α : Type} [DecidableEq α] {H : SimpleGraph α} {s : Finset α}
    (h : H.IsNClique 5 s) : ∃ a b c d e, H.Adj a b ∧ H.Adj a c ∧ H.Adj b c ∧
      H.Adj a d ∧ H.Adj b d ∧ H.Adj c d ∧ H.Adj a e ∧ H.Adj b e ∧ H.Adj c e ∧ H.Adj d e := by
  have hc := h.card_eq
  obtain ⟨e, he⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, b, c, d, ha, hb, hc', hd, h1, h2, h3, h4, h5, h6⟩ :=
    four_of_clique (h.erase_of_mem he)
  rw [Finset.mem_erase] at ha hb hc' hd
  exact ⟨a, b, c, d, e, h1, h2, h3, h4, h5, h6, h.1 ha.2 he ha.1, h.1 hb.2 he hb.1,
    h.1 hc'.2 he hc'.1, h.1 hd.2 he hd.1⟩

/-! A circulant `(4,5)`-graph on `ℤ/24`: `i ~ j` iff `i - j ≡ ±1, ±2, ±4, ±8, ±9 (mod 24)`
(found by exhaustive search over the 4095 circulants on 24 vertices). Absence of `K₄` and
of independent `5`-sets is checked by two boolean searches evaluated by `decide`. -/

private def dist24 (d : ℕ) : Bool :=
  d == 1 || d == 2 || d == 4 || d == 8 || d == 9 ||
  d == 15 || d == 16 || d == 20 || d == 22 || d == 23

private def aB (i j : ℕ) : Bool := dist24 ((i + 24 - j) % 24)

private def cB (i j : ℕ) : Bool := i != j && !aB i j

private def chk4 : Bool :=
  (List.range 24).all fun a => (List.range 24).all fun b => !(aB a b) ||
    (List.range 24).all fun c => !(aB a c && aB b c) ||
      (List.range 24).all fun d => !(aB a d && aB b d && aB c d)

private def chk5 : Bool :=
  (List.range 24).all fun a => (List.range 24).all fun b => !(cB a b) ||
    (List.range 24).all fun c => !(cB a c && cB b c) ||
      (List.range 24).all fun d => !(cB a d && cB b d && cB c d) ||
        (List.range 24).all fun e => !(cB a e && cB b e && cB c e && cB d e)

set_option maxRecDepth 100000 in
private lemma chk4_true : chk4 = true := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private lemma chk5_true : chk5 = true := by decide

private lemma noK4_nat (a b c d : ℕ) (ha : a < 24) (hb : b < 24) (hc : c < 24) (hd : d < 24)
    (h1 : aB a b = true) (h2 : aB a c = true) (h3 : aB b c = true) (h4 : aB a d = true)
    (h5 : aB b d = true) (h6 : aB c d = true) : False := by
  have h := chk4_true
  simp only [chk4, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h a ha b hb with h' | h'
  · simp [h1] at h'
  rcases h' c hc with h' | h'
  · simp [h2, h3] at h'
  have h' := h' d hd
  simp [h4, h5, h6] at h'

private lemma noI5_nat (a b c d e : ℕ) (ha : a < 24) (hb : b < 24) (hc : c < 24) (hd : d < 24)
    (he : e < 24) (h1 : cB a b = true) (h2 : cB a c = true) (h3 : cB b c = true)
    (h4 : cB a d = true) (h5 : cB b d = true) (h6 : cB c d = true) (h7 : cB a e = true)
    (h8 : cB b e = true) (h9 : cB c e = true) (h10 : cB d e = true) : False := by
  have h := chk5_true
  simp only [chk5, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h a ha b hb with h' | h'
  · simp [h1] at h'
  rcases h' c hc with h' | h'
  · simp [h2, h3] at h'
  rcases h' d hd with h' | h'
  · simp [h4, h5, h6] at h'
  have h' := h' e he
  simp [h7, h8, h9, h10] at h'

private lemma aB_symm : ∀ i j : Fin 24, aB i.val j.val = true → aB j.val i.val = true := by
  decide

private lemma aB_irrefl : ∀ i : Fin 24, ¬ aB i.val i.val = true := by decide

private def C24 : SimpleGraph (Fin 24) where
  Adj i j := aB i.val j.val = true
  symm := ⟨aB_symm⟩
  loopless := ⟨aB_irrefl⟩

private lemma C24c_adj {i j : Fin 24} (h : C24ᶜ.Adj i j) : cB i.val j.val = true := by
  rw [SimpleGraph.compl_adj] at h
  obtain ⟨hne, hn⟩ := h
  have hne' : i.val ≠ j.val := Fin.val_ne_of_ne hne
  change ¬ aB i.val j.val = true at hn
  simp [cB, hne', hn]

private lemma C24_noK4 (a b c d : Fin 24) (h1 : C24.Adj a b) (h2 : C24.Adj a c)
    (h3 : C24.Adj b c) (h4 : C24.Adj a d) (h5 : C24.Adj b d) (h6 : C24.Adj c d) : False :=
  noK4_nat a b c d a.2 b.2 c.2 d.2 h1 h2 h3 h4 h5 h6

private lemma C24c_noK5 (a b c d e : Fin 24) (h1 : C24ᶜ.Adj a b) (h2 : C24ᶜ.Adj a c)
    (h3 : C24ᶜ.Adj b c) (h4 : C24ᶜ.Adj a d) (h5 : C24ᶜ.Adj b d) (h6 : C24ᶜ.Adj c d)
    (h7 : C24ᶜ.Adj a e) (h8 : C24ᶜ.Adj b e) (h9 : C24ᶜ.Adj c e) (h10 : C24ᶜ.Adj d e) : False :=
  noI5_nat a b c d e a.2 b.2 c.2 d.2 e.2 (C24c_adj h1) (C24c_adj h2) (C24c_adj h3)
    (C24c_adj h4) (C24c_adj h5) (C24c_adj h6) (C24c_adj h7) (C24c_adj h8) (C24c_adj h9)
    (C24c_adj h10)

private lemma not_RP45_24 : ¬ RP 4 5 24 := by
  intro h
  rcases h (Fin 24) (by simp) C24 with ⟨s, hs⟩ | ⟨s, hs⟩
  · obtain ⟨a, b, c, d, -, -, -, -, h1, h2, h3, h4, h5, h6⟩ := four_of_clique hs
    exact C24_noK4 a b c d h1 h2 h3 h4 h5 h6
  · obtain ⟨a, b, c, d, e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := five_of_clique hs
    exact C24c_noK5 a b c d e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem solution : 25 ≤ Erdos77.asymmetricRamsey 4 5 :=
  lt_ramsey not_RP45_24 RP45
