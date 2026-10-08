-- Prove2me | solution 1 for MatousekLP.Integrality.konig
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T15:16:16.916586+00:00
-- url     : https://prove2.me/submissions/5f8fb1b4-32af-4fea-94ce-061fccc27961

/-
König's theorem for bipartite graphs (maximum matching = minimum vertex cover), derived from
Menger's theorem (`Menger.menger_set`, a Proved platform theorem).

Take `A = X`, `B = Y` for a bipartition `(X, Y)`. Every edge `xy` is an `X`–`Y` path, so an `X`–`Y`
separator is a vertex cover and has at least `τ` vertices, where `τ` is the minimum vertex cover size.
Menger gives `τ` vertex-disjoint `X`–`Y` paths. As `X ∩ Y = ∅` each path has at least two vertices,
and its first edge is an edge of `G`; the first edges of disjoint paths are distinct and pairwise
disjoint, so they form a matching of size `τ`. Conversely a matching has at most `τ` edges because each
edge needs its own cover vertex. Hence the matching is maximum and the cover is minimum.
-/
import Mathlib
import Definitions.Def_MatousekLP_Integrality_BipartiteGraph
import Definitions.Def_Menger_Linkage
import Theorems.Thm_Menger_menger_set

set_option autoImplicit false

namespace KonigLib
open MatousekLP.Integrality Menger

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_min_cover (G : SimpleGraph V) :
    ∃ C : Finset V, G.IsVertexCover (C : Set V) ∧
      ∀ C' : Finset V, G.IsVertexCover (C' : Set V) → C.card ≤ C'.card := by
  classical
  obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun C : Finset V => G.IsVertexCover (C : Set V))) Finset.card
    ⟨Finset.univ, by simp [SimpleGraph.isVertexCover_univ]⟩
  exact ⟨C, (Finset.mem_filter.1 hC).2, fun C' hC' => hmin C' (by simpa using hC')⟩

theorem first_edge {G : SimpleGraph V} {X Y : Finset V} (hXY : Disjoint X Y) {p : List V}
    (hp : IsABPath G Finset.univ X Y p) :
    ∃ a b : V, G.Adj a b ∧ a ∈ p ∧ b ∈ p ∧ a ∈ X := by
  obtain ⟨hne, hnd, hch, _, ⟨a, ha, haX⟩, ⟨b', hb, hbY⟩⟩ := hp
  cases p with
  | nil => exact absurd rfl hne
  | cons a' t =>
    cases t with
    | nil =>
      simp at ha hb
      subst ha; subst hb
      exact absurd (Finset.mem_inter.2 ⟨haX, hbY⟩) (by simpa [Finset.disjoint_iff_inter_eq_empty.1 hXY] using Finset.notMem_empty _)
    | cons b t' =>
      simp at ha
      subst ha
      exact ⟨a', b, (List.isChain_cons_cons.1 hch).1, by simp, by simp, haX⟩

theorem path_pair {G : SimpleGraph V} {X Y : Finset V} {a b : V} (ha : a ∈ X) (hb : b ∈ Y)
    (hab : G.Adj a b) : IsABPath G Finset.univ X Y [a, b] :=
  ⟨by simp, by simp [hab.ne], List.isChain_cons_cons.2 ⟨hab, List.IsChain.singleton _⟩,
    fun v _ => Finset.mem_univ v, ⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩

theorem konig_core (G : SimpleGraph V) (hG : IsBipartite G) :
    ∃ M : Finset (Sym2 V), IsMatching G M ∧
      (∀ M' : Finset (Sym2 V), IsMatching G M' → M'.card ≤ M.card) ∧
      ∃ C : Finset V, G.IsVertexCover (C : Set V) ∧
        (∀ C' : Finset V, G.IsVertexCover (C' : Set V) → C.card ≤ C'.card) ∧
        M.card = C.card := by
  classical
  obtain ⟨X, Y, hXY, _, hadj⟩ := hG
  obtain ⟨C, hC, hmin⟩ := exists_min_cover G
  have hlink : HasLinkage G Finset.univ X Y C.card := by
    refine menger_set G Finset.univ X Y (Finset.subset_univ _) (Finset.subset_univ _) C.card
      (fun Z _ hZ => hmin Z ?_)
    intro v w hvw
    rcases hadj v w hvw with ⟨hv, hw⟩ | ⟨hv, hw⟩
    · obtain ⟨z, hz, hzp⟩ := hZ _ (path_pair hv hw hvw)
      simp at hzp
      rcases hzp with rfl | rfl
      · exact Or.inl (Finset.mem_coe.2 hz)
      · exact Or.inr (Finset.mem_coe.2 hz)
    · obtain ⟨z, hz, hzp⟩ := hZ _ (path_pair hw hv hvw.symm)
      simp at hzp
      rcases hzp with rfl | rfl
      · exact Or.inr (Finset.mem_coe.2 hz)
      · exact Or.inl (Finset.mem_coe.2 hz)
  have hub : ∀ M' : Finset (Sym2 V), IsMatching G M' → M'.card ≤ C.card := by
    intro M' hM'
    have hcov : ∀ e' ∈ M', ∃ c ∈ C, c ∈ e' := by
      intro e' he'
      have hedge := hM'.1 e' he'
      induction e' using Sym2.ind with
      | h u w =>
        have hadj' : G.Adj u w := hedge
        rcases hC hadj' with h | h
        · exact ⟨u, Finset.mem_coe.1 h, Sym2.mem_mk_left u w⟩
        · exact ⟨w, Finset.mem_coe.1 h, Sym2.mem_mk_right u w⟩
    by_cases hM'e : M' = ∅
    · simp [hM'e]
    obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.2 hM'e
    obtain ⟨c0, _, _⟩ := hcov e0 he0
    haveI : Nonempty V := ⟨c0⟩
    choose! cc hcc using hcov
    refine Finset.card_le_card_of_injOn cc (fun e' he' => Finset.mem_coe.2 (hcc e' he').1) ?_
    intro e1 h1 e2 h2 h12
    have hc1 := (hcc e1 h1).2
    have hc2 := (hcc e2 h2).2
    have hle := hM'.2 (cc e1)
    exact Finset.card_le_one.1 hle e1 (Finset.mem_filter.2 ⟨h1, hc1⟩) e2
      (Finset.mem_filter.2 ⟨h2, h12 ▸ hc2⟩)
  obtain ⟨L, hlen, hpaths, hpair⟩ := hlink
  by_cases hL : L = []
  · subst hL
    refine ⟨∅, ⟨by simp, by simp⟩, fun M' hM' => ?_, C, hC, hmin, ?_⟩
    · simpa [hlen.symm] using hub M' hM'
    · simpa using hlen
  obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil L hL
  obtain ⟨a0, ha0, _⟩ := (hpaths p0 hp0).2.2.2.2.1
  haveI : Nonempty (Sym2 V) := ⟨s(a0, a0)⟩
  have hex : ∀ p ∈ L, ∃ e : Sym2 V, ∃ a b : V, e = s(a, b) ∧ G.Adj a b ∧ a ∈ p ∧ b ∈ p := by
    intro p hp
    obtain ⟨a, b, h1, h2, h3, _⟩ := first_edge hXY (hpaths p hp)
    exact ⟨s(a, b), a, b, rfl, h1, h2, h3⟩
  choose! e he using hex
  haveI hsymm : Std.Symm (fun p q : List V => ∀ v ∈ p, v ∉ q) :=
    ⟨fun p q h v hv hvq => h v hvq hv⟩
  have hdisj : ∀ p ∈ L, ∀ q ∈ L, p ≠ q → ∀ v ∈ p, v ∉ q := fun p hp q hq hpq =>
    hpair.forall hp hq hpq
  have hnd : L.Nodup := by
    refine (List.Pairwise.and_mem.1 hpair).imp ?_
    rintro p q ⟨hp, hq, h⟩ rfl
    obtain ⟨a, ha, _⟩ := (hpaths p hp).2.2.2.2.1
    exact h a (List.mem_of_mem_head? ha) (List.mem_of_mem_head? ha)
  have hmem : ∀ p ∈ L, ∀ v ∈ e p, v ∈ p := by
    intro p hp v hv
    obtain ⟨a, b, he', _, ha, hb⟩ := he p hp
    rw [he'] at hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact ha
    · exact hb
  have hinj : ∀ p ∈ L, ∀ q ∈ L, e p = e q → p = q := by
    intro p hp q hq hpq
    by_contra hne
    obtain ⟨a, b, he', _, ha, hb⟩ := he p hp
    have : a ∈ e q := by rw [← hpq, he']; exact Sym2.mem_mk_left a b
    exact hdisj p hp q hq hne a ha (hmem q hq a this)
  set M : Finset (Sym2 V) := L.toFinset.image e with hM
  have hMcard : M.card = C.card := by
    rw [hM, Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd, hlen]
    intro p hp q hq h
    exact hinj p (List.mem_toFinset.1 hp) q (List.mem_toFinset.1 hq) h
  have hmatch : IsMatching G M := by
    refine ⟨fun e' he' => ?_, fun v => ?_⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 he'
      obtain ⟨a, b, he'', hab, _, _⟩ := he p (List.mem_toFinset.1 hp)
      rw [he'']
      exact hab
    · rw [Finset.card_le_one]
      intro e1 h1 e2 h2
      obtain ⟨_, he1⟩ := Finset.mem_filter.1 h1
      obtain ⟨_, he2⟩ := Finset.mem_filter.1 h2
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 h1).1
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 h2).1
      have hp' := List.mem_toFinset.1 hp
      have hq' := List.mem_toFinset.1 hq
      have : p = q := by
        by_contra hne
        exact hdisj p hp' q hq' hne v (hmem p hp' v he1) (hmem q hq' v he2)
      rw [this]
  exact ⟨M, hmatch, fun M' hM' => hMcard ▸ hub M' hM', C, hC, hmin, hMcard⟩

end KonigLib

open MatousekLP.Integrality in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : IsBipartite G) :
    ∃ M : Finset (Sym2 V), IsMatching G M ∧
      (∀ M' : Finset (Sym2 V), IsMatching G M' → M'.card ≤ M.card) ∧
      ∃ C : Finset V, G.IsVertexCover (C : Set V) ∧
        (∀ C' : Finset V, G.IsVertexCover (C' : Set V) → C.card ≤ C'.card) ∧
        M.card = C.card :=
  KonigLib.konig_core G hG
