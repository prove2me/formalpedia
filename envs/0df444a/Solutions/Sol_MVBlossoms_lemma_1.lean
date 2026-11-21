-- Prove2me | solution 1 for MVBlossoms.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:53:13.26335+00:00
-- url     : https://prove2.me/submissions/011e1c4b-7e56-4392-a33a-153254aefbb6

import Mathlib
import Definitions.Def_MVBlossoms_evenLevel
import Definitions.Def_MVBlossoms_oddLevel
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_edgeTenacity
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_IsBridge

namespace Aux_MV1

open MVBlossoms SimpleGraph

variable {V : Type} {G : SimpleGraph V}

theorem alt_parity {S : Set (Sym2 V)} (l : List (Sym2 V))
    (hc : l.IsChain (fun e e' => (e ∈ S ↔ e' ∉ S)))
    (h0 : ∀ (h : 0 < l.length), l[0] ∉ S) :
    ∀ (k : ℕ) (hk : k < l.length), (l[k] ∈ S ↔ Odd k) := by
  intro k
  induction k with
  | zero =>
    intro hk
    exact ⟨fun h => absurd h (h0 hk), fun h => absurd h (by decide)⟩
  | succ k ih =>
    intro hk
    have hR := hc.getElem k hk
    have ih' := ih (by omega)
    rw [Nat.odd_add_one]
    constructor
    · intro h hk'
      exact (hR.mp (ih'.mpr hk')) h
    · intro h
      by_contra h'
      exact h (ih'.mp (hR.mpr h'))

theorem first_not_mem (M : G.Subgraph) {f x : V} (hf : BergeMatching.Core.IsNeutral M f)
    (p : G.Walk f x) : ∀ (h : 0 < p.edges.length), p.edges[0] ∉ M.edgeSet := by
  cases p with
  | nil => intro h; simp at h
  | cons hadj q =>
    intro _
    simp only [Walk.edges_cons, List.getElem_cons_zero]
    exact fun hm => hf _ hm (Sym2.mem_mk_left _ _)

theorem edges_getElem' {f x : V} (p : G.Walk f x) (n : ℕ) (h : n < p.edges.length) :
    p.edges[n] = s(p.getVert n, p.getVert (n + 1)) := by
  have h' : n < p.darts.length := by
    rw [Walk.length_darts]; rwa [Walk.length_edges] at h
  have e := Walk.darts_getElem_eq_getVert n h'
  simp only [Walk.edges, List.getElem_map, e]
  try rfl

theorem walk_parity (M : G.Subgraph) {f x : V} (hf : BergeMatching.Core.IsNeutral M f)
    (p : G.Walk f x) (halt : BergeMatching.Core.IsAlternatingWrt M.edgeSet p) (k : ℕ)
    (hk : k < p.length) : s(p.getVert k, p.getVert (k + 1)) ∈ M.edgeSet ↔ Odd k := by
  have hk' : k < p.edges.length := by rw [Walk.length_edges]; exact hk
  rw [← edges_getElem' p k hk']
  exact alt_parity p.edges halt.2 (first_not_mem M hf p) k hk'

theorem last_not_mem (M : G.Subgraph) {f x : V} (hf : BergeMatching.Core.IsNeutral M f)
    (p : G.Walk f x) (hc : p.edges.IsChain (fun e e' => (e ∈ M.edgeSet ↔ e' ∉ M.edgeSet)))
    (hodd : Odd p.length) : ∀ e ∈ p.edges.getLast?, e ∉ M.edgeSet := by
  intro e he
  rw [Option.mem_def, List.getLast?_eq_getElem?, List.getElem?_eq_some_iff] at he
  obtain ⟨hlt, rfl⟩ := he
  intro hm
  have h1 := (alt_parity p.edges hc (first_not_mem M hf p) _ hlt).mp hm
  rw [Walk.length_edges] at h1
  have h2 := Nat.odd_iff.mp h1
  have h3 := Nat.odd_iff.mp hodd
  omega

theorem match_unique (M : G.Subgraph) (hM : M.IsMatching) {v w u : V}
    (h1 : s(v, w) ∈ M.edgeSet) (h2 : s(v, u) ∈ M.edgeSet) : w = u := by
  rw [Subgraph.mem_edgeSet] at h1 h2
  exact (hM (M.edge_vert h1)).unique h1 h2

theorem not_mem_support (M : G.Subgraph) (hM : M.IsMatching) {f u v : V}
    (hf : BergeMatching.Core.IsNeutral M f) (p : G.Walk f u) (hp : p.IsPath)
    (halt : BergeMatching.Core.IsAlternatingWrt M.edgeSet p) (hodd : Odd p.length)
    (huv : s(u, v) ∈ M.edgeSet) : v ∉ p.support := by
  intro hv
  obtain ⟨j, hj, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  have hvu : v ≠ u := (M.adj_sub (Subgraph.mem_edgeSet.mp huv)).ne.symm
  have huv' : s(v, u) ∈ M.edgeSet := by rw [Sym2.eq_swap]; exact huv
  have hjL : j ≠ p.length := by
    intro e
    rw [e, Walk.getVert_length] at hj
    exact hvu hj.symm
  have hj0 : j ≠ 0 := by
    intro e
    rw [e, Walk.getVert_zero] at hj
    have : f ∈ s(u, v) := by rw [hj]; exact Sym2.mem_mk_right u v
    exact hf _ huv this
  have hjlt : j < p.length := lt_of_le_of_ne hjle hjL
  have hoddL := Nat.odd_iff.mp hodd
  rcases Nat.even_or_odd j with hje | hjo
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hje' := Nat.even_iff.mp hje
    have hodd_i : Odd i := Nat.odd_iff.mpr (by omega)
    have hm := (walk_parity M hf p halt i (by omega)).mpr hodd_i
    rw [hj] at hm
    have hm' : s(v, p.getVert i) ∈ M.edgeSet := by rw [Sym2.eq_swap]; exact hm
    have hiu := match_unique M hM hm' huv'
    have hinj := hp.getVert_injOn (show i ≤ p.length by omega) (show p.length ≤ p.length from le_rfl)
      (by rw [hiu, Walk.getVert_length])
    omega
  · have hm := (walk_parity M hf p halt j hjlt).mpr hjo
    rw [hj] at hm
    have hiu := match_unique M hM hm huv'
    have hinj := hp.getVert_injOn (show j + 1 ≤ p.length by omega)
      (show p.length ≤ p.length from le_rfl) (by rw [hiu, Walk.getVert_length])
    have hjo' := Nat.odd_iff.mp hjo
    omega

theorem extend (M : G.Subgraph) (hM : M.IsMatching) {f u v : V} (p : G.Walk f u)
    (hp : IsAltPathFromUnmatched M p) (hodd : Odd p.length) (huv : s(u, v) ∈ M.edgeSet)
    (hadj : G.Adj u v) :
    IsAltPathFromUnmatched M (p.concat hadj) ∧ Even (p.concat hadj).length := by
  have hnot := not_mem_support M hM hp.1 p hp.2.1 hp.2.2 hodd huv
  have hpath : (p.concat hadj).IsPath := (Walk.concat_isPath_iff hadj).mpr ⟨hp.2.1, hnot⟩
  refine ⟨⟨hp.1, hpath, hpath.isTrail, ?_⟩, ?_⟩
  · rw [Walk.edges_concat, List.concat_eq_append, List.isChain_append]
    refine ⟨hp.2.2.2, List.isChain_singleton _, fun x hx y hy => ?_⟩
    have hxn := last_not_mem M hp.1 p hp.2.2.2 hodd x hx
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact ⟨fun h => absurd h hxn, fun h => absurd huv h⟩
  · rw [Walk.length_concat]
    exact Nat.even_iff.mpr (by have := Nat.odd_iff.mp hodd; omega)

theorem restrict (M : G.Subgraph) (hM : M.IsMatching) {f u v : V} (q : G.Walk f v)
    (hq : IsAltPathFromUnmatched M q) (heven : Even q.length) (huv : s(u, v) ∈ M.edgeSet) :
    ∃ q' : G.Walk f u, IsAltPathFromUnmatched M q' ∧ Odd q'.length ∧ q'.length + 1 = q.length := by
  have huv' : s(v, u) ∈ M.edgeSet := by rw [Sym2.eq_swap]; exact huv
  cases q with
  | nil =>
    exfalso
    exact hq.1 _ huv (Sym2.mem_mk_right _ _)
  | cons h q₁ =>
    obtain ⟨x, q₀, h₀, he⟩ := Walk.exists_cons_eq_concat h q₁
    rw [he] at hq heven ⊢
    have hlen0 : (q₀.concat h₀).length = q₀.length + 1 := Walk.length_concat q₀ h₀
    rw [hlen0] at heven
    have hodd0 : Odd q₀.length := Nat.odd_iff.mpr (by have := Nat.even_iff.mp heven; omega)
    have hchain := hq.2.2.2
    rw [Walk.edges_concat, List.concat_eq_append, List.isChain_append] at hchain
    obtain ⟨hc0, _, hj⟩ := hchain
    have hpath0 : q₀.IsPath := ((Walk.concat_isPath_iff h₀).mp hq.2.1).1
    have hxv : s(x, v) ∈ M.edgeSet := by
      have hne : q₀.edges ≠ [] := by
        intro hnil
        have h4 := congrArg List.length hnil
        rw [Walk.length_edges, List.length_nil] at h4
        have h5 := Nat.odd_iff.mp hodd0
        omega
      obtain ⟨e, he'⟩ : ∃ e, q₀.edges.getLast? = some e := by
        cases hl : q₀.edges.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
        | some e => exact ⟨e, rfl⟩
      have hmem : e ∈ q₀.edges.getLast? := Option.mem_def.mpr he'
      have hen := last_not_mem M hq.1 q₀ hc0 hodd0 e hmem
      have hR := hj e hmem (s(x, v)) (by simp)
      by_contra hcon
      exact hen (hR.mpr hcon)
    have hxv' : s(v, x) ∈ M.edgeSet := by rw [Sym2.eq_swap]; exact hxv
    have hxu : x = u := match_unique M hM hxv' huv'
    subst hxu
    refine ⟨q₀, ⟨hq.1, hpath0, hpath0.isTrail, hc0⟩, hodd0, ?_⟩
    rw [hlen0]

theorem attain (M : G.Subgraph) (v : V) (P : ℕ → Prop)
    (h : (⨅ (f : V) (p : G.Walk f v) (_ : IsAltPathFromUnmatched M p) (_ : P p.length),
      (p.length : ℕ∞)) ≠ ⊤) :
    ∃ (f : V) (p : G.Walk f v), IsAltPathFromUnmatched M p ∧ P p.length ∧
      (p.length : ℕ∞) = ⨅ (f : V) (p : G.Walk f v) (_ : IsAltPathFromUnmatched M p)
        (_ : P p.length), (p.length : ℕ∞) := by
  classical
  have hne : ∃ n, ∃ (f : V) (p : G.Walk f v), IsAltPathFromUnmatched M p ∧ P p.length ∧
      p.length = n := by
    by_contra hcon
    apply h
    simp only [iInf_eq_top]
    intro f p hp hP
    exact absurd ⟨p.length, f, p, hp, hP, rfl⟩ hcon
  obtain ⟨f, p, hp, hP, hlen⟩ := Nat.find_spec hne
  refine ⟨f, p, hp, hP, le_antisymm ?_ ?_⟩
  · apply le_iInf; intro f'; apply le_iInf; intro p'; apply le_iInf; intro hp'
    apply le_iInf; intro hP'
    rw [hlen]
    exact_mod_cast Nat.find_min' hne ⟨f', p', hp', hP', rfl⟩
  · exact iInf_le_of_le f (iInf_le_of_le p (iInf_le_of_le hp (iInf_le_of_le hP le_rfl)))

theorem attain_odd (M : G.Subgraph) {u : V} (h : oddLevel M u ≠ ⊤) :
    ∃ (f : V) (p : G.Walk f u), IsAltPathFromUnmatched M p ∧ Odd p.length ∧
      (p.length : ℕ∞) = oddLevel M u :=
  attain M u Odd h

theorem attain_even (M : G.Subgraph) {u : V} (h : evenLevel M u ≠ ⊤) :
    ∃ (f : V) (p : G.Walk f u), IsAltPathFromUnmatched M p ∧ Even p.length ∧
      (p.length : ℕ∞) = evenLevel M u :=
  attain M u Even h

theorem odd_le (M : G.Subgraph) {f u : V} (p : G.Walk f u) (hp : IsAltPathFromUnmatched M p)
    (hodd : Odd p.length) : oddLevel M u ≤ p.length := by
  unfold oddLevel
  exact iInf_le_of_le f (iInf_le_of_le p (iInf_le_of_le hp (iInf_le_of_le hodd le_rfl)))

theorem even_le (M : G.Subgraph) {f u : V} (p : G.Walk f u) (hp : IsAltPathFromUnmatched M p)
    (heven : Even p.length) : evenLevel M u ≤ p.length := by
  unfold evenLevel
  exact iInf_le_of_le f (iInf_le_of_le p (iInf_le_of_le hp (iInf_le_of_le heven le_rfl)))

theorem even_eq (M : G.Subgraph) (hM : M.IsMatching) {u v : V} (huv : s(u, v) ∈ M.edgeSet)
    (hfu : oddLevel M u ≠ ⊤) : evenLevel M v = oddLevel M u + 1 := by
  have hadj : G.Adj u v := M.adj_sub (Subgraph.mem_edgeSet.mp huv)
  obtain ⟨f, p, hp, hodd, hlen⟩ := attain_odd M hfu
  obtain ⟨hP, heven⟩ := extend M hM p hp hodd huv hadj
  have hle : evenLevel M v ≤ oddLevel M u + 1 := by
    calc evenLevel M v ≤ ((p.concat hadj).length : ℕ∞) := even_le M _ hP heven
      _ = oddLevel M u + 1 := by rw [Walk.length_concat, ← hlen, Nat.cast_add, Nat.cast_one]
  apply le_antisymm hle
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfu
  have h1 : oddLevel M u + 1 ≠ ⊤ := by
    rw [← ha]
    exact_mod_cast ENat.coe_ne_top (a + 1)
  have hfv : evenLevel M v ≠ ⊤ := ne_top_of_le_ne_top h1 hle
  obtain ⟨f', q, hq, hev, hqlen⟩ := attain_even M hfv
  obtain ⟨q', hq', hodd', hlen'⟩ := restrict M hM q hq hev huv
  rw [← hqlen, ← hlen']
  have := odd_le M q' hq' hodd'
  push_cast
  exact add_le_add this le_rfl

theorem pred_iff (M : G.Subgraph) (hM : M.IsMatching) {u v : V} (huv : s(u, v) ∈ M.edgeSet)
    (hfu : oddLevel M u ≠ ⊤) : IsPred M u v ↔ oddLevel M u + 1 ≤ oddLevel M v := by
  have hE := even_eq M hM huv hfu
  constructor
  · rintro ⟨f, q, h, hor, hlen⟩
    rcases hor with hev | hodd
    · have : evenLevel M v ≤ oddLevel M v := by
        rw [← hev.2.2, hlen]
        exact min_le_right _ _
      rw [← hE]
      exact this
    · exfalso
      obtain ⟨hP, hodd', _⟩ := hodd
      have hmem : s(u, v) ∈ (q.concat h).edges.getLast? := by
        rw [Walk.edges_concat]
        simp
      exact last_not_mem M hP.1 (q.concat h) hP.2.2.2 hodd' _ hmem huv
  · intro hle
    obtain ⟨f, p, hp, hodd, hlen⟩ := attain_odd M hfu
    have hadj : G.Adj u v := M.adj_sub (Subgraph.mem_edgeSet.mp huv)
    obtain ⟨hP, heven⟩ := extend M hM p hp hodd huv hadj
    have hlenP : ((p.concat hadj).length : ℕ∞) = evenLevel M v := by
      rw [hE, Walk.length_concat, ← hlen, Nat.cast_add, Nat.cast_one]
    refine ⟨f, p, hadj, Or.inl ⟨hP, heven, hlenP⟩, ?_⟩
    rw [hlenP]
    show evenLevel M v = min (evenLevel M v) (oddLevel M v)
    rw [min_eq_left]
    rw [hE]
    exact hle

end Aux_MV1

open MVBlossoms in
theorem solution {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M)
    (u v : V) (huv : s(u, v) ∈ M.edgeSet) (hfin : edgeTenacity M u v ≠ ⊤) :
    evenLevel M v = oddLevel M u + 1 ∧ tenacity M v = edgeTenacity M u v ∧
      ∀ i : ℕ, edgeTenacity M u v = ((2 * i + 1 : ℕ) : ℕ∞) →
        (IsBridge M u v ↔ oddLevel M u = (i : ℕ∞) ∧ oddLevel M v = (i : ℕ∞)) := by
  have hET : edgeTenacity M u v = oddLevel M u + oddLevel M v + 1 := by
    unfold edgeTenacity
    rw [if_pos huv]
  have hfu : oddLevel M u ≠ ⊤ := by
    intro h
    rw [hET, h] at hfin
    simp at hfin
  have hfv : oddLevel M v ≠ ⊤ := by
    intro h
    rw [hET, h] at hfin
    simp at hfin
  have huv' : s(v, u) ∈ M.edgeSet := by rw [Sym2.eq_swap]; exact huv
  have hadj : G.Adj u v := M.adj_sub (SimpleGraph.Subgraph.mem_edgeSet.mp huv)
  have hE := Aux_MV1.even_eq M hM huv hfu
  refine ⟨hE, ?_, ?_⟩
  · unfold tenacity
    rw [hE, hET, add_right_comm]
  · intro i hi
    rw [hET] at hi
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfu
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hfv
    rw [← ha, ← hb] at hi
    have hab : a + b = 2 * i := by
      have : a + b + 1 = 2 * i + 1 := by exact_mod_cast hi
      omega
    have h1 := Aux_MV1.pred_iff M hM huv hfu
    have h2 := Aux_MV1.pred_iff M hM huv' hfv
    rw [← ha, ← hb] at h1 h2
    unfold IsBridge IsProp
    rw [h1, h2, ← ha, ← hb]
    have e1 : ((a : ℕ∞) + 1 ≤ (b : ℕ∞)) ↔ a + 1 ≤ b := by norm_cast
    have e2 : ((b : ℕ∞) + 1 ≤ (a : ℕ∞)) ↔ b + 1 ≤ a := by norm_cast
    have e3 : ((a : ℕ∞) = (i : ℕ∞)) ↔ a = i := by norm_cast
    have e4 : ((b : ℕ∞) = (i : ℕ∞)) ↔ b = i := by norm_cast
    rw [e1, e2, e3, e4]
    constructor
    · rintro ⟨_, hn⟩
      constructor <;> omega
    · rintro ⟨rfl, rfl⟩
      exact ⟨hadj, by omega⟩
