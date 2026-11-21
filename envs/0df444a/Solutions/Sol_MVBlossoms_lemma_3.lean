-- Prove2me | solution 1 for MVBlossoms.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:18:35.901594+00:00
-- url     : https://prove2.me/submissions/e5821ba8-9cfb-4134-a8b2-4b0b2e0a50c6

import Mathlib
import Definitions.Def_MVBlossoms_IsOuter
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_edgeTenacity
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_IsBridge

namespace Aux_MVB

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

/-! ### Sequences -/

/-- An alternating path from an unmatched vertex, as a sequence of vertices. -/
def APath (M : G.Subgraph) (n : ℕ) (x : ℕ → V) : Prop :=
  (∀ i < n, G.Adj (x i) (x (i + 1))) ∧ (∀ i j, i ≤ n → j ≤ n → x i = x j → i = j) ∧
    BergeMatching.Core.IsNeutral M (x 0) ∧
    (∀ i < n, (s(x i, x (i + 1)) ∈ M.edgeSet ↔ i % 2 = 1))

theorem APath.prefix {M : G.Subgraph} {n : ℕ} {x : ℕ → V} (h : APath M n x) {k : ℕ}
    (hk : k ≤ n) : APath M k x :=
  ⟨fun i hi => h.1 i (by omega), fun i j hi hj e => h.2.1 i j (by omega) (by omega) e, h.2.2.1,
    fun i hi => h.2.2.2 i (by omega)⟩

theorem apath_of_walk (M : G.Subgraph) {f v : V} (p : G.Walk f v)
    (hp : IsAltPathFromUnmatched M p) : APath M p.length p.getVert := by
  refine ⟨fun i hi => p.adj_getVert_succ hi, fun i j hi hj h => hp.2.1.getVert_injOn hi hj h,
    ?_, fun i hi => ?_⟩
  · rw [Walk.getVert_zero]; exact hp.1
  · rw [walk_parity M hp.1 p hp.2.2 i hi, Nat.odd_iff]

theorem walk_of_seq {n : ℕ} {x : ℕ → V} (h : ∀ i < n, G.Adj (x i) (x (i + 1))) :
    ∃ p : G.Walk (x 0) (x n), p.length = n ∧ ∀ i ≤ n, p.getVert i = x i := by
  induction n generalizing x with
  | zero =>
    refine ⟨Walk.nil, rfl, fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    rfl
  | succ n ih =>
    obtain ⟨q, hq, hqx⟩ := ih (x := fun i => x (i + 1)) (fun i hi => h (i + 1) (by omega))
    refine ⟨Walk.cons (h 0 (by omega)) q, by rw [Walk.length_cons, hq], fun i hi => ?_⟩
    cases i with
    | zero => rfl
    | succ i => rw [Walk.getVert_cons_succ]; exact hqx i (by omega)

theorem alt_of_getVert (M : G.Subgraph) {a b : V} (p : G.Walk a b) {n : ℕ} {x : ℕ → V}
    (hn : p.length = n) (hx : ∀ i ≤ n, p.getVert i = x i) (hA : APath M n x) :
    IsAltPathFromUnmatched M p := by
  have hpath : p.IsPath := by
    rw [← Walk.IsPath.getVert_injOn_iff]
    intro i hi j hj h
    simp only [Set.mem_setOf_eq] at hi hj
    rw [hx i (by omega), hx j (by omega)] at h
    exact hA.2.1 i j (by omega) (by omega) h
  refine ⟨?_, hpath, hpath.isTrail, ?_⟩
  · have : a = x 0 := by rw [← hx 0 (Nat.zero_le _), Walk.getVert_zero]
    rw [this]; exact hA.2.2.1
  · rw [List.isChain_iff_getElem]
    intro t ht
    have hlen : p.edges.length = n := by rw [Walk.length_edges, hn]
    rw [edges_getElem' p t (by omega), edges_getElem' p (t + 1) ht]
    rw [hx t (by omega), hx (t + 1) (by omega), hx (t + 1 + 1) (by omega)]
    rw [hA.2.2.2 t (by omega), hA.2.2.2 (t + 1) (by omega)]
    omega

theorem first_hit {m : ℕ} {y : ℕ → V} (S : V → Prop) (h : S (y m)) :
    ∃ L, L ≤ m ∧ S (y L) ∧ ∀ s < L, ¬ S (y s) := by
  classical
  have hex : ∃ L, S (y L) := ⟨m, h⟩
  exact ⟨Nat.find hex, Nat.find_min' hex h, Nat.find_spec hex, fun s hs => Nat.find_min hex hs⟩

theorem splice_fwd (M : G.Subgraph) {n m L j : ℕ} {x y : ℕ → V} (hx : APath M n x)
    (hy : APath M m y) (hL : L ≤ m) (hj : j ≤ n) (hyx : y L = x j) (hpar : L % 2 = j % 2)
    (havoid : ∀ s < L, ∀ i, j ≤ i → i ≤ n → y s ≠ x i) :
    ∃ z : ℕ → V, APath M (L + (n - j)) z ∧ z (L + (n - j)) = x n ∧
      (∀ t ≤ L, z t = y t) ∧ (∀ t, L ≤ t → z t = x (j + (t - L))) := by
  classical
  let z : ℕ → V := fun t => if t ≤ L then y t else x (j + (t - L))
  have z1 : ∀ t, t ≤ L → z t = y t := fun t ht => if_pos ht
  have z2 : ∀ t, L ≤ t → z t = x (j + (t - L)) := by
    intro t ht
    by_cases h : t ≤ L
    · have e : t = L := le_antisymm h ht
      rw [e, z1 L le_rfl, hyx, Nat.sub_self, Nat.add_zero]
    · exact if_neg h
  refine ⟨z, ⟨?_, ?_, ?_, ?_⟩, ?_, z1, z2⟩
  · intro t ht
    by_cases h : t < L
    · rw [z1 t h.le, z1 (t + 1) h]; exact hy.1 t (by omega)
    · rw [z2 t (by omega), z2 (t + 1) (by omega)]
      have e : j + (t + 1 - L) = j + (t - L) + 1 := by omega
      rw [e]; exact hx.1 (j + (t - L)) (by omega)
  · intro a b ha hb hab
    rcases le_or_gt a L with h1 | h1 <;> rcases le_or_gt b L with h2 | h2
    · rw [z1 a h1, z1 b h2] at hab; exact hy.2.1 a b (by omega) (by omega) hab
    · rw [z1 a h1, z2 b h2.le] at hab
      rcases lt_or_eq_of_le h1 with h3 | h3
      · exact absurd hab (havoid a h3 (j + (b - L)) (by omega) (by omega))
      · rw [h3, hyx] at hab
        have := hx.2.1 _ _ hj (by omega) hab; omega
    · rw [z2 a h1.le, z1 b h2] at hab
      rcases lt_or_eq_of_le h2 with h3 | h3
      · exact absurd hab.symm (havoid b h3 (j + (a - L)) (by omega) (by omega))
      · rw [h3, hyx] at hab
        have := hx.2.1 _ _ (by omega) hj hab; omega
    · rw [z2 a h1.le, z2 b h2.le] at hab
      have := hx.2.1 _ _ (by omega) (by omega) hab; omega
  · rw [z1 0 (Nat.zero_le _)]; exact hy.2.2.1
  · intro t ht
    by_cases h : t < L
    · rw [z1 t h.le, z1 (t + 1) h]; exact hy.2.2.2 t (by omega)
    · rw [z2 t (by omega), z2 (t + 1) (by omega)]
      have e : j + (t + 1 - L) = j + (t - L) + 1 := by omega
      rw [e, hx.2.2.2 (j + (t - L)) (by omega)]; omega
  · rw [z2 (L + (n - j)) (by omega)]; congr 1; omega

theorem splice_bwd (M : G.Subgraph) {n m L j k : ℕ} {x y : ℕ → V} (hx : APath M n x)
    (hy : APath M m y) (hL : L ≤ m) (hkj : k ≤ j) (hj : j ≤ n) (hyx : y L = x j)
    (hpar : L % 2 ≠ j % 2) (havoid : ∀ s < L, ∀ i, k ≤ i → i ≤ j → y s ≠ x i) :
    ∃ z : ℕ → V, APath M (L + (j - k)) z ∧ z (L + (j - k)) = x k ∧
      (∀ t ≤ L, z t = y t) ∧ (∀ t, L ≤ t → z t = x (j - (t - L))) := by
  classical
  let z : ℕ → V := fun t => if t ≤ L then y t else x (j - (t - L))
  have z1 : ∀ t, t ≤ L → z t = y t := fun t ht => if_pos ht
  have z2 : ∀ t, L ≤ t → z t = x (j - (t - L)) := by
    intro t ht
    by_cases h : t ≤ L
    · have e : t = L := le_antisymm h ht
      rw [e, z1 L le_rfl, hyx, Nat.sub_self, Nat.sub_zero]
    · exact if_neg h
  refine ⟨z, ⟨?_, ?_, ?_, ?_⟩, ?_, z1, z2⟩
  · intro t ht
    by_cases h : t < L
    · rw [z1 t h.le, z1 (t + 1) h]; exact hy.1 t (by omega)
    · rw [z2 t (by omega), z2 (t + 1) (by omega)]
      have e : j - (t - L) = (j - (t + 1 - L)) + 1 := by omega
      rw [e]; exact (hx.1 (j - (t + 1 - L)) (by omega)).symm
  · intro a b ha hb hab
    rcases le_or_gt a L with h1 | h1 <;> rcases le_or_gt b L with h2 | h2
    · rw [z1 a h1, z1 b h2] at hab; exact hy.2.1 a b (by omega) (by omega) hab
    · rw [z1 a h1, z2 b h2.le] at hab
      rcases lt_or_eq_of_le h1 with h3 | h3
      · exact absurd hab (havoid a h3 (j - (b - L)) (by omega) (by omega))
      · rw [h3, hyx] at hab
        have := hx.2.1 _ _ hj (by omega) hab; omega
    · rw [z2 a h1.le, z1 b h2] at hab
      rcases lt_or_eq_of_le h2 with h3 | h3
      · exact absurd hab.symm (havoid b h3 (j - (a - L)) (by omega) (by omega))
      · rw [h3, hyx] at hab
        have := hx.2.1 _ _ (by omega) hj hab; omega
    · rw [z2 a h1.le, z2 b h2.le] at hab
      have := hx.2.1 _ _ (by omega) (by omega) hab; omega
  · rw [z1 0 (Nat.zero_le _)]; exact hy.2.2.1
  · intro t ht
    by_cases h : t < L
    · rw [z1 t h.le, z1 (t + 1) h]; exact hy.2.2.2 t (by omega)
    · rw [z2 t (by omega), z2 (t + 1) (by omega)]
      have e : j - (t - L) = (j - (t + 1 - L)) + 1 := by omega
      rw [e, Sym2.eq_swap, hx.2.2.2 (j - (t + 1 - L)) (by omega)]; omega
  · rw [z2 (L + (j - k)) (by omega)]; congr 1; omega

/-! ### Levels by parity -/

noncomputable def lv (M : G.Subgraph) (v : V) (k : ℕ) : ℕ∞ :=
  if k % 2 = 0 then evenLevel M v else oddLevel M v

theorem lv_congr (M : G.Subgraph) (v : V) {a b : ℕ} (h : a % 2 = b % 2) :
    lv M v a = lv M v b := by
  unfold lv; rw [h]

theorem ten_lv (M : G.Subgraph) (v : V) (k : ℕ) : tenacity M v = lv M v k + lv M v (k + 1) := by
  unfold tenacity lv
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg (by omega), if_pos (by omega), add_comm]

theorem level_le' (M : G.Subgraph) (P : ℕ → Prop) {n : ℕ} {x : ℕ → V} (hA : APath M n x)
    (hP : P n) :
    (⨅ (f : V) (p : G.Walk f (x n)) (_ : IsAltPathFromUnmatched M p) (_ : P p.length),
      (p.length : ℕ∞)) ≤ n := by
  obtain ⟨p, hp, hpx⟩ := walk_of_seq hA.1
  have halt := alt_of_getVert M p hp hpx hA
  have hP' : P p.length := by rw [hp]; exact hP
  refine iInf_le_of_le (x 0) (iInf_le_of_le p (iInf_le_of_le halt (iInf_le_of_le hP' ?_)))
  exact le_of_eq (by rw [hp])

theorem lv_le (M : G.Subgraph) {n k : ℕ} {x : ℕ → V} (hA : APath M n x) (h : n % 2 = k % 2) :
    lv M (x n) k ≤ n := by
  unfold lv
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [if_pos hk]
    exact level_le' M Even hA (Nat.even_iff.mpr (by omega))
  · rw [if_neg (by omega)]
    exact level_le' M Odd hA (Nat.odd_iff.mpr (by omega))

theorem lv_attain (M : G.Subgraph) {v : V} {k : ℕ} (h : lv M v k ≠ ⊤) :
    ∃ (m : ℕ) (y : ℕ → V), APath M m y ∧ y m = v ∧ m % 2 = k % 2 ∧ lv M v k = m := by
  unfold lv at h ⊢
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [if_pos hk] at h
    rw [if_pos hk]
    obtain ⟨f, p, hp, hev, hlen⟩ := attain_even M h
    exact ⟨p.length, p.getVert, apath_of_walk M p hp, p.getVert_length,
      by rw [hk]; exact Nat.even_iff.mp hev, hlen.symm⟩
  · rw [if_neg (by omega)] at h
    rw [if_neg (by omega)]
    obtain ⟨f, p, hp, hod, hlen⟩ := attain_odd M h
    exact ⟨p.length, p.getVert, apath_of_walk M p hp, p.getVert_length,
      by rw [hk]; exact Nat.odd_iff.mp hod, hlen.symm⟩

theorem minLevel_eq (M : G.Subgraph) (v : V) (k : ℕ) (h1 : lv M v k = k)
    (h2 : (k : ℕ∞) ≤ lv M v (k + 1)) : minLevel M v = k := by
  unfold minLevel
  unfold lv at h1 h2
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [if_pos hk] at h1
    rw [if_neg (by omega)] at h2
    rw [h1]; exact min_eq_left h2
  · rw [if_neg (by omega)] at h1
    rw [if_pos (by omega)] at h2
    rw [h1]; exact min_eq_right h2

/-! ### Limited BFS honesty (sequence form) -/

theorem caseB (M : G.Subgraph) {n : ℕ} {x : ℕ → V} (hx : APath M n x)
    (hlev : lv M (x n) n = n) {k : ℕ} (hk : k ≤ n) {r : ℕ} (hr : lv M (x n) (n + 1) = r) :
    lv M (x k) (k + 1) ≤ ((r + (n - k) : ℕ) : ℕ∞) ∨ k ≤ r := by
  obtain ⟨m, w, hw, hwv, _, hlen⟩ :=
    lv_attain M (k := n + 1) (v := x n) (by rw [hr]; exact ENat.natCast_ne_top r)
  rw [hr] at hlen
  have hmr : m = r := by exact_mod_cast hlen.symm
  obtain ⟨L, hLm, ⟨i, hki, hin, hwi⟩, hmin⟩ :=
    first_hit (y := w) (fun a => ∃ i, k ≤ i ∧ i ≤ n ∧ a = x i) ⟨n, hk, le_rfl, hwv⟩
  have havoid : ∀ s < L, ∀ i', k ≤ i' → i' ≤ n → w s ≠ x i' :=
    fun s hs i' h1 h2 he => hmin s hs ⟨i', h1, h2, he⟩
  by_cases hp : L % 2 = i % 2
  · right
    obtain ⟨z, hz, hzn, -, -⟩ := splice_fwd M hx hw hLm hin hwi hp
      (fun s hs i' h1 h2 => havoid s hs i' (by omega) h2)
    have h1 := lv_le M hz (k := n) (by omega)
    rw [hzn, hlev] at h1
    have : n ≤ L + (n - i) := by exact_mod_cast h1
    omega
  · left
    obtain ⟨z, hz, hzk, -, -⟩ := splice_bwd M hx hw hLm hki hin hwi hp
      (fun s hs i' h1 h2 => havoid s hs i' h1 (by omega))
    have h1 := lv_le M hz (k := k + 1) (by omega)
    rw [hzk] at h1
    refine h1.trans ?_
    exact_mod_cast (by omega : L + (i - k) ≤ r + (n - k))

theorem dishonest (M : G.Subgraph) {n : ℕ} {x : ℕ → V} (hx : APath M n x)
    (hlev : lv M (x n) n = n) {k : ℕ} (hk : k ≤ n) {m : ℕ} (hm : lv M (x k) k = m)
    (hmk : m < k) :
    ∃ c : ℕ, lv M (x k) (k + 1) ≤ c ∧ c + k < m + n ∧ c < n := by
  obtain ⟨m', y, hy, hyu, hpar, hlen⟩ :=
    lv_attain M (k := k) (v := x k) (by rw [hm]; exact ENat.natCast_ne_top m)
  rw [hm] at hlen
  have hmm : m' = m := by exact_mod_cast hlen.symm
  have hex : ∃ s, s ≤ m' ∧ ∃ i, k < i ∧ i ≤ n ∧ y s = x i := by
    by_contra hne
    push_neg at hne
    obtain ⟨z, hz, hzn, -, -⟩ := splice_fwd M hx hy (L := m') le_rfl hk hyu (by omega) (by
      intro s hs i h1 h2 he
      rcases lt_or_eq_of_le h1 with h3 | h3
      · exact hne s hs.le i h3 h2 he
      · rw [← h3, ← hyu] at he
        have := hy.2.1 s m' (by omega) le_rfl he
        omega)
    have h1 := lv_le M hz (k := n) (by omega)
    rw [hzn, hlev] at h1
    have : n ≤ m' + (n - k) := by exact_mod_cast h1
    omega
  obtain ⟨s0, hs0, hS0⟩ := hex
  obtain ⟨L, hL, ⟨j, hkj, hjn, hyj⟩, hmin⟩ :=
    first_hit (y := y) (m := s0) (fun a => ∃ i, k < i ∧ i ≤ n ∧ a = x i) hS0
  have hLm : L < m' := by
    rcases lt_or_eq_of_le (hL.trans hs0) with h | h
    · exact h
    · rw [h, hyu] at hyj
      have := hx.2.1 k j hk hjn hyj
      omega
  have havoid : ∀ s < L, ∀ i, k ≤ i → i ≤ n → y s ≠ x i := by
    intro s hs i h1 h2 he
    rcases lt_or_eq_of_le h1 with h3 | h3
    · exact hmin s hs ⟨i, h3, h2, he⟩
    · rw [← h3, ← hyu] at he
      have := hy.2.1 s m' (by omega) le_rfl he
      omega
  by_cases hp : L % 2 = j % 2
  · exfalso
    obtain ⟨z, hz, hzn, -, -⟩ := splice_fwd M hx hy (by omega) hjn hyj hp
      (fun s hs i h1 h2 => havoid s hs i (by omega) h2)
    have h1 := lv_le M hz (k := n) (by omega)
    rw [hzn, hlev] at h1
    have : n ≤ L + (n - j) := by exact_mod_cast h1
    omega
  · obtain ⟨z, hz, hzk, -, -⟩ := splice_bwd M hx hy (by omega) hkj.le hjn hyj hp
      (fun s hs i h1 h2 => havoid s hs i h1 (by omega))
    have h1 := lv_le M hz (k := k + 1) (by omega)
    rw [hzk] at h1
    exact ⟨L + (j - k), h1, by omega, by omega⟩

theorem thm2_seq (M : G.Subgraph) {n : ℕ} {x : ℕ → V} (hx : APath M n x)
    (hlev : lv M (x n) n = n) {k : ℕ} (hk : k ≤ n)
    (hten : tenacity M (x n) ≤ tenacity M (x k)) :
    lv M (x k) k = k ∧ (tenacity M (x n) < tenacity M (x k) → (k : ℕ∞) ≤ lv M (x k) (k + 1)) := by
  have hle : lv M (x k) k ≤ k := lv_le M (hx.prefix hk) rfl
  have hvn := ten_lv M (x n) n
  rw [hlev] at hvn
  have hpart1 : lv M (x k) k = k := by
    by_contra hne
    have hlt : lv M (x k) k < k := lt_of_le_of_ne hle hne
    obtain ⟨m, hm⟩ : ∃ m : ℕ, lv M (x k) k = m :=
      ⟨(lv M (x k) k).toNat, (ENat.natCast_toNat (ne_top_of_lt hlt)).symm⟩
    have hmk : m < k := by rw [hm] at hlt; exact_mod_cast hlt
    obtain ⟨c, hc, hc1, hc2⟩ := dishonest M hx hlev hk hm hmk
    have key : tenacity M (x k) < tenacity M (x n) := by
      rw [hvn, ten_lv M (x k) k, hm]
      rcases eq_or_ne (lv M (x n) (n + 1)) ⊤ with hA | hA
      · rw [hA, add_top]
        refine lt_of_le_of_lt (add_le_add le_rfl hc) ?_
        rw [← Nat.cast_add]; exact ENat.natCast_lt_top _
      · obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hA
        rw [← hr]
        rcases le_or_gt n r with hnr | hnr
        · calc (m : ℕ∞) + lv M (x k) (k + 1) ≤ (m : ℕ∞) + (c : ℕ∞) := add_le_add le_rfl hc
            _ < (n : ℕ∞) + (r : ℕ∞) := by exact_mod_cast (by omega : m + c < n + r)
        · rcases caseB M hx hlev hk hr.symm with h | h
          · calc (m : ℕ∞) + lv M (x k) (k + 1) ≤ (m : ℕ∞) + ((r + (n - k) : ℕ) : ℕ∞) :=
                  add_le_add le_rfl h
              _ < (n : ℕ∞) + (r : ℕ∞) := by
                  exact_mod_cast (by omega : m + (r + (n - k)) < n + r)
          · calc (m : ℕ∞) + lv M (x k) (k + 1) ≤ (m : ℕ∞) + (c : ℕ∞) := add_le_add le_rfl hc
              _ < (n : ℕ∞) + (r : ℕ∞) := by exact_mod_cast (by omega : m + c < n + r)
    exact absurd hten (not_le.mpr key)
  refine ⟨hpart1, fun hlt => ?_⟩
  by_contra hne
  push_neg at hne
  obtain ⟨c, hc⟩ : ∃ c : ℕ, lv M (x k) (k + 1) = c :=
    ⟨_, (ENat.natCast_toNat (ne_top_of_lt hne)).symm⟩
  rw [hc] at hne
  have hck : c < k := by exact_mod_cast hne
  have hku : tenacity M (x k) = ((k + c : ℕ) : ℕ∞) := by
    rw [ten_lv M (x k) k, hpart1, hc, Nat.cast_add]
  rw [hku, hvn] at hlt
  rcases eq_or_ne (lv M (x n) (n + 1)) ⊤ with hA | hA
  · rw [hA, add_top] at hlt; exact absurd hlt (not_lt.mpr le_top)
  · obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hA
    rw [← hr] at hlt
    have hlt' : n + r < k + c := by exact_mod_cast hlt
    rcases le_or_gt n r with hnr | hnr
    · omega
    · rcases caseB M hx hlev hk hr.symm with h | h
      · rw [hc] at h
        have : c ≤ r + (n - k) := by exact_mod_cast h
        omega
      · omega

/-- From a walk which is an even/odd level path. -/
theorem lev_of_walk (M : G.Subgraph) {f v : V} (p : G.Walk f v)
    (hp : IsEvenLevelPath M p ∨ IsOddLevelPath M p) :
    APath M p.length p.getVert ∧ lv M (p.getVert p.length) p.length = p.length := by
  have hA : IsAltPathFromUnmatched M p := by rcases hp with h | h <;> exact h.1
  refine ⟨apath_of_walk M p hA, ?_⟩
  rw [p.getVert_length]
  unfold lv
  rcases hp with h | h
  · rw [if_pos (Nat.even_iff.mp h.2.1)]; exact h.2.2.symm
  · rw [if_neg (by have := Nat.odd_iff.mp h.2.1; omega)]; exact h.2.2.symm

end Aux_MVB

namespace Aux_MVB

open MVBlossoms SimpleGraph

variable {V : Type} {G : SimpleGraph V}

theorem lv_even (M : G.Subgraph) (v : V) {k : ℕ} (hk : k % 2 = 0) : lv M v k = evenLevel M v := by
  unfold lv; rw [if_pos hk]

theorem lv_odd (M : G.Subgraph) (v : V) {k : ℕ} (hk : k % 2 = 1) : lv M v k = oddLevel M v := by
  unfold lv; rw [if_neg (by omega)]

theorem minLevel_le_lv (M : G.Subgraph) (v : V) (k : ℕ) : minLevel M v ≤ lv M v k := by
  unfold minLevel lv
  split_ifs
  · exact min_le_left _ _
  · exact min_le_right _ _

theorem getVert_concat_le {u v w : V} (q : G.Walk u v) (h : G.Adj v w) (i : ℕ)
    (hi : i ≤ q.length) : (q.concat h).getVert i = q.getVert i := by
  rw [Walk.concat_eq_append, Walk.getVert_append', if_pos hi]

theorem getVert_concat_end {u v w : V} (q : G.Walk u v) (h : G.Adj v w) :
    (q.concat h).getVert (q.length + 1) = w := by
  have := (q.concat h).getVert_length
  rwa [Walk.length_concat] at this

theorem levpath_of (M : G.Subgraph) {f v : V} (p : G.Walk f v) (hA : IsAltPathFromUnmatched M p)
    (h : lv M v p.length = p.length) : IsEvenLevelPath M p ∨ IsOddLevelPath M p := by
  unfold lv at h
  rcases Nat.mod_two_eq_zero_or_one p.length with hk | hk
  · rw [if_pos hk] at h; exact Or.inl ⟨hA, Nat.even_iff.mpr hk, h.symm⟩
  · rw [if_neg (by omega)] at h; exact Or.inr ⟨hA, Nat.odd_iff.mpr hk, h.symm⟩

theorem pred_of_seq (M : G.Subgraph) {n : ℕ} {x : ℕ → V} (hA : APath M (n + 1) x)
    (hmin : minLevel M (x (n + 1)) = ((n + 1 : ℕ) : ℕ∞)) : IsPred M (x n) (x (n + 1)) := by
  obtain ⟨q, hq, hqx⟩ := walk_of_seq (hA.prefix (Nat.le_succ n)).1
  have hadj : G.Adj (x n) (x (n + 1)) := hA.1 n (by omega)
  have hgv : ∀ i ≤ n + 1, (q.concat hadj).getVert i = x i := by
    intro i hi
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · rw [getVert_concat_le q hadj i (by omega), hqx i (by omega)]
    · obtain rfl : i = n + 1 := by omega
      have := getVert_concat_end q hadj
      rw [hq] at this
      exact this
  have hlen : (q.concat hadj).length = n + 1 := by rw [Walk.length_concat, hq]
  have halt := alt_of_getVert M (q.concat hadj) hlen hgv hA
  have hlv : lv M (x (n + 1)) (n + 1) = ((n + 1 : ℕ) : ℕ∞) :=
    le_antisymm (lv_le M hA rfl) (by rw [← hmin]; exact minLevel_le_lv M (x (n + 1)) (n + 1))
  refine ⟨x 0, q, hadj, levpath_of M _ halt (by rw [hlen]; exact hlv), ?_⟩
  rw [hlen, hmin]

theorem seq_of_pred (M : G.Subgraph) {u v : V} (h : IsPred M u v) :
    ∃ (n : ℕ) (x : ℕ → V), APath M (n + 1) x ∧ x n = u ∧ x (n + 1) = v ∧
      minLevel M v = ((n + 1 : ℕ) : ℕ∞) := by
  obtain ⟨f, q, hadj, hor, hlen⟩ := h
  have hA : IsAltPathFromUnmatched M (q.concat hadj) := by rcases hor with h | h <;> exact h.1
  have hx := apath_of_walk M _ hA
  rw [Walk.length_concat] at hx
  refine ⟨q.length, (q.concat hadj).getVert, hx, ?_, ?_, ?_⟩
  · rw [getVert_concat_le q hadj _ le_rfl, q.getVert_length]
  · exact getVert_concat_end q hadj
  · rw [← hlen, Walk.length_concat]

theorem extend_seq (M : G.Subgraph) {n : ℕ} {x : ℕ → V} (hA : APath M n x) {w : V}
    (hadj : G.Adj (x n) w) (hpar : s(x n, w) ∈ M.edgeSet ↔ n % 2 = 1)
    (hnot : ∀ i ≤ n, x i ≠ w) :
    ∃ z : ℕ → V, APath M (n + 1) z ∧ z (n + 1) = w ∧ ∀ i ≤ n, z i = x i := by
  classical
  let z : ℕ → V := fun t => if t ≤ n then x t else w
  have z1 : ∀ t, t ≤ n → z t = x t := fun t ht => if_pos ht
  have z2 : z (n + 1) = w := if_neg (by omega)
  refine ⟨z, ⟨?_, ?_, ?_, ?_⟩, z2, z1⟩
  · intro t ht
    rcases Nat.lt_or_ge t n with h | h
    · rw [z1 t h.le, z1 (t + 1) h]; exact hA.1 t h
    · obtain rfl : t = n := by omega
      rw [z1 t le_rfl, z2]; exact hadj
  · intro a b ha hb hab
    rcases Nat.lt_or_ge a (n + 1) with h1 | h1 <;> rcases Nat.lt_or_ge b (n + 1) with h2 | h2
    · rw [z1 a (by omega), z1 b (by omega)] at hab
      exact hA.2.1 a b (by omega) (by omega) hab
    · obtain rfl : b = n + 1 := by omega
      rw [z1 a (by omega), z2] at hab
      exact absurd hab (hnot a (by omega))
    · obtain rfl : a = n + 1 := by omega
      rw [z1 b (by omega), z2] at hab
      exact absurd hab.symm (hnot b (by omega))
    · omega
  · rw [z1 0 (Nat.zero_le _)]; exact hA.2.2.1
  · intro t ht
    rcases Nat.lt_or_ge t n with h | h
    · rw [z1 t h.le, z1 (t + 1) h]; exact hA.2.2.2 t h
    · obtain rfl : t = n := by omega
      rw [z1 t le_rfl, z2]; exact hpar

theorem isBridge_symm (M : G.Subgraph) {u v : V} (h : IsBridge M u v) : IsBridge M v u :=
  ⟨h.1.symm, fun hp => h.2 (hp.elim Or.inr Or.inl)⟩

end Aux_MVB

namespace Aux_MVB

open MVBlossoms SimpleGraph

variable {V : Type} {G : SimpleGraph V}

/-- If `v` (a neighbour of `u` along an unmatched edge with `v` not a predecessor of `u`) lies on an
even level(u) path, then `oddLevel v < evenLevel u`. -/
theorem on_path_odd_lt (M : G.Subgraph) {n : ℕ} {x : ℕ → V} (hx : APath M n x)
    (hlev : lv M (x n) n = n) (hn : n % 2 = 0) {v : V} (hadj : G.Adj (x n) v)
    (hun : s(x n, v) ∉ M.edgeSet) (hnp : ¬ IsPred M v (x n)) {i : ℕ} (hi : i ≤ n) (hxi : x i = v) :
    oddLevel M v < n := by
  have hin : i < n := by
    rcases lt_or_eq_of_le hi with h | h
    · exact h
    · rw [h] at hxi; exact absurd hxi hadj.ne
  rcases Nat.mod_two_eq_zero_or_one i with hie | hio
  · -- even position: build an odd path to `u` through `v`
    have hpre := hx.prefix hi
    have hadj' : G.Adj (x i) (x n) := by rw [hxi]; exact hadj.symm
    have hpar : s(x i, x n) ∈ M.edgeSet ↔ i % 2 = 1 := by
      rw [hxi, Sym2.eq_swap]; constructor
      · intro h; exact absurd h hun
      · intro h; omega
    have hnot : ∀ t ≤ i, x t ≠ x n := by
      intro t ht he
      have := hx.2.1 t n (by omega) le_rfl he
      omega
    obtain ⟨z, hz, hzn, hzx⟩ := extend_seq M hpre hadj' hpar hnot
    have hodu : lv M (x n) (i + 1) ≤ ((i + 1 : ℕ) : ℕ∞) := by
      have := lv_le M hz (k := i + 1) rfl
      rwa [hzn] at this
    -- oddLevel u < i + 1, otherwise v is a predecessor of u
    have hlt : lv M (x n) (i + 1) < ((i + 1 : ℕ) : ℕ∞) := by
      refine lt_of_le_of_ne hodu (fun heq => hnp ?_)
      have hmin : minLevel M (z (i + 1)) = ((i + 1 : ℕ) : ℕ∞) := by
        rw [hzn]
        unfold minLevel
        rw [← lv_even M (x n) hn, hlev, ← lv_odd M (x n) (k := i + 1) (by omega), heq]
        exact min_eq_right (by exact_mod_cast (by omega : i + 1 ≤ n))
      have := pred_of_seq M hz hmin
      rwa [hzx i le_rfl, hxi, hzn] at this
    obtain ⟨m, y, hy, hyu, hpar', hlen⟩ := lv_attain M (k := i + 1) (v := x n) (ne_top_of_lt hlt)
    rw [hlen] at hlt
    have hmi : m < i + 1 := by exact_mod_cast hlt
    obtain ⟨L, hLm, ⟨j, hij, hjn, hyj⟩, hmin⟩ :=
      first_hit (y := y) (fun a => ∃ j, i ≤ j ∧ j ≤ n ∧ a = x j) ⟨n, hi, le_rfl, hyu⟩
    have havoid : ∀ s < L, ∀ j', i ≤ j' → j' ≤ n → y s ≠ x j' :=
      fun s hs j' h1 h2 he => hmin s hs ⟨j', h1, h2, he⟩
    by_cases hp : L % 2 = j % 2
    · exfalso
      obtain ⟨z', hz', hzn', -, -⟩ := splice_fwd M hx hy hLm hjn hyj hp
        (fun s hs j' h1 h2 => havoid s hs j' (by omega) h2)
      have h1 := lv_le M hz' (k := n) (by omega)
      rw [hzn', hlev] at h1
      have : n ≤ L + (n - j) := by exact_mod_cast h1
      omega
    · obtain ⟨z', hz', hzi, -, -⟩ := splice_bwd M hx hy hLm hij hjn hyj hp
        (fun s hs j' h1 h2 => havoid s hs j' h1 (by omega))
      have h1 := lv_le M hz' (k := 1) (by omega)
      rw [hzi, hxi, lv_odd M v (k := 1) rfl] at h1
      exact lt_of_le_of_lt h1 (by exact_mod_cast (by omega : L + (j - i) < n))
  · have h1 := lv_le M (hx.prefix hi) (k := 1) (by omega)
    rw [hxi, lv_odd M v (k := 1) rfl] at h1
    exact lt_of_le_of_lt h1 (by exact_mod_cast hin)

end Aux_MVB

open MVBlossoms in
theorem solution {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M)
    (u v : V) (hadj : G.Adj u v) (hun : s(u, v) ∉ M.edgeSet) (hbr : IsBridge M u v) :
    tenacity M v ≤ edgeTenacity M u v ∧
      (tenacity M v = edgeTenacity M u v → edgeTenacity M u v ≠ ⊤ → IsOuter M v) := by
  have hET : edgeTenacity M u v = evenLevel M u + evenLevel M v + 1 := by
    unfold edgeTenacity
    rw [if_neg hun]
  have hnp : ¬ IsPred M v u := fun h => hbr.2 (Or.inr h)
  have hnp' : ¬ IsPred M u v := fun h => hbr.2 (Or.inl h)
  rcases eq_or_ne (evenLevel M u) ⊤ with htop | hfin
  · refine ⟨by rw [hET, htop, top_add, top_add]; exact le_top, fun _ h => ?_⟩
    exact absurd (show edgeTenacity M u v = ⊤ by rw [hET, htop, top_add, top_add]) h
  have he0 : Aux_MVB.lv M u 0 ≠ ⊤ := by rw [Aux_MVB.lv_even M u rfl]; exact hfin
  obtain ⟨n, x, hx, hxu, hpar, hlen⟩ := Aux_MVB.lv_attain M he0
  rw [Aux_MVB.lv_even M u rfl] at hlen
  have hn0 : n % 2 = 0 := by omega
  have hlev : Aux_MVB.lv M (x n) n = n := by rw [hxu, Aux_MVB.lv_even M u hn0, hlen]
  have hadj' : G.Adj (x n) v := by rw [hxu]; exact hadj
  have hun' : s(x n, v) ∉ M.edgeSet := by rw [hxu]; exact hun
  have hnp'' : ¬ IsPred M v (x n) := by rw [hxu]; exact hnp
  have hparv : s(x n, v) ∈ M.edgeSet ↔ n % 2 = 1 := ⟨fun h => absurd h hun', fun h => by omega⟩
  -- the key dichotomy
  have hcase : (∃ i ≤ n, x i = v) ∨ ∀ i ≤ n, x i ≠ v := by
    by_cases h : ∃ i ≤ n, x i = v
    · exact Or.inl h
    · push_neg at h; exact Or.inr h
  have hod : oddLevel M v ≤ ((n + 1 : ℕ) : ℕ∞) := by
    rcases hcase with ⟨i, hi, hxi⟩ | hnot
    · exact (Aux_MVB.on_path_odd_lt M hx hlev hn0 hadj' hun' hnp'' hi hxi).le.trans
        (by exact_mod_cast (Nat.le_succ n))
    · obtain ⟨z, hz, hzv, -⟩ := Aux_MVB.extend_seq M hx hadj' hparv hnot
      have := Aux_MVB.lv_le M hz (k := 1) (by omega)
      rwa [hzv, Aux_MVB.lv_odd M v (k := 1) rfl] at this
  have hET' : edgeTenacity M u v = (n : ℕ∞) + evenLevel M v + 1 := by rw [hET, hlen]
  refine ⟨?_, fun heq hfinET => ?_⟩
  · rw [hET']
    unfold tenacity
    calc evenLevel M v + oddLevel M v ≤ evenLevel M v + ((n + 1 : ℕ) : ℕ∞) :=
          add_le_add le_rfl hod
      _ = (n : ℕ∞) + evenLevel M v + 1 := by push_cast; ring
  · -- finite case
    have hevf : evenLevel M v ≠ ⊤ := by
      intro h; apply hfinET; rw [hET', h, add_top, top_add]
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hevf
    have hodf : oddLevel M v ≠ ⊤ := by
      intro h; apply hfinET; rw [← heq]; unfold tenacity; rw [h, add_top]
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hodf
    have hb' : b = n + 1 := by
      have h1 := heq
      unfold tenacity at h1
      rw [hET', ← ha, ← hb] at h1
      have : a + b = n + a + 1 := by exact_mod_cast h1
      omega
    have hnot : ∀ i ≤ n, x i ≠ v := by
      intro i hi hxi
      have := Aux_MVB.on_path_odd_lt M hx hlev hn0 hadj' hun' hnp'' hi hxi
      rw [← hb, hb'] at this
      have : n + 1 < n := by exact_mod_cast this
      omega
    refine ⟨?_, ?_⟩
    · unfold minLevel
      exact ne_top_of_le_ne_top hodf (min_le_right _ _)
    · by_contra hle
      push_neg at hle
      apply hnp'
      obtain ⟨z, hz, hzv, hzx⟩ := Aux_MVB.extend_seq M hx hadj' hparv hnot
      have hmin : minLevel M (z (n + 1)) = ((n + 1 : ℕ) : ℕ∞) := by
        rw [hzv]; unfold minLevel
        rw [min_eq_right hle, ← hb, hb']
      have := Aux_MVB.pred_of_seq M hz hmin
      rwa [hzx n le_rfl, hxu, hzv] at this
