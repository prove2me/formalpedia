-- Prove2me | solution 1 for MVBlossoms.corollary_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:55:47.915917+00:00
-- url     : https://prove2.me/submissions/e83ba746-6b71-4f6e-8407-902dc73d9d1a

import Mathlib
import Definitions.Def_MVBlossoms_edgeTenacity
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_IsBase
import Definitions.Def_MVBlossoms_blossom

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

theorem tm_le (M : G.Subgraph) (v : V) : tm M ≤ tenacity M v := by
  unfold tm; exact iInf_le _ v

theorem lv_even (M : G.Subgraph) (v : V) {k : ℕ} (hk : k % 2 = 0) : lv M v k = evenLevel M v := by
  unfold lv; rw [if_pos hk]


theorem lv_odd (M : G.Subgraph) (v : V) {k : ℕ} (hk : k % 2 = 1) : lv M v k = oddLevel M v := by
  unfold lv; rw [if_neg (by omega)]


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


end Aux_MVB


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

end Aux_MV1

namespace Aux_MVB

open MVBlossoms SimpleGraph

variable {V : Type} {G : SimpleGraph V}

noncomputable def mlv (M : G.Subgraph) (v : V) : ℕ∞ := min (evenLevel M v) (oddLevel M v)

theorem mlv_le_lv (M : G.Subgraph) (v : V) (k : ℕ) : mlv M v ≤ lv M v k := by
  unfold mlv lv
  split_ifs
  · exact min_le_left _ _
  · exact min_le_right _ _

theorem mlv_cases (M : G.Subgraph) (v : V) (k : ℕ) :
    mlv M v = lv M v k ∨ mlv M v = lv M v (k + 1) := by
  unfold mlv
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [lv_even M v hk, lv_odd M v (k := k + 1) (by omega)]
    rcases le_total (evenLevel M v) (oddLevel M v) with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (min_eq_right h)
  · rw [lv_odd M v hk, lv_even M v (k := k + 1) (by omega)]
    rcases le_total (evenLevel M v) (oddLevel M v) with h | h
    · exact Or.inr (min_eq_left h)
    · exact Or.inl (min_eq_right h)

/-- `b` is the highest vertex of tenacity `> t_m` on the sequence `x[0..n]`. -/
def IsTop (M : G.Subgraph) (x : ℕ → V) (n : ℕ) (b : V) : Prop :=
  ∃ β ≤ n, x β = b ∧ tm M < tenacity M b ∧ ∀ k, β < k → k ≤ n → tenacity M (x k) ≤ tm M

theorem top_unique (M : G.Subgraph) {x : ℕ → V} {n : ℕ} {b b' : V} (h : IsTop M x n b)
    (h' : IsTop M x n b') : b = b' := by
  obtain ⟨β, hβ, hxb, hb, hk⟩ := h
  obtain ⟨β', hβ', hxb', hb', hk'⟩ := h'
  rcases lt_trichotomy β β' with hl | he | hl
  · have := hk β' hl hβ'
    rw [hxb'] at this
    exact absurd this (not_le.mpr hb')
  · rw [← hxb, ← hxb', he]
  · have := hk' β hl hβ
    rw [hxb] at this
    exact absurd this (not_le.mpr hb)

theorem top_prefix (M : G.Subgraph) {x : ℕ → V} {n a : ℕ} {b : V} (ha : a ≤ n)
    (hr : ∀ k, a < k → k ≤ n → tenacity M (x k) ≤ tm M) (h : IsTop M x n b) : IsTop M x a b := by
  obtain ⟨β, hβ, hxb, hb, hk⟩ := h
  have hβa : β ≤ a := by
    by_contra hc
    push_neg at hc
    have := hr β hc hβ
    rw [hxb] at this
    exact absurd this (not_le.mpr hb)
  exact ⟨β, hβa, hxb, hb, fun k h1 h2 => hk k h1 (by omega)⟩

theorem top_extend (M : G.Subgraph) {x : ℕ → V} {n a : ℕ} {b : V} (ha : a ≤ n)
    (hr : ∀ k, a < k → k ≤ n → tenacity M (x k) ≤ tm M) (h : IsTop M x a b) : IsTop M x n b := by
  obtain ⟨β, hβ, hxb, hb, hk⟩ := h
  refine ⟨β, by omega, hxb, hb, fun k h1 h2 => ?_⟩
  rcases le_or_gt k a with h3 | h3
  · exact hk k h1 h3
  · exact hr k h3 h2

theorem top_congr (M : G.Subgraph) {x x' : ℕ → V} {n : ℕ} {b : V} (he : ∀ i ≤ n, x i = x' i)
    (h : IsTop M x n b) : IsTop M x' n b := by
  obtain ⟨β, hβ, hxb, hb, hk⟩ := h
  refine ⟨β, hβ, by rw [← he β hβ]; exact hxb, hb, fun k h1 h2 => ?_⟩
  rw [← he k h2]; exact hk k h1 h2

theorem exists_greatest (P : ℕ → Prop) {N a0 : ℕ} (h0 : a0 ≤ N) (hP : P a0) :
    ∃ a, a ≤ N ∧ P a ∧ ∀ k, a < k → k ≤ N → ¬ P k := by
  classical
  exact ⟨Nat.findGreatest P N, Nat.findGreatest_le N, Nat.findGreatest_spec h0 hP,
    fun k hk hkN => Nat.findGreatest_is_greatest hk hkN⟩

theorem top_exists (M : G.Subgraph) {x : ℕ → V} (n : ℕ) (h0 : tm M < tenacity M (x 0)) :
    ∃ b, IsTop M x n b := by
  obtain ⟨a, ha, hPa, hmax⟩ :=
    exists_greatest (fun a => tm M < tenacity M (x a)) (Nat.zero_le n) h0
  exact ⟨x a, a, ha, rfl, hPa, fun k h1 h2 => not_lt.mp (hmax k h1 h2)⟩

theorem lm_le (M : G.Subgraph) {N : ℕ} {z : ℕ → V} (hz : APath M N z) (hN : 0 < N)
    (hneu : BergeMatching.Core.IsNeutral M (z N)) : lm M ≤ N := by
  obtain ⟨p, hp, hpx⟩ := walk_of_seq hz.1
  have halt := alt_of_getVert M p hp hpx hz
  have hpos : 0 < p.length := by omega
  unfold lm
  refine iInf_le_of_le (z 0) (iInf_le_of_le (z N) (iInf_le_of_le p (iInf_le_of_le halt
    (iInf_le_of_le hneu (iInf_le_of_le hpos ?_)))))
  exact le_of_eq (by rw [hp])

theorem tm_lt_ten_neutral (M : G.Subgraph) (hstd : tm M < lm M) {f : V}
    (hf : BergeMatching.Core.IsNeutral M f) : tm M < tenacity M f := by
  have hodd : lm M ≤ oddLevel M f := by
    rcases eq_or_ne (oddLevel M f) ⊤ with h | h
    · rw [h]; exact le_top
    · have h1 : lv M f 1 ≠ ⊤ := by rw [lv_odd M f rfl]; exact h
      obtain ⟨m, y, hy, hyf, hpar, hlen⟩ := lv_attain M h1
      rw [lv_odd M f rfl] at hlen
      rw [hlen]
      refine lm_le M hy (by omega) ?_
      rw [hyf]; exact hf
  calc tm M < lm M := hstd
    _ ≤ oddLevel M f := hodd
    _ ≤ tenacity M f := by unfold tenacity; exact le_add_self

theorem um_fin (M : G.Subgraph) (hstd : tm M < lm M) {v : V} (hv : tenacity M v = tm M) (k : ℕ) :
    lv M v k ≠ ⊤ := by
  intro h
  have e := ten_lv M v k
  rw [h, top_add, hv] at e
  exact (ne_top_of_lt hstd) e

theorem base_unique (M : G.Subgraph) (hstd : tm M < lm M) :
    ∀ d : ℕ, ∀ v : V, tenacity M v = tm M → mlv M v = d →
    ∀ (n : ℕ) (x : ℕ → V) (n' : ℕ) (x' : ℕ → V) (b b' : V),
      APath M n x → x n = v → lv M v n = n → APath M n' x' → x' n' = v → lv M v n' = n' →
      IsTop M x n b → IsTop M x' n' b' → b = b' := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro v hv hd
  have opp : ∀ (n : ℕ) (x : ℕ → V) (m : ℕ) (y : ℕ → V) (b b' : V),
      APath M n x → x n = v → lv M v n = n → APath M m y → y m = v → lv M v m = m →
      n % 2 ≠ m % 2 → IsTop M x n b → IsTop M y m b' → b = b' := by
    intro n x m y b b' hx hxv hxl hy hyv hyl hnm htx hty
    have hxl' : lv M (x n) n = n := by rw [hxv]; exact hxl
    have hyl' : lv M (y m) m = m := by rw [hyv]; exact hyl
    have htm : tm M = ((n + m : ℕ) : ℕ∞) := by
      rw [← hv, ten_lv M v n, hxl, lv_congr M v (show (n + 1) % 2 = m % 2 by omega), hyl,
        Nat.cast_add]
    have hge : ∀ w : V, ((n + m : ℕ) : ℕ∞) ≤ tenacity M w := by
      intro w; rw [← htm]; exact tm_le M w
    have honx : ∀ k ≤ n, lv M (x k) k = k := fun k hk =>
      (thm2_seq M hx hxl' hk (by rw [hxv, hv]; exact tm_le M _)).1
    have hony : ∀ k ≤ m, lv M (y k) k = k := fun k hk =>
      (thm2_seq M hy hyl' hk (by rw [hyv, hv]; exact tm_le M _)).1
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exfalso
        have h1 := tm_lt_ten_neutral M hstd hx.2.2.1
        rw [h0] at hxv
        rw [hxv, hv] at h1
        exact lt_irrefl _ h1
      · exact h0
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso
        have h1 := tm_lt_ten_neutral M hstd hy.2.2.1
        rw [h0] at hyv
        rw [hyv, hv] at h1
        exact lt_irrefl _ h1
      · exact h0
    have hex : ∃ a, a ≤ n - 1 ∧ ∃ c ≤ m, x a = y c := by
      by_contra hne
      push_neg at hne
      obtain ⟨z, hz, hz0, -, -⟩ := splice_bwd M hy hx (L := n) (j := m) (k := 0) le_rfl
        (Nat.zero_le m) le_rfl (by rw [hxv, hyv]) hnm
        (fun s hs i _ hi => hne s (by omega) i hi)
      have h1 := lm_le M hz (by omega) (by rw [hz0]; exact hy.2.2.1)
      rw [Nat.sub_zero] at h1
      have : lm M ≤ tm M := by rw [htm]; exact h1
      exact absurd hstd (not_lt.mpr this)
    obtain ⟨a0, ha0, hP0⟩ := hex
    obtain ⟨a, ha, ⟨c, hc, hac⟩, hmax⟩ :=
      exists_greatest (fun a => ∃ c ≤ m, x a = y c) ha0 hP0
    have han : a < n := by omega
    have hcm : c < m := by
      rcases lt_or_eq_of_le hc with h | h
      · exact h
      · exfalso
        rw [h, hyv, ← hxv] at hac
        have := hx.2.1 a n (by omega) le_rfl hac
        omega
    have hlu1 := honx a han.le
    have hlu2 := hony c hc
    rw [hac] at hlu1
    have hpar : a % 2 = c % 2 := by
      by_contra hne
      have e := ten_lv M (y c) a
      rw [hlu1, lv_congr M (y c) (show (a + 1) % 2 = c % 2 by omega), hlu2] at e
      have h2 := hge (y c)
      rw [e] at h2
      have : n + m ≤ a + c := by exact_mod_cast h2
      omega
    have hac' : a = c := by
      have e := lv_congr M (y c) hpar
      rw [hlu1, hlu2] at e
      exact_mod_cast e
    rw [← hac'] at hc hcm hlu2 hac
    have hupx : ∀ k, a < k → k ≤ n → tenacity M (x k) ≤ tm M := by
      intro k hk1 hk2
      rcases lt_or_eq_of_le hk2 with hk | hk
      · obtain ⟨z, hz, hzk, -, -⟩ := splice_bwd M hx hy (L := m) (j := n) (k := k) le_rfl hk2
          le_rfl (by rw [hxv, hyv]) (by omega) (by
            intro s hs i hi1 hi2 he
            rcases lt_or_eq_of_le hi2 with hi | hi
            · exact hmax i (by omega) (by omega) ⟨s, hs.le, he.symm⟩
            · rw [hi, hxv, ← hyv] at he
              have := hy.2.1 s m (by omega) le_rfl he
              omega)
        have h1 := lv_le M hz (k := k + 1) (by omega)
        rw [hzk] at h1
        rw [ten_lv M (x k) k, honx k hk2, htm]
        calc (k : ℕ∞) + lv M (x k) (k + 1) ≤ (k : ℕ∞) + ((m + (n - k) : ℕ) : ℕ∞) :=
              add_le_add le_rfl h1
          _ = ((n + m : ℕ) : ℕ∞) := by rw [← Nat.cast_add]; congr 1; omega
      · exact (by rw [hk, hxv, hv] : tenacity M (x k) = tm M).le
    have hupy : ∀ k, a < k → k ≤ m → tenacity M (y k) ≤ tm M := by
      intro k hk1 hk2
      rcases lt_or_eq_of_le hk2 with hk | hk
      · obtain ⟨z, hz, hzk, -, -⟩ := splice_bwd M hy hx (L := n) (j := m) (k := k) le_rfl hk2
          le_rfl (by rw [hxv, hyv]) hnm (by
            intro s hs i hi1 hi2 he
            rcases lt_or_eq_of_le hi2 with hi | hi
            · rcases lt_trichotomy s a with hsa | hsa | hsa
              · have e1 := honx s (by omega)
                have e2 := hony i (by omega)
                rw [he] at e1
                by_cases hp : s % 2 = i % 2
                · have e := lv_congr M (y i) hp
                  rw [e1, e2] at e
                  have : s = i := by exact_mod_cast e
                  omega
                · have e := ten_lv M (y i) i
                  rw [e2, lv_congr M (y i) (show (i + 1) % 2 = s % 2 by omega), e1] at e
                  have h2 := hge (y i)
                  rw [e] at h2
                  have : n + m ≤ i + s := by exact_mod_cast h2
                  omega
              · rw [hsa, hac] at he
                have := hy.2.1 a i (by omega) (by omega) he
                omega
              · exact hmax s hsa (by omega) ⟨i, hi2, he⟩
            · rw [hi, hyv, ← hxv] at he
              have := hx.2.1 s n (by omega) le_rfl he
              omega)
        have h1 := lv_le M hz (k := k + 1) (by omega)
        rw [hzk] at h1
        rw [ten_lv M (y k) k, hony k hk2, htm]
        calc (k : ℕ∞) + lv M (y k) (k + 1) ≤ (k : ℕ∞) + ((n + (m - k) : ℕ) : ℕ∞) :=
              add_le_add le_rfl h1
          _ = ((n + m : ℕ) : ℕ∞) := by rw [← Nat.cast_add]; congr 1; omega
      · exact (by rw [hk, hyv, hv] : tenacity M (y k) = tm M).le
    rcases eq_or_lt_of_le (tm_le M (x a)) with hu | hu
    · have hxa : lv M (x a) a = a := honx a han.le
      have h1 : mlv M (x a) ≤ (a : ℕ∞) := by
        rw [← hxa]; exact mlv_le_lv M (x a) a
      obtain ⟨d', hd'⟩ : ∃ d' : ℕ, mlv M (x a) = d' :=
        ⟨_, (ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top a) h1)).symm⟩
      have h2 : (a : ℕ∞) < mlv M v := by
        rcases mlv_cases M v n with h | h
        · rw [h, hxl]; exact_mod_cast han
        · rw [h, lv_congr M v (show (n + 1) % 2 = m % 2 by omega), hyl]; exact_mod_cast hcm
      have hdd : d' < d := by
        rw [hd'] at h1
        rw [hd] at h2
        have : d' ≤ a := by exact_mod_cast h1
        have : a < d := by exact_mod_cast h2
        omega
      exact ih d' hdd (x a) hu.symm hd' a x a y b b' (hx.prefix han.le) rfl hxa
        (hy.prefix hcm.le) hac.symm hxa (top_prefix M han.le hupx htx) (top_prefix M hcm.le hupy hty)
    · have h1 : IsTop M x n (x a) := ⟨a, han.le, rfl, hu, hupx⟩
      have h2 : IsTop M y m (x a) := ⟨a, hcm.le, hac.symm, hu, hupy⟩
      rw [top_unique M htx h1, top_unique M hty h2]
  intro n x n' x' b b' hx hxv hxl hx' hx'v hx'l htx htx'
  by_cases hp : n % 2 = n' % 2
  · have hfin : lv M v (n + 1) ≠ ⊤ := um_fin M hstd hv (n + 1)
    obtain ⟨m, y, hy, hyv, hpar, hlen⟩ := lv_attain M hfin
    have hyl : lv M v m = m := by rw [lv_congr M v hpar]; exact hlen
    obtain ⟨b3, hb3⟩ := top_exists M (x := y) m (tm_lt_ten_neutral M hstd hy.2.2.1)
    rw [opp n x m y b b3 hx hxv hxl hy hyv hyl (by omega) htx hb3,
      opp n' x' m y b' b3 hx' hx'v hx'l hy hyv hyl (by omega) htx' hb3]
  · exact opp n x n' x' b b' hx hxv hxl hx' hx'v hx'l hp htx htx'

theorem pos_getVert [DecidableEq V] {f v : V} (p : G.Walk f v) (hp : p.IsPath) {k : ℕ} (hk : k ≤ p.length) :
    (p.takeUntil (p.getVert k) (p.getVert_mem_support k)).length = k := by
  have h1 := p.getVert_length_takeUntil (p.getVert_mem_support k)
  exact hp.getVert_injOn (p.length_takeUntil_le_length _) hk h1

theorem top_of_base [DecidableEq V] (M : G.Subgraph) {f v : V} (p : G.Walk f v) (hp : p.IsPath)
    (hv : tenacity M v = tm M) {b : V} (h : IsBaseWrtPath M p b) :
    IsTop M p.getVert p.length b := by
  obtain ⟨hb, hlt, hall⟩ := h
  refine ⟨(p.takeUntil b hb).length, p.length_takeUntil_le_length hb,
    p.getVert_length_takeUntil hb, by rw [← hv]; exact hlt, fun k hk1 hk2 => ?_⟩
  rw [← hv]
  apply hall (p.getVert k) (p.getVert_mem_support k)
  rw [pos_getVert p hp hk2]; exact hk1

theorem base_of_top [DecidableEq V] (M : G.Subgraph) {f v : V} (p : G.Walk f v) (hp : p.IsPath)
    (hv : tenacity M v = tm M) {b : V} (h : IsTop M p.getVert p.length b) :
    IsBaseWrtPath M p b := by
  obtain ⟨β, hβ, hxb, hlt, hall⟩ := h
  have hb : b ∈ p.support := by rw [← hxb]; exact p.getVert_mem_support β
  refine ⟨hb, by rw [hv]; exact hlt, fun w hw hpos => ?_⟩
  rw [hv]
  have hbβ : (p.takeUntil b hb).length = β := by
    have e : p.getVert (p.takeUntil b hb).length = p.getVert β := by
      rw [p.getVert_length_takeUntil hb, hxb]
    exact hp.getVert_injOn (p.length_takeUntil_le_length hb) hβ e
  have := hall _ (by omega) (p.length_takeUntil_le_length hw)
  rwa [p.getVert_length_takeUntil hw] at this

/-- Every vertex of tenacity `t_m` has a unique base (as a set statement). -/
theorem cor2 [DecidableEq V] (M : G.Subgraph) (hstd : tm M < lm M) (v : V)
    (hv : tenacity M v = tm M) :
    ∃ (n : ℕ) (x : ℕ → V) (b0 : V), APath M n x ∧ x n = v ∧ lv M v n = n ∧ n % 2 = 0 ∧
      IsTop M x n b0 ∧ baseSet M v = {b0} := by
  have hfin := um_fin M hstd hv 0
  obtain ⟨n, x, hx, hxv, hpar, hlen⟩ := lv_attain M hfin
  have hxl : lv M v n = n := by rw [lv_congr M v hpar]; exact hlen
  obtain ⟨b0, hb0⟩ := top_exists M (x := x) n (tm_lt_ten_neutral M hstd hx.2.2.1)
  refine ⟨n, x, b0, hx, hxv, hxl, by omega, hb0, Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · obtain ⟨q, hq, hqx⟩ := walk_of_seq hx.1
    have halt := alt_of_getVert M q hq hqx hx
    subst hxv
    show ∃ (f : V) (p : G.Walk f (x n)), (IsEvenLevelPath M p ∨ IsOddLevelPath M p) ∧
      IsBaseWrtPath M p b0
    refine ⟨x 0, q, levpath_of M q halt (by rw [hq]; exact hxl), ?_⟩
    apply base_of_top M q halt.2.1 hv
    rw [hq]
    exact top_congr M (fun i hi => (hqx i hi).symm) hb0
  · intro b hb
    have hb' : ∃ (f : V) (p : G.Walk f v), (IsEvenLevelPath M p ∨ IsOddLevelPath M p) ∧
      IsBaseWrtPath M p b := hb
    obtain ⟨f, p, hp, hbase⟩ := hb'
    obtain ⟨hpx, hpl⟩ := lev_of_walk M p hp
    have hpath : p.IsPath := by rcases hp with h | h <;> exact h.1.2.1
    have ht := top_of_base M p hpath hv hbase
    have h1 : mlv M v ≤ (n : ℕ∞) := by rw [← hxl]; exact mlv_le_lv M v n
    obtain ⟨d, hd⟩ : ∃ d : ℕ, mlv M v = d :=
      ⟨_, (ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top n) h1)).symm⟩
    rw [p.getVert_length] at hpl
    exact base_unique M hstd d v hv hd p.length p.getVert n x b b0 hpx p.getVert_length hpl
      hx hxv hxl ht hb0

end Aux_MVB

namespace Aux_MVB

open MVBlossoms SimpleGraph

variable {V : Type} {G : SimpleGraph V}

theorem Tset_sub_blossom [DecidableEq V] (M : G.Subgraph) (b : V) :
    ∀ s : ℕ, ¬ ((s : ℕ∞) < tm M) → Tset M b s ⊆ blossom M b s
  | 0, h => by intro w hw; rw [blossom, if_neg h]; exact hw
  | 1, h => by intro w hw; rw [blossom, if_neg h]; exact hw
  | s + 2, h => by intro w hw; rw [blossom, if_neg h]; exact Set.mem_union_left _ hw

theorem mem_baseSet_of_walk [DecidableEq V] (M : G.Subgraph) {f v : V} (p : G.Walk f v)
    (hp : IsEvenLevelPath M p ∨ IsOddLevelPath M p) (hv : tenacity M v = tm M) {b : V}
    (h : IsTop M p.getVert p.length b) : b ∈ baseSet M v := by
  have hpath : p.IsPath := by rcases hp with h | h <;> exact h.1.2.1
  show ∃ (f : V) (p : G.Walk f v), (IsEvenLevelPath M p ∨ IsOddLevelPath M p) ∧
    IsBaseWrtPath M p b
  exact ⟨f, p, hp, base_of_top M p hpath hv h⟩

/-- Matched edges of tenacity `t_m`: both endpoints have tenacity `t_m` and the same base. -/
theorem matched_same_base [DecidableEq V] (M : G.Subgraph) (hM : M.IsMatching)
    (hstd : tm M < lm M) (u v : V) (huv : s(u, v) ∈ M.edgeSet)
    (hten : edgeTenacity M u v = tm M) :
    tenacity M u = tm M ∧ tenacity M v = tm M ∧
      ∃ b : V, baseSet M u = {b} ∧ baseSet M v = {b} := by
  have hfin : edgeTenacity M u v ≠ ⊤ := by rw [hten]; exact ne_top_of_lt hstd
  have hET : edgeTenacity M u v = oddLevel M u + oddLevel M v + 1 := by
    unfold edgeTenacity; rw [if_pos huv]
  have hfu : oddLevel M u ≠ ⊤ := by
    intro h; rw [hET, h] at hfin; simp at hfin
  have hfv : oddLevel M v ≠ ⊤ := by
    intro h; rw [hET, h] at hfin; simp at hfin
  have huv' : s(v, u) ∈ M.edgeSet := by rw [Sym2.eq_swap]; exact huv
  have hEv := Aux_MV1.even_eq M hM huv hfu
  have hEu := Aux_MV1.even_eq M hM huv' hfv
  have htv : tenacity M v = tm M := by
    rw [← hten, hET]; unfold tenacity; rw [hEv]; ring
  have htu : tenacity M u = tm M := by
    rw [← hten, hET]; unfold tenacity; rw [hEu]; ring
  refine ⟨htu, htv, ?_⟩
  obtain ⟨_, _, bu, _, _, _, _, _, hbu⟩ := cor2 M hstd u htu
  obtain ⟨_, _, bv, _, _, _, _, _, hbv⟩ := cor2 M hstd v htv
  refine ⟨bu, hbu, ?_⟩
  rw [hbv]
  -- an odd level(u) path and its extension
  obtain ⟨f, p, hp, hodd, hlen⟩ := Aux_MV1.attain_odd M hfu
  have hadj : G.Adj u v := M.adj_sub (SimpleGraph.Subgraph.mem_edgeSet.mp huv)
  obtain ⟨hP, heven⟩ := Aux_MV1.extend M hM p hp hodd huv hadj
  obtain ⟨bp, hbp⟩ := top_exists M (x := p.getVert) p.length
    (by rw [Walk.getVert_zero]; exact tm_lt_ten_neutral M hstd hp.1)
  have h1 : bp ∈ baseSet M u := mem_baseSet_of_walk M p (Or.inr ⟨hp, hodd, hlen⟩) htu hbp
  rw [hbu] at h1
  have hcl : (p.concat hadj).length = p.length + 1 := Walk.length_concat p hadj
  have hlev : ((p.concat hadj).length : ℕ∞) = evenLevel M v := by
    rw [hcl, hEv, ← hlen, Nat.cast_succ]
  have htop : IsTop M (p.concat hadj).getVert (p.concat hadj).length bp := by
    rw [hcl]
    refine top_extend M (Nat.le_succ _) (fun k hk1 hk2 => ?_)
      (top_congr M (fun i hi => (getVert_concat_le p hadj i hi).symm) hbp)
    have : k = p.length + 1 := by omega
    rw [this, getVert_concat_end]; exact htv.le
  have h2 : bp ∈ baseSet M v :=
    mem_baseSet_of_walk M (p.concat hadj) (Or.inl ⟨hP, heven, hlev⟩) htv htop
  rw [hbv] at h2
  rw [Set.mem_singleton_iff] at h1 h2
  rw [← h1, h2]

end Aux_MVB

open MVBlossoms in
theorem solution {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph)
    (hM : M.IsMatching) (hstd : tm M < lm M)
    (t₀ : ℕ) (ht₀ : (t₀ : ℕ∞) = tm M)
    (u v : V) (huv : s(u, v) ∈ M.edgeSet) (hten : edgeTenacity M u v = tm M) :
    ∃ b : V, IsBase M u b ∧ IsBase M v b ∧ u ∈ blossom M b t₀ ∧ v ∈ blossom M b t₀ := by
  obtain ⟨htu, htv, b, hbu, hbv⟩ := Aux_MVB.matched_same_base M hM hstd u v huv hten
  have hnot : ¬ ((t₀ : ℕ∞) < tm M) := by rw [ht₀]; exact lt_irrefl _
  refine ⟨b, hbu, hbv, Aux_MVB.Tset_sub_blossom M b t₀ hnot ?_,
    Aux_MVB.Tset_sub_blossom M b t₀ hnot ?_⟩
  · show tenacity M u = (t₀ : ℕ∞) ∧ IsBase M u b
    exact ⟨by rw [htu, ht₀], hbu⟩
  · show tenacity M v = (t₀ : ℕ∞) ∧ IsBase M v b
    exact ⟨by rw [htv, ht₀], hbv⟩
