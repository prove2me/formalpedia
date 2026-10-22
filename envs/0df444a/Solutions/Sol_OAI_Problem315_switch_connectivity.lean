-- Prove2me | solution 1 for OAI.Problem315.switch_connectivity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T05:14:43.70657+00:00
-- url     : https://prove2.me/submissions/6cacfdaa-b4e1-4a89-9fe6-cc600f37a556

import Mathlib
import Definitions.Def_SwitchChain

set_option linter.all false

namespace OAI.Problem315

open SimpleGraph

variable {n : ℕ}

/-- The 2-switch replacing the edges `ab, ce` by `ac, be`. -/
def sw (G : SimpleGraph (Fin n)) (a b c e : Fin n) : SimpleGraph (Fin n) :=
  replaceEdges G (fromEdgeSet {s(a, b), s(c, e)}) (fromEdgeSet {s(a, c), s(b, e)})

lemma sw_adj (G : SimpleGraph (Fin n)) (a b c e u w : Fin n) :
    (sw G a b c e).Adj u w ↔
      (G.Adj u w ∧ ¬ ((s(u, w) = s(a, b) ∨ s(u, w) = s(c, e)) ∧ u ≠ w)) ∨
        ((s(u, w) = s(a, c) ∨ s(u, w) = s(b, e)) ∧ u ≠ w) := by
  show (G.Adj u w ∧ ¬ (fromEdgeSet _).Adj u w) ∨ (fromEdgeSet _).Adj u w ↔ _
  simp only [fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff]

structure Dist (a b c e : Fin n) : Prop where
  ab : a ≠ b
  ac : a ≠ c
  ae : a ≠ e
  bc : b ≠ c
  be : b ≠ e
  ce : c ≠ e

lemma sw_adj_a {G : SimpleGraph (Fin n)} {a b c e : Fin n} (h : Dist a b c e) (w : Fin n) :
    (sw G a b c e).Adj a w ↔ (G.Adj a w ∧ w ≠ b) ∨ w = c := by
  have := h.ab; have := h.ac; have := h.ae; have := h.bc; have := h.be; have := h.ce
  rw [sw_adj]
  simp only [Sym2.eq_iff]
  by_cases hb : w = b
  · subst hb; simp_all
  · by_cases hc : w = c
    · subst hc; simp_all
    · constructor
      · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
        · exact Or.inl ⟨h1, hb⟩
        · exfalso; rcases h1 with (⟨-, h⟩ | ⟨h, -⟩) | (⟨h, -⟩ | ⟨h, -⟩) <;> simp_all
      · rintro (⟨h1, -⟩ | h1)
        · left; refine ⟨h1, fun ⟨h3, _⟩ => ?_⟩
          rcases h3 with (⟨-, h⟩ | ⟨h, -⟩) | (⟨h, -⟩ | ⟨h, -⟩) <;> simp_all
        · exact absurd h1 hc

lemma sw_symm_args (G : SimpleGraph (Fin n)) (a b c e : Fin n) :
    sw G a b c e = sw G b a e c := by
  ext u w
  rw [sw_adj, sw_adj]
  have h1 : (s(u, w) = s(a, b) ∨ s(u, w) = s(c, e)) ↔ (s(u, w) = s(b, a) ∨ s(u, w) = s(e, c)) := by
    rw [Sym2.eq_swap (a := a), Sym2.eq_swap (a := c)]
  have h2 : (s(u, w) = s(a, c) ∨ s(u, w) = s(b, e)) ↔ (s(u, w) = s(b, e) ∨ s(u, w) = s(a, c)) :=
    or_comm
  rw [h1, h2]

lemma sw_comm_args (G : SimpleGraph (Fin n)) (a b c e : Fin n) :
    sw G a b c e = sw G c e a b := by
  ext u w
  rw [sw_adj, sw_adj]
  have h1 : (s(u, w) = s(a, b) ∨ s(u, w) = s(c, e)) ↔ (s(u, w) = s(c, e) ∨ s(u, w) = s(a, b)) :=
    or_comm
  have h2 : (s(u, w) = s(a, c) ∨ s(u, w) = s(b, e)) ↔ (s(u, w) = s(c, a) ∨ s(u, w) = s(e, b)) := by
    rw [Sym2.eq_swap (a := c), Sym2.eq_swap (a := e)]
  rw [h1, h2]

lemma Dist.symm1 {a b c e : Fin n} (h : Dist a b c e) : Dist b a e c :=
  ⟨h.ab.symm, h.be, h.bc, h.ae, h.ac, h.ce.symm⟩

lemma Dist.symm2 {a b c e : Fin n} (h : Dist a b c e) : Dist c e a b :=
  ⟨h.ce, h.ac.symm, h.bc.symm, h.ae.symm, h.be.symm, h.ab⟩

lemma sw_adj_b {G : SimpleGraph (Fin n)} {a b c e : Fin n} (h : Dist a b c e) (w : Fin n) :
    (sw G a b c e).Adj b w ↔ (G.Adj b w ∧ w ≠ a) ∨ w = e := by
  rw [sw_symm_args]; exact sw_adj_a h.symm1 w

lemma sw_adj_c {G : SimpleGraph (Fin n)} {a b c e : Fin n} (h : Dist a b c e) (w : Fin n) :
    (sw G a b c e).Adj c w ↔ (G.Adj c w ∧ w ≠ e) ∨ w = a := by
  rw [sw_comm_args]; exact sw_adj_a h.symm2 w

lemma sw_adj_e {G : SimpleGraph (Fin n)} {a b c e : Fin n} (h : Dist a b c e) (w : Fin n) :
    (sw G a b c e).Adj e w ↔ (G.Adj e w ∧ w ≠ c) ∨ w = b := by
  rw [sw_comm_args]; exact sw_adj_b h.symm2 w

lemma sw_adj_other {G : SimpleGraph (Fin n)} {a b c e u : Fin n}
    (hu : u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ u ≠ e) (w : Fin n) :
    (sw G a b c e).Adj u w ↔ G.Adj u w := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  rw [sw_adj]
  simp only [Sym2.eq_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact h
    · exfalso; rcases h with (⟨h, -⟩ | ⟨h, -⟩) | (⟨h, -⟩ | ⟨h, -⟩) <;> tauto
  · intro h; left; refine ⟨h, fun ⟨h', _⟩ => ?_⟩
    rcases h' with (⟨h, -⟩ | ⟨h, -⟩) | (⟨h, -⟩ | ⟨h, -⟩) <;> tauto

lemma graphDegree_eq_of_iff (G G' : SimpleGraph (Fin n)) (u r t : Fin n) (hr : G.Adj u r)
    (ht : ¬ G.Adj u t) (h : ∀ w, G'.Adj u w ↔ (G.Adj u w ∧ w ≠ r) ∨ w = t) :
    graphDegree G' u = graphDegree G u := by
  classical
  unfold graphDegree
  have hfin : (Finset.univ.filter (fun w => G'.Adj u w)) =
      insert t ((Finset.univ.filter (fun w => G.Adj u w)).erase r) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase, h]
    tauto
  have hr' : r ∈ Finset.univ.filter (fun w => G.Adj u w) := by simpa using hr
  have ht' : t ∉ (Finset.univ.filter (fun w => G.Adj u w)).erase r := by simp [ht]
  rw [hfin, Finset.card_insert_of_notMem ht', Finset.card_erase_of_mem hr']
  have : 0 < (Finset.univ.filter (fun w => G.Adj u w)).card := Finset.card_pos.mpr ⟨r, hr'⟩
  omega

lemma sw_realizes {d : Fin n → ℕ} {G : SimpleGraph (Fin n)} (hG : Realizes n d G)
    {a b c e : Fin n} (h : Dist a b c e) (hab : G.Adj a b) (hce : G.Adj c e)
    (hac : ¬ G.Adj a c) (hbe : ¬ G.Adj b e) : Realizes n d (sw G a b c e) := by
  intro u
  rw [← hG u]
  by_cases ua : u = a
  · subst ua; exact graphDegree_eq_of_iff _ _ _ b c hab hac (sw_adj_a h)
  by_cases ub : u = b
  · subst ub; exact graphDegree_eq_of_iff _ _ _ a e hab.symm hbe (sw_adj_b h)
  by_cases uc : u = c
  · subst uc; exact graphDegree_eq_of_iff _ _ _ e a hce (fun h' => hac h'.symm) (sw_adj_c h)
  by_cases ue : u = e
  · subst ue; exact graphDegree_eq_of_iff _ _ _ c b hce.symm (fun h' => hbe h'.symm) (sw_adj_e h)
  unfold graphDegree
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact sw_adj_other ⟨ua, ub, uc, ue⟩ w

lemma pm_of {a b c e : Fin n} (h : Dist a b c e) :
    IsPerfectMatchingOn ({a, b, c, e} : Finset (Fin n)) (fromEdgeSet {s(a, b), s(c, e)}) := by
  have := h.ab; have := h.ac; have := h.ae; have := h.bc; have := h.be; have := h.ce
  have := h.ab.symm; have := h.ac.symm; have := h.ae.symm; have := h.bc.symm; have := h.be.symm
  have := h.ce.symm
  intro v
  simp only [fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · refine ⟨b, by simp_all, fun w hw => ?_⟩
      rcases hw with ⟨(⟨-, h⟩ | ⟨h, -⟩) | (⟨h, -⟩ | ⟨h, -⟩), -⟩ <;> simp_all
    · refine ⟨a, by simp_all, fun w hw => ?_⟩
      rcases hw with ⟨(⟨h, -⟩ | ⟨-, h⟩) | (⟨h, -⟩ | ⟨h, -⟩), -⟩ <;> simp_all
    · refine ⟨e, by simp_all, fun w hw => ?_⟩
      rcases hw with ⟨(⟨h, -⟩ | ⟨h, -⟩) | (⟨-, h⟩ | ⟨h, -⟩), -⟩ <;> simp_all
    · refine ⟨c, by simp_all, fun w hw => ?_⟩
      rcases hw with ⟨(⟨h, -⟩ | ⟨h, -⟩) | (⟨h, -⟩ | ⟨-, h⟩), -⟩ <;> simp_all
  · intro hv w hw
    rcases hw with ⟨(⟨h, -⟩ | ⟨h, -⟩) | (⟨h, -⟩ | ⟨h, -⟩), -⟩ <;> simp_all

lemma switchStep_sw {d : Fin n → ℕ} (G : GraphState n d) {a b c e : Fin n} (h : Dist a b c e)
    (hab : G.1.Adj a b) (hce : G.1.Adj c e) (hac : ¬ G.1.Adj a c) (hbe : ¬ G.1.Adj b e) :
    SwitchStep n d G ⟨sw G.1 a b c e, sw_realizes G.2 h hab hce hac hbe⟩ := by
  classical
  have := h.ab; have := h.ac; have := h.ae; have := h.bc; have := h.be; have := h.ce
  have hS : ({a, b, c, e} : Finset (Fin n)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp_all), Finset.card_insert_of_notMem (by simp_all),
      Finset.card_pair h.ce]
  let S : FourSet n := ⟨{a, b, c, e}, hS⟩
  let M : PerfectMatching S := ⟨fromEdgeSet {s(a, b), s(c, e)}, pm_of h⟩
  have h' : Dist a c b e := ⟨h.ac, h.ab, h.ae, h.bc.symm, h.ce, h.be⟩
  let N : PerfectMatching S := ⟨fromEdgeSet {s(a, c), s(b, e)}, by
    have := pm_of h'
    rwa [Finset.insert_comm c b] at this⟩
  have hM : M.1.Adj a b := by simp [M, fromEdgeSet_adj, h.ab]
  have hN : ¬ N.1.Adj a b := by
    simp only [N, fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff]
    rintro ⟨(⟨-, h1⟩ | ⟨h1, -⟩) | (⟨h1, -⟩ | ⟨h1, -⟩), -⟩ <;> simp_all
  have hne : M ≠ N := fun heq => hN (heq ▸ hM)
  have hvalid : validSwitch G.1 ⟨S, ⟨(M, N), hne⟩⟩ := by
    constructor
    · intro u w huw
      simp only [removedMatching, M, fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff,
        Sym2.eq_iff] at huw
      rcases huw with ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), -⟩
      · exact hab
      · exact hab.symm
      · exact hce
      · exact hce.symm
    · intro u w huw
      simp only [addedMatching, N, fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff,
        Sym2.eq_iff] at huw
      rcases huw with ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), -⟩
      · exact hac
      · exact fun h'' => hac h''.symm
      · exact hbe
      · exact fun h'' => hbe h''.symm
  refine ⟨⟨S, ⟨(M, N), hne⟩⟩, hvalid, ?_⟩
  simp only [proposalResult, if_pos hvalid]
  rfl

lemma sw_sw {G : SimpleGraph (Fin n)} {a b c e : Fin n} (h : Dist a b c e)
    (hab : G.Adj a b) (hce : G.Adj c e) (hac : ¬ G.Adj a c) (hbe : ¬ G.Adj b e) :
    sw (sw G a b c e) a c b e = G := by
  have := h.ab; have := h.ac; have := h.ae; have := h.bc; have := h.be; have := h.ce
  ext u w
  rw [sw_adj, sw_adj]
  have key : ∀ u w, G.Adj u w ↔ s(u, w) ∈ G.edgeSet := fun _ _ => (mem_edgeSet G).symm
  have hd : u ≠ w ↔ ¬ (s(u, w)).IsDiag := by simp
  rw [key u w, hd]
  have d1 : s(a, b) ≠ s(c, e) := by simp [Sym2.eq_iff]; tauto
  have d2 : s(a, b) ≠ s(a, c) := by simp [Sym2.eq_iff]; tauto
  have d3 : s(a, b) ≠ s(b, e) := by simp [Sym2.eq_iff]; tauto
  have d4 : s(c, e) ≠ s(a, c) := by simp [Sym2.eq_iff]; tauto
  have d5 : s(c, e) ≠ s(b, e) := by simp [Sym2.eq_iff]; tauto
  have d6 : s(a, c) ≠ s(b, e) := by simp [Sym2.eq_iff]; tauto
  rw [key a b] at hab; rw [key c e] at hce; rw [key a c] at hac; rw [key b e] at hbe
  have n1 : ¬ (s(a, b)).IsDiag := by simpa using h.ab
  have n2 : ¬ (s(c, e)).IsDiag := by simpa using h.ce
  have n3 : ¬ (s(a, c)).IsDiag := by simpa using h.ac
  have n4 : ¬ (s(b, e)).IsDiag := by simpa using h.be
  clear key hd
  generalize s(u, w) = P
  by_cases h1 : P = s(a, b)
  · subst h1; simp [hab, n1, d1, d2, d3]
  by_cases h2 : P = s(c, e)
  · subst h2; simp [hce, n2, d1.symm, d4, d5]
  by_cases h3 : P = s(a, c)
  · subst h3; simp [hac, n3, d2.symm, d4.symm, d6]
  by_cases h4 : P = s(b, e)
  · subst h4; simp [hbe, n4, d3.symm, d5.symm, d6.symm]
  simp [h1, h2, h3, h4]

/-- Graphs agreeing at all vertices `< k`. -/
def Agree (k : ℕ) (G H : SimpleGraph (Fin n)) : Prop :=
  ∀ u : Fin n, u.val < k → ∀ w, G.Adj u w ↔ H.Adj u w

open Classical in
/-- Number of neighbours of `u` among the vertices `≥ k`. -/
noncomputable def outDeg (k : ℕ) (K : SimpleGraph (Fin n)) (u : Fin n) : ℕ :=
  (Finset.univ.filter (fun z => k ≤ z.val ∧ K.Adj u z)).card

lemma outDeg_eq {d : Fin n → ℕ} (G H : GraphState n d) {k : ℕ} (hA : Agree k G.1 H.1)
    (u : Fin n) : outDeg k G.1 u = outDeg k H.1 u := by
  classical
  have hG := G.2 u
  have hH := H.2 u
  unfold graphDegree at hG hH
  have split : ∀ K : SimpleGraph (Fin n), (Finset.univ.filter (fun w => K.Adj u w)).card =
      (Finset.univ.filter (fun z => z.val < k ∧ K.Adj u z)).card + outDeg k K u := by
    intro K
    unfold outDeg
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro hz; by_cases hk : z.val < k
        · exact Or.inl ⟨hk, hz⟩
        · exact Or.inr ⟨by omega, hz⟩
      · rintro (⟨-, hz⟩ | ⟨-, hz⟩) <;> exact hz
    · rw [Finset.disjoint_left]; intro z h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
  have hin : (Finset.univ.filter (fun z => z.val < k ∧ G.1.Adj u z)) =
      (Finset.univ.filter (fun z => z.val < k ∧ H.1.Adj u z)) := by
    ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hk, hz⟩; exact ⟨hk, ((hA z hk u).1 hz.symm).symm⟩
    · rintro ⟨hk, hz⟩; exact ⟨hk, ((hA z hk u).2 hz.symm).symm⟩
  have e1 := split G.1
  have e2 := split H.1
  rw [hin] at e1
  omega

lemma count_lemma (K : SimpleGraph (Fin n)) (k : ℕ) (x y v : Fin n) (hkx : k ≤ x.val)
    (hky : k ≤ y.val) (hkv : k ≤ v.val) (hxv : K.Adj x v) (hyv : ¬ K.Adj y v) (hvy : v ≠ y)
    (hno : ∀ z, k ≤ z.val → z ≠ x → K.Adj y z → K.Adj x z) :
    outDeg k K y + 1 ≤ outDeg k K x := by
  classical
  unfold outDeg
  set A := Finset.univ.filter (fun z => k ≤ z.val ∧ K.Adj y z)
  set B := Finset.univ.filter (fun z => k ≤ z.val ∧ K.Adj x z)
  have hsub : A.erase x ⊆ (B.erase y).erase v := by
    intro z hz
    simp only [A, B, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    obtain ⟨hzx, hkz, hyz⟩ := hz
    refine ⟨fun hzv => hyv (hzv ▸ hyz), K.ne_of_adj hyz |>.symm, hkz, hno z hkz hzx hyz⟩
  have hvB : v ∈ B.erase y := by
    simp only [B, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hvy, hkv, hxv⟩
  have c1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hvB] at c1
  have hpos : 0 < (B.erase y).card := Finset.card_pos.mpr ⟨v, hvB⟩
  by_cases hxy : K.Adj x y
  · have hxA : x ∈ A := by simp [A, hkx, hxy.symm]
    have hyB : y ∈ B := by simp [B, hky, hxy]
    rw [Finset.card_erase_of_mem hxA] at c1
    rw [Finset.card_erase_of_mem hyB] at c1 hpos
    have : 0 < A.card := Finset.card_pos.mpr ⟨x, hxA⟩
    omega
  · have hxA : x ∉ A := by simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; exact fun ⟨_, h⟩ => hxy h.symm
    have hyB : y ∉ B := by simp [B, hxy]
    rw [Finset.erase_eq_of_notMem hxA] at c1
    rw [Finset.erase_eq_of_notMem hyB] at c1 hpos
    omega

lemma exists_switch {d : Fin n → ℕ} (G H : GraphState n d) {k : ℕ} (hA : Agree k G.1 H.1)
    (v x y : Fin n) (hv : v.val = k) (hx : G.1.Adj v x) (hx' : ¬ H.1.Adj v x)
    (hy : H.1.Adj v y) (hy' : ¬ G.1.Adj v y) :
    k ≤ x.val ∧ k ≤ y.val ∧
    ((∃ z, k ≤ z.val ∧ z ≠ x ∧ G.1.Adj y z ∧ ¬ G.1.Adj x z) ∨
      (∃ z, k ≤ z.val ∧ z ≠ y ∧ H.1.Adj x z ∧ ¬ H.1.Adj y z)) := by
  have hkx : k ≤ x.val := by
    by_contra hlt; push Not at hlt
    exact hx' ((hA x hlt v).1 hx.symm).symm
  have hky : k ≤ y.val := by
    by_contra hlt; push Not at hlt
    exact hy' ((hA y hlt v).2 hy.symm).symm
  refine ⟨hkx, hky, ?_⟩
  by_contra hno
  push Not at hno
  obtain ⟨h1, h2⟩ := hno
  have c1 := count_lemma G.1 k x y v hkx hky hv.ge hx.symm (fun h => hy' h.symm)
    (H.1.ne_of_adj hy)
    (fun z hz hzx hyz => h1 z hz hzx hyz)
  have c2 := count_lemma H.1 k y x v hky hkx hv.ge hy.symm (fun h => hx' h.symm)
    (G.1.ne_of_adj hx)
    (fun z hz hzy hxz => h2 z hz hzy hxz)
  have e1 := outDeg_eq G H hA x
  have e2 := outDeg_eq G H hA y
  omega

lemma exists_other {G H : SimpleGraph (Fin n)} {u : Fin n}
    (hdeg : graphDegree G u = graphDegree H u) (w : Fin n) (hw : G.Adj u w) (hw' : ¬ H.Adj u w) :
    ∃ y, H.Adj u y ∧ ¬ G.Adj u y := by
  classical
  by_contra hno
  push Not at hno
  unfold graphDegree at hdeg
  have hss : (Finset.univ.filter (fun y => H.Adj u y)) ⊂ (Finset.univ.filter (fun y => G.Adj u y)) := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨w, by simpa using hw, by simpa using hw'⟩
    · intro y hy; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢; exact hno y hy
  have := Finset.card_lt_card hss
  omega

open Classical in
noncomputable def diffCount (v : Fin n) (G H : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter (fun w => ¬ (G.Adj v w ↔ H.Adj v w))).card

lemma ne_of_le_lt {k : ℕ} {u a : Fin n} (hu : u.val < k) (ha : k ≤ a.val) : u ≠ a :=
  fun h => by subst h; omega

lemma agree_sw_left {k : ℕ} {G H : SimpleGraph (Fin n)} (hA : Agree k G H) {a b c e : Fin n}
    (ha : k ≤ a.val) (hb : k ≤ b.val) (hc : k ≤ c.val) (he : k ≤ e.val) :
    Agree k (sw G a b c e) H := by
  intro u hu w
  rw [sw_adj_other ⟨ne_of_le_lt hu ha, ne_of_le_lt hu hb, ne_of_le_lt hu hc, ne_of_le_lt hu he⟩]
  exact hA u hu w

lemma agree_sw_right {k : ℕ} {G H : SimpleGraph (Fin n)} (hA : Agree k G H) {a b c e : Fin n}
    (ha : k ≤ a.val) (hb : k ≤ b.val) (hc : k ≤ c.val) (he : k ≤ e.val) :
    Agree k G (sw H a b c e) := by
  intro u hu w
  rw [sw_adj_other ⟨ne_of_le_lt hu ha, ne_of_le_lt hu hb, ne_of_le_lt hu hc, ne_of_le_lt hu he⟩]
  exact hA u hu w

/-- Replacing the neighbourhood of `v` by one that differs from `N_G(v)` only by removing
`x ∈ diff` and adding `y ∈ diff` decreases the difference count. -/
lemma diffCount_lt {G G' H : SimpleGraph (Fin n)} {v x y : Fin n} (hxy : x ≠ y)
    (hx : G.Adj v x) (hx' : ¬ H.Adj v x) (hy : H.Adj v y)
    (h : ∀ w, G'.Adj v w ↔ (G.Adj v w ∧ w ≠ x) ∨ w = y) :
    diffCount v G' H < diffCount v G H := by
  classical
  unfold diffCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨x, by simp [hx, hx'], ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, h, not_not]
    simp [hxy, hx']
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, h] at hw ⊢
    by_cases hwx : w = x
    · subst hwx; simp_all
    by_cases hwy : w = y
    · subst hwy; simp_all
    simp_all

lemma diffCount_lt' {G H H' : SimpleGraph (Fin n)} {v x y : Fin n} (hxy : x ≠ y)
    (hy : H.Adj v y) (hy' : ¬ G.Adj v y) (hx : G.Adj v x)
    (h : ∀ w, H'.Adj v w ↔ (H.Adj v w ∧ w ≠ y) ∨ w = x) :
    diffCount v G H' < diffCount v G H := by
  have e : ∀ K L : SimpleGraph (Fin n), diffCount v K L = diffCount v L K := by
    intro K L
    classical
    unfold diffCount
    congr 1
    ext w
    simp [iff_comm]
  rw [e G H', e G H]
  exact diffCount_lt hxy.symm hy hy' hx h

lemma agree_succ {k : ℕ} (hk : k < n) {G H : SimpleGraph (Fin n)} (hA : Agree k G H)
    (h0 : diffCount ⟨k, hk⟩ G H = 0) : Agree (k + 1) G H := by
  classical
  intro u hu w
  rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | hu
  · exact hA u hu w
  · have : u = ⟨k, hk⟩ := Fin.ext hu
    subst this
    by_contra hne
    unfold diffCount at h0
    rw [Finset.card_eq_zero] at h0
    have : w ∈ (Finset.univ.filter (fun w => ¬ (G.Adj ⟨k, hk⟩ w ↔ H.Adj ⟨k, hk⟩ w))) := by
      simpa using hne
    rw [h0] at this
    simp at this

theorem conn_step {d : Fin n → ℕ} {k : ℕ} (hk : k < n)
    (IH : ∀ G H : GraphState n d, Agree (k + 1) G.1 H.1 →
      Relation.ReflTransGen (SwitchStep n d) G H) :
    ∀ m, ∀ G H : GraphState n d, Agree k G.1 H.1 → diffCount ⟨k, hk⟩ G.1 H.1 ≤ m →
      Relation.ReflTransGen (SwitchStep n d) G H := by
  intro m
  induction m with
  | zero =>
    intro G H hA hm
    exact IH G H (agree_succ hk hA (by omega))
  | succ m ih =>
    intro G H hA hm
    set v : Fin n := ⟨k, hk⟩ with hvdef
    by_cases h0 : diffCount v G.1 H.1 = 0
    · exact IH G H (agree_succ hk hA h0)
    have hdeg : graphDegree G.1 v = graphDegree H.1 v := (G.2 v).trans (H.2 v).symm
    -- find x ∈ N_G(v) \ N_H(v) and y ∈ N_H(v) \ N_G(v)
    obtain ⟨x, y, hx, hx', hy, hy'⟩ : ∃ x y, G.1.Adj v x ∧ ¬ H.1.Adj v x ∧ H.1.Adj v y ∧
        ¬ G.1.Adj v y := by
      classical
      obtain ⟨w, hw⟩ : ∃ w, ¬ (G.1.Adj v w ↔ H.1.Adj v w) := by
        by_contra hno
        push Not at hno
        apply h0
        unfold diffCount
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro w _; exact not_not.mpr (hno w)
      by_cases hGw : G.1.Adj v w
      · have hHw : ¬ H.1.Adj v w := fun h => hw ⟨fun _ => h, fun _ => hGw⟩
        obtain ⟨y, hy, hy'⟩ := exists_other hdeg w hGw hHw
        exact ⟨w, y, hGw, hHw, hy, hy'⟩
      · have hHw : H.1.Adj v w := by
          by_contra h; exact hw ⟨fun h' => absurd h' hGw, fun h' => absurd h' h⟩
        obtain ⟨x, hx, hx'⟩ := exists_other hdeg.symm w hHw hGw
        exact ⟨x, w, hx, hx', hHw, hGw⟩
    obtain ⟨hkx, hky, hcase⟩ := exists_switch G H hA v x y rfl hx hx' hy hy'
    have hvx : v ≠ x := G.1.ne_of_adj hx
    have hvy : v ≠ y := H.1.ne_of_adj hy
    have hxy : x ≠ y := fun h => hy' (h ▸ hx)
    have hkv : k ≤ v.val := le_rfl
    rcases hcase with ⟨z, hkz, hzx, hyz, hxz⟩ | ⟨z, hkz, hzy, hxz, hyz⟩
    · -- switch in `G`
      have hvz : v ≠ z := fun h => hy' (h ▸ hyz).symm
      have hD : Dist v x y z := ⟨hvx, hvy, hvz, hxy, hzx.symm, G.1.ne_of_adj hyz⟩
      have step := switchStep_sw G hD hx hyz hy' hxz
      refine Relation.ReflTransGen.head step (ih _ H (agree_sw_left hA hkv hkx hky hkz) ?_)
      have := diffCount_lt (G' := sw G.1 v x y z) hxy hx hx' hy (sw_adj_a hD)
      show diffCount v (sw G.1 v x y z) H.1 ≤ m
      omega
    · -- switch in `H`, then switch back
      have hvz : v ≠ z := fun h => hx' (h ▸ hxz).symm
      have hD : Dist v y x z := ⟨hvy, hvx, hvz, hxy.symm, hzy.symm, H.1.ne_of_adj hxz⟩
      let H' : GraphState n d := ⟨sw H.1 v y x z, sw_realizes H.2 hD hy hxz hx' hyz⟩
      have c1 : Relation.ReflTransGen (SwitchStep n d) G H' := by
        refine ih G H' (agree_sw_right hA hkv hky hkx hkz) ?_
        have := diffCount_lt' (H' := sw H.1 v y x z) hxy hy hy' hx (sw_adj_a hD)
        show diffCount v G.1 (sw H.1 v y x z) ≤ m
        omega
      have hD' : Dist v x y z := ⟨hvx, hvy, hvz, hxy, H.1.ne_of_adj hxz, hzy.symm⟩
      have a1 : H'.1.Adj v x := (sw_adj_a hD x).2 (Or.inr rfl)
      have a2 : H'.1.Adj y z := (sw_adj_b hD z).2 (Or.inr rfl)
      have a3 : ¬ H'.1.Adj v y := by
        intro h; rcases (sw_adj_a hD y).1 h with ⟨-, h⟩ | h
        · exact h rfl
        · exact hxy h.symm
      have a4 : ¬ H'.1.Adj x z := by
        intro h; rcases (sw_adj_c hD z).1 h with ⟨-, h⟩ | h
        · exact h rfl
        · exact hvz h.symm
      have step := switchStep_sw H' hD' a1 a2 a3 a4
      have hback : (⟨sw H'.1 v x y z, sw_realizes H'.2 hD' a1 a2 a3 a4⟩ : GraphState n d) = H :=
        Subtype.ext (sw_sw hD hy hxz hx' hyz)
      rw [hback] at step
      exact c1.tail step

theorem conn_all {d : Fin n → ℕ} :
    ∀ j, ∀ G H : GraphState n d, Agree (n - j) G.1 H.1 →
      Relation.ReflTransGen (SwitchStep n d) G H := by
  intro j
  induction j with
  | zero =>
    intro G H hA
    have : G = H := by
      apply Subtype.ext
      ext u w
      exact hA u (by simp) w
    subst this
    exact Relation.ReflTransGen.refl
  | succ j ih =>
    intro G H hA
    by_cases hj : j < n
    · have hk : n - (j + 1) < n := by omega
      refine conn_step hk (fun G H hA' => ih G H ?_) _ G H hA le_rfl
      have : n - j = n - (j + 1) + 1 := by omega
      rw [this]; exact hA'
    · have : n - (j + 1) = n - j := by omega
      rw [this] at hA
      exact ih G H hA

end OAI.Problem315

theorem solution :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → OAI.Problem315.Graphical n d →
      ∀ G H : OAI.Problem315.GraphState n d,
        Relation.ReflTransGen (OAI.Problem315.SwitchStep n d) G H := by
  intro n d _ _ _ G H
  refine OAI.Problem315.conn_all n G H ?_
  intro u hu
  simp at hu
