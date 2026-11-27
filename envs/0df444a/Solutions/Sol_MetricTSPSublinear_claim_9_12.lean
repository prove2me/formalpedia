-- Prove2me | solution 1 for MetricTSPSublinear.claim_9_12
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:34:14.237296+00:00
-- url     : https://prove2.me/submissions/7fff382e-e612-4081-90ad-fa73873d9769

import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_Dominated
import Definitions.Def_MetricTSPSublinear_IsDualFeasible
import Definitions.Def_MetricTSPSublinear_SteinerTree
import Definitions.Def_TreeCoverLB_WeightedTree
import Mathlib

section ASM0
-- from Solutions.GT.Merge

/-!
# The merge process of Claim 9.12 (Azarmehr–Behnezhad, arXiv:2611.04283, p.43–44)

Terminals `Fin (m+1)`, merge edges `(ea j, eb j)`, `j : Fin m`, processed in the order `j = 0, 1, …, m-1`.
Tree nodes `Fin (2m+2)`: node `0` is the root `z`, merge step `j` creates node `m - j` (so merge nodes are
`1, …, m`, numbered in reverse creation order), terminal `i` is node `m + 1 + i`.

The state after `s` steps is a pair `(rt, pa)`: `rt i` is the current root of the component of terminal `i`, and
`pa` is the parent array built so far (`0` = not yet set). Step `s` with edge `(a, b)`, `r₁ = rt a`, `r₂ = rt b`,
`w = node (m - s)`: set `pa r₁ = pa r₂ = w` and redirect every terminal whose root is `r₁` or `r₂` to `w`.
This is exactly the procedure of the paper ("create a new node r joined to the current component roots r₁, r₂").
-/

open scoped Classical

namespace MTSPGT
open SimpleGraph

section Merge
variable {m : ℕ} (ea eb : Fin m → Fin (m + 1))

/-- `ℕ`-indexed endpoint (junk `0` beyond `m`). -/
def ext (e : Fin m → Fin (m + 1)) (j : ℕ) : Fin (m + 1) := if h : j < m then e ⟨j, h⟩ else 0

lemma ext_fin (e : Fin m → Fin (m + 1)) (j : Fin m) : ext e j = e j := by
  simp [ext, j.isLt]

/-- The node of terminal `i`. -/
def tnode (i : Fin (m + 1)) : Fin (2 * m + 1 + 1) := ⟨m + 1 + i.val, by omega⟩

/-- The node created by merge step `j`. -/
def mnode (m j : ℕ) : Fin (2 * m + 1 + 1) := ⟨m - j, by omega⟩

@[simp] lemma tnode_val (i : Fin (m + 1)) : (tnode i).val = m + 1 + i.val := rfl
@[simp] lemma mnode_val (j : ℕ) : (mnode m j).val = m - j := rfl

lemma tnode_inj : Function.Injective (tnode (m := m)) := by
  intro a b h
  have := congrArg Fin.val h
  simp at this
  exact Fin.ext this

/-- The state: (current component roots, parent array). -/
abbrev State (m : ℕ) := (Fin (m + 1) → Fin (2 * m + 1 + 1)) × (Fin (2 * m + 1 + 1) → Fin (2 * m + 1 + 1))

/-- One merge step. -/
def step (s : ℕ) (st : State m) : State m :=
  (fun i => if st.1 i = st.1 (ext ea s) ∨ st.1 i = st.1 (ext eb s) then mnode m s else st.1 i,
   fun x => if x = st.1 (ext ea s) ∨ x = st.1 (ext eb s) then mnode m s else st.2 x)

/-- The state after `s` steps. -/
def state : ℕ → State m
  | 0 => (tnode, fun _ => 0)
  | s + 1 => step ea eb s (state s)

/-- Component roots after `s` steps. -/
def rt (s : ℕ) : Fin (m + 1) → Fin (2 * m + 1 + 1) := (state ea eb s).1
/-- Parent array after `s` steps. -/
def pa (s : ℕ) : Fin (2 * m + 1 + 1) → Fin (2 * m + 1 + 1) := (state ea eb s).2

/-- The final parent array: the constructed tree. -/
def par : Fin (2 * m + 1 + 1) → Fin (2 * m + 1 + 1) := pa ea eb m

lemma rt_zero (i : Fin (m + 1)) : rt ea eb 0 i = tnode i := rfl
lemma pa_zero (x : Fin (2 * m + 1 + 1)) : pa ea eb 0 x = 0 := rfl

/-- The two roots joined at step `s`. -/
def R12 (s : ℕ) (x : Fin (2 * m + 1 + 1)) : Prop :=
  x = rt ea eb s (ext ea s) ∨ x = rt ea eb s (ext eb s)

lemma rt_succ (s : ℕ) (i : Fin (m + 1)) :
    rt ea eb (s + 1) i = if R12 ea eb s (rt ea eb s i) then mnode m s else rt ea eb s i := by
  simp only [rt, R12, state, step]; congr

lemma pa_succ (s : ℕ) (x : Fin (2 * m + 1 + 1)) :
    pa ea eb (s + 1) x = if R12 ea eb s x then mnode m s else pa ea eb s x := by
  simp only [pa, rt, R12, state, step]; congr

/-- The basic invariants. -/
theorem inv (s : ℕ) (hs : s ≤ m) :
    (∀ i, (rt ea eb s i = tnode i ∨ (rt ea eb s i).val ≤ m) ∧ m - s < (rt ea eb s i).val) ∧
    (∀ x, pa ea eb s x = 0 ∨
      (m - s < (pa ea eb s x).val ∧ (pa ea eb s x).val ≤ m ∧ (pa ea eb s x).val < x.val)) ∧
    (∀ x : Fin (2 * m + 1 + 1), x.val ≤ m - s → pa ea eb s x = 0) ∧
    (∀ i, pa ea eb s (rt ea eb s i) = 0) := by
  induction s with
  | zero =>
    refine ⟨fun i => ⟨Or.inl rfl, ?_⟩, fun x => Or.inl rfl, fun x _ => rfl, fun i => rfl⟩
    simp [rt_zero]; omega
  | succ s ih =>
    obtain ⟨hA, hB, hC, hD⟩ := ih (by omega)
    have hR : ∀ x, R12 ea eb s x → m - s < x.val := by
      rintro x (h | h) <;> rw [h] <;> exact (hA _).2
    refine ⟨fun i => ?_, fun x => ?_, fun x hx => ?_, fun i => ?_⟩
    · rw [rt_succ]
      split_ifs with h
      · refine ⟨Or.inr ?_, ?_⟩ <;> simp <;> omega
      · exact ⟨(hA i).1, by have := (hA i).2; omega⟩
    · rw [pa_succ]
      split_ifs with h
      · right; have := hR x h; simp; omega
      · rcases hB x with h' | h'
        · exact Or.inl h'
        · right; omega
    · rw [pa_succ]
      split_ifs with h
      · have := hR x h; omega
      · exact hC x (by omega)
    · rw [rt_succ]
      split_ifs with h
      · rw [pa_succ, if_neg]
        · exact hC _ (by simp)
        · intro h'; have := hR _ h'; simp at this
      · rw [pa_succ, if_neg h]; exact hD i

lemma rt_gt (s : ℕ) (hs : s ≤ m) (i : Fin (m + 1)) : m - s < (rt ea eb s i).val :=
  ((inv ea eb s hs).1 i).2

lemma rt_ne_zero (s : ℕ) (hs : s ≤ m) (i : Fin (m + 1)) : rt ea eb s i ≠ 0 := by
  intro h; have := rt_gt ea eb s hs i; rw [h] at this; simp at this

lemma pa_zero_zero (s : ℕ) (hs : s ≤ m) : pa ea eb s 0 = 0 :=
  (inv ea eb s hs).2.2.1 0 (by simp)

lemma mnode_ne_zero {s : ℕ} (hs : s < m) : mnode m s ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp at this; omega

lemma R12_gt {s : ℕ} (hs : s ≤ m) {x : Fin (2 * m + 1 + 1)} (h : R12 ea eb s x) : m - s < x.val := by
  rcases h with h | h <;> rw [h] <;> exact rt_gt ea eb s hs _

/-- Parents, once set, are never changed. -/
lemma pa_succ_of_ne {s : ℕ} (hs : s < m) {x : Fin (2 * m + 1 + 1)} (hx : pa ea eb s x ≠ 0) :
    pa ea eb (s + 1) x = pa ea eb s x := by
  rw [pa_succ, if_neg]
  rintro (h | h) <;> rw [h] at hx <;> exact hx ((inv ea eb s hs.le).2.2.2 _)

lemma pa_mono {s s' : ℕ} (hss : s ≤ s') (hs' : s' ≤ m) {x : Fin (2 * m + 1 + 1)} (hx : pa ea eb s x ≠ 0) :
    pa ea eb s' x = pa ea eb s x := by
  induction s', hss using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have e := ih (by omega)
    rw [pa_succ_of_ne ea eb (by omega) (by rw [e]; exact hx), e]

lemma pa_iter_mono {s s' : ℕ} (hss : s ≤ s') (hs' : s' ≤ m) (k : ℕ) {x : Fin (2 * m + 1 + 1)}
    (hx : (pa ea eb s)^[k] x ≠ 0) : (pa ea eb s')^[k] x = (pa ea eb s)^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply'] at hx ⊢
    have hk : (pa ea eb s)^[k] x ≠ 0 := by
      intro h; rw [h, pa_zero_zero ea eb s (by omega)] at hx; exact hx rfl
    rw [ih hk, pa_mono ea eb hss hs' hx, Function.iterate_succ_apply']

/-- Every terminal reaches its current root by following parents. -/
theorem rt_reach (s : ℕ) (hs : s ≤ m) (i : Fin (m + 1)) : ∃ k, (pa ea eb s)^[k] (tnode i) = rt ea eb s i := by
  induction s with
  | zero => exact ⟨0, rfl⟩
  | succ s ih =>
    obtain ⟨k, hk⟩ := ih (by omega)
    have hk' : (pa ea eb (s + 1))^[k] (tnode i) = rt ea eb s i := by
      rw [pa_iter_mono ea eb (Nat.le_succ s) hs k (by rw [hk]; exact rt_ne_zero ea eb s (by omega) i), hk]
    rw [rt_succ]
    split_ifs with h
    · refine ⟨k + 1, ?_⟩
      rw [Function.iterate_succ_apply', hk', pa_succ, if_pos h]
    · exact ⟨k, hk'⟩

/-- Merged terminals stay merged. -/
lemma rt_succ_eq {s : ℕ} {i i' : Fin (m + 1)} (h : rt ea eb s i = rt ea eb s i') :
    rt ea eb (s + 1) i = rt ea eb (s + 1) i' := by
  rw [rt_succ, rt_succ, h]

lemma rt_mono_eq {s s' : ℕ} (hss : s ≤ s') {i i' : Fin (m + 1)} (h : rt ea eb s i = rt ea eb s i') :
    rt ea eb s' i = rt ea eb s' i' := by
  induction s', hss using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact rt_succ_eq ea eb ih

/-- After step `j`, the endpoints of edge `j` are merged. -/
lemma rt_edge {j s : ℕ} (hjs : j < s) : rt ea eb s (ext ea j) = rt ea eb s (ext eb j) := by
  refine rt_mono_eq ea eb hjs ?_
  rw [rt_succ, rt_succ, if_pos (show R12 ea eb j _ from Or.inl rfl),
    if_pos (show R12 ea eb j _ from Or.inr rfl)]

/-- Equal roots imply connectivity along the edges processed so far. -/
theorem rt_eq_reach (Gr : SimpleGraph (Fin (m + 1))) (s : ℕ) (hs : s ≤ m)
    (hG : ∀ j < s, Gr.Reachable (ext ea j) (ext eb j)) {i i' : Fin (m + 1)}
    (h : rt ea eb s i = rt ea eb s i') : Gr.Reachable i i' := by
  induction s generalizing i i' with
  | zero => rw [rt_zero, rt_zero] at h; rw [tnode_inj h]
  | succ s ih =>
    have ih' := fun {i i'} => ih (by omega) (fun j hj => hG j (by omega)) (i := i) (i' := i')
    have hgt := fun x => rt_gt ea eb s (by omega) x
    have hw : ∀ x, R12 ea eb s (rt ea eb s x) → Gr.Reachable x (ext ea s) := by
      rintro x (hx | hx)
      · exact ih' hx
      · exact (ih' hx).trans (hG s (by omega)).symm
    rw [rt_succ, rt_succ] at h
    split_ifs at h with h1 h2 h2
    · exact (hw i h1).trans (hw i' h2).symm
    · have := congrArg Fin.val h; have := hgt i'; simp at *; omega
    · have := congrArg Fin.val h; have := hgt i; simp at *; omega
    · exact ih' h

/-- The children of the node created at step `j` are among the two roots joined at step `j`. -/
theorem pa_child (s : ℕ) (hs : s ≤ m) (x : Fin (2 * m + 1 + 1)) (j : ℕ) (hj : j < s)
    (h : pa ea eb s x = mnode m j) : R12 ea eb j x := by
  induction s with
  | zero => omega
  | succ s ih =>
    rw [pa_succ] at h
    split_ifs at h with h1
    · have := congrArg Fin.val h; simp at this
      have : j = s := by omega
      subst this; exact h1
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · exact ih (by omega) hj h
      · subst hj
        rcases (inv ea eb j (by omega)).2.1 x with h' | h' <;> rw [h] at h'
        · exact absurd h' (mnode_ne_zero (by omega))
        · simp at h'

/-- The node created at step `j` has the root `rt j (ea j)` as a child. -/
theorem par_child (j : ℕ) (hj : j < m) : par ea eb (rt ea eb j (ext ea j)) = mnode m j := by
  have h1 : pa ea eb (j + 1) (rt ea eb j (ext ea j)) = mnode m j := by
    rw [pa_succ, if_pos (show R12 ea eb j _ from Or.inl rfl)]
  unfold par
  rw [pa_mono ea eb (Nat.succ_le_of_lt hj) le_rfl (by rw [h1]; exact mnode_ne_zero hj), h1]

lemma par_lt (x : Fin (2 * m + 1 + 1)) (hx : x ≠ 0) : par ea eb x < x := by
  rcases (inv ea eb m le_rfl).2.1 x with h | h
  · unfold par; rw [h]; exact Fin.pos_iff_ne_zero.mpr hx
  · exact h.2.2

lemma par_val_le (x : Fin (2 * m + 1 + 1)) : (par ea eb x).val ≤ m := by
  rcases (inv ea eb m le_rfl).2.1 x with h | h
  · unfold par; rw [h]; simp
  · exact h.2.1

lemma rt_cases (s : ℕ) (hs : s ≤ m) (i : Fin (m + 1)) :
    rt ea eb s i = tnode i ∨ ∃ j < s, rt ea eb s i = mnode m j := by
  rcases ((inv ea eb s hs).1 i).1 with h | h
  · exact Or.inl h
  · right
    have := rt_gt ea eb s hs i
    refine ⟨m - (rt ea eb s i).val, by omega, Fin.ext ?_⟩
    simp; omega

end Merge

end MTSPGT

end ASM0

section ASM1
-- from Solutions.GT.Exchange

/-!
# Maximum spanning trees, merge orders, and the exchange argument

`IsMSTOrder g ea eb`: the pairs `(ea j, eb j)`, `j : Fin m`, are the `m` distinct edges of a spanning tree `R` of
the complete graph on `Fin (m+1)` which has maximum total weight `∑ g` among all spanning trees, listed with
non-increasing `g`. Existence is `exists_isMSTOrder`.

Main fact (`exists_common`): two terminals `a ≠ b` have a common ancestor in the merge tree, created at a step `j`
whose edge has `g(e_j) ≥ g(a, b)` (the maximum spanning tree property, via the exchange argument).
-/

open scoped Classical

namespace MTSPGT
open SimpleGraph

section Exch
variable {m : ℕ} (ea eb : Fin m → Fin (m + 1))

/-- The spanning tree `R` given by the edge list. -/
def edgeGraph : SimpleGraph (Fin (m + 1)) := fromEdgeSet (Set.range fun j => s(ea j, eb j))

/-- **Maximum spanning tree with a non-increasing edge order.** -/
structure IsMSTOrder (g : Sym2 (Fin (m + 1)) → ℝ) (ea eb : Fin m → Fin (m + 1)) : Prop where
  ne : ∀ j, ea j ≠ eb j
  inj : Function.Injective (fun j => s(ea j, eb j))
  tree : (edgeGraph ea eb).IsTree
  max : ∀ T : SimpleGraph (Fin (m + 1)), T.IsTree → ∑ e ∈ T.edgeFinset, g e ≤ ∑ j, g s(ea j, eb j)
  anti : ∀ i j : Fin m, i ≤ j → g s(ea j, eb j) ≤ g s(ea i, eb i)

lemma eq_of_reach {V β : Type*} {G : SimpleGraph V} (f : V → β) (h : ∀ u v, G.Adj u v → f u = f v) {a b : V}
    (hr : G.Reachable a b) : f a = f b := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons ha _ ih => exact (h _ _ ha).trans ih

lemma reach_of_reach {V : Type*} {G G' : SimpleGraph V} (h : ∀ u v, G.Adj u v → G'.Reachable u v) {a b : V}
    (hr : G.Reachable a b) : G'.Reachable a b := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons ha _ ih => exact (h _ _ ha).trans ih

lemma rt_final {g : Sym2 (Fin (m + 1)) → ℝ} (hM : IsMSTOrder g ea eb) (a b : Fin (m + 1)) :
    rt ea eb m a = rt ea eb m b := by
  refine eq_of_reach (G := edgeGraph ea eb) (rt ea eb m) ?_ (hM.tree.connected.preconnected a b)
  intro u v huv
  simp only [edgeGraph, fromEdgeSet_adj, Set.mem_range] at huv
  obtain ⟨⟨j, hj⟩, -⟩ := huv
  have e := rt_edge ea eb (s := m) j.isLt
  rw [ext_fin, ext_fin] at e
  rcases Sym2.eq_iff.mp hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact e
  · exact e.symm

/-- **The exchange argument.** -/
theorem exchange {g : Sym2 (Fin (m + 1)) → ℝ} (hM : IsMSTOrder g ea eb) (j : ℕ) (hj : j < m)
    {a b : Fin (m + 1)} (hab : a ≠ b) (hne : rt ea eb j a ≠ rt ea eb j b)
    (ha : R12 ea eb j (rt ea eb j a)) (hb : R12 ea eb j (rt ea eb j b)) :
    g s(a, b) ≤ g s(ext ea j, ext eb j) := by
  set jj : Fin m := ⟨j, hj⟩ with hjj
  have hea : ext ea j = ea jj := ext_fin ea jj
  have heb : ext eb j = eb jj := ext_fin eb jj
  rw [hea, heb]
  by_cases hin : ∃ j', s(ea j', eb j') = s(a, b)
  · obtain ⟨j', hj'⟩ := hin
    rw [← hj']
    by_cases hlt : j'.val < j
    · exfalso
      have e := rt_edge ea eb (s := j) hlt
      rw [ext_fin, ext_fin] at e
      rcases Sym2.eq_iff.mp hj' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at e; exact hne e
      · rw [h1, h2] at e; exact hne e.symm
    · exact hM.anti jj j' (by rw [Fin.le_def]; simp [jj]; omega)
  · push Not at hin
    set E : Fin m → Sym2 (Fin (m + 1)) := fun j => s(ea j, eb j) with hE
    set F : Finset (Sym2 (Fin (m + 1))) := ((Finset.univ.image E).erase (E jj)) ∪ {s(a, b)} with hF
    set R' : SimpleGraph (Fin (m + 1)) := fromEdgeSet (↑F) with hR'
    have hEd : ∀ j, ¬ (E j).IsDiag := fun j => by simpa [E] using hM.ne j
    have habd : ¬ (s(a, b)).IsDiag := by simpa using hab
    have hedge : R'.edgeSet = ↑F := by
      rw [hR', edgeSet_fromEdgeSet]
      ext e
      simp only [Set.mem_sdiff, Finset.mem_coe, and_iff_left_iff_imp]
      intro he
      simp only [hF, Finset.mem_union, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_singleton] at he
      rcases he with ⟨-, j, rfl⟩ | rfl
      · exact hEd j
      · exact habd
    have hnotin : s(a, b) ∉ (Finset.univ.image E).erase (E jj) := by
      simp only [Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and, not_and, not_exists]
      exact fun _ j => hin j
    have hcard : F.card = m := by
      rw [hF, Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hnotin),
        Finset.card_erase_of_mem (by simp), Finset.card_image_of_injective _ hM.inj]
      simp; omega
    have hadjR' : ∀ j', j' ≠ jj → R'.Adj (ea j') (eb j') := by
      intro j' hj'
      rw [hR', fromEdgeSet_adj]
      refine ⟨?_, hM.ne j'⟩
      simp only [hF, Finset.coe_union, Finset.coe_erase, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Finset.coe_singleton, Set.mem_union, Set.mem_sdiff, Set.mem_range, Set.mem_singleton_iff]
      exact Or.inl ⟨⟨j', rfl⟩, fun h => hj' (hM.inj h)⟩
    have hadjab : R'.Adj a b := by
      rw [hR', fromEdgeSet_adj]
      exact ⟨by simp [hF], hab⟩
    have hpre : ∀ j' < j, R'.Reachable (ext ea j') (ext eb j') := by
      intro j' hj'
      have h1 := ext_fin ea ⟨j', by omega⟩
      have h2 := ext_fin eb ⟨j', by omega⟩
      rw [h1, h2]
      exact (hadjR' _ (by intro h; rw [Fin.ext_iff] at h; simp [jj] at h; omega)).reachable
    have hreach := fun {i i'} => rt_eq_reach ea eb R' j hj.le hpre (i := i) (i' := i')
    have hpq : R'.Reachable (ea jj) (eb jj) := by
      rw [← hea, ← heb]
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hne
      · exact (hreach ha).symm.trans (hadjab.reachable.trans (hreach hb))
      · exact (hreach hb).symm.trans (hadjab.symm.reachable.trans (hreach ha))
      · exact absurd (ha.trans hb.symm) hne
    have hconn : R'.Connected := by
      refine ⟨fun u v => reach_of_reach ?_ (hM.tree.connected.preconnected u v)⟩
      intro u v huv
      simp only [edgeGraph, fromEdgeSet_adj, Set.mem_range] at huv
      obtain ⟨⟨j', hj'⟩, -⟩ := huv
      have : R'.Reachable (ea j') (eb j') := by
        by_cases h : j' = jj
        · rw [h]; exact hpq
        · exact (hadjR' j' h).reachable
      rcases Sym2.eq_iff.mp hj' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact this
      · exact this.symm
    have htree : R'.IsTree := by
      rw [isTree_iff_connected_and_card]
      refine ⟨hconn, ?_⟩
      rw [hedge, Nat.card_coe_set_eq, Set.ncard_coe_finset, hcard]
      simp
    have hmax := hM.max R' htree
    replace hmax : ∑ e ∈ F, g e ≤ ∑ j, g s(ea j, eb j) := by
      convert hmax using 2
      ext e; simp only [edgeFinset, Set.mem_toFinset, hedge, Finset.mem_coe]
    rw [hF, Finset.sum_union (Finset.disjoint_singleton_right.mpr hnotin),
      Finset.sum_erase_eq_sub (by simp), Finset.sum_image (fun x _ y _ h => hM.inj h)] at hmax
    simp only [Finset.sum_singleton] at hmax
    change _ ≤ ∑ j, g (E j) at hmax
    have : g (E jj) = g s(ea jj, eb jj) := rfl
    linarith

/-- **Common ancestor.** Two distinct terminals have a common ancestor, created at a step `j` whose edge
`e_j` satisfies `g(a, b) ≤ g(e_j)`. -/
theorem exists_common {g : Sym2 (Fin (m + 1)) → ℝ} (hM : IsMSTOrder g ea eb) {a b : Fin (m + 1)} (hab : a ≠ b) :
    ∃ j < m, (∃ k, (par ea eb)^[k] (tnode a) = mnode m j) ∧ (∃ k, (par ea eb)^[k] (tnode b) = mnode m j) ∧
      g s(a, b) ≤ g s(ext ea j, ext eb j) := by
  have hex : ∃ s, rt ea eb s a = rt ea eb s b := ⟨m, rt_final ea eb hM a b⟩
  set s0 := Nat.find hex with hs0
  have hP : rt ea eb s0 a = rt ea eb s0 b := Nat.find_spec hex
  have hle : s0 ≤ m := Nat.find_min' hex (rt_final ea eb hM a b)
  have hpos : s0 ≠ 0 := by
    intro h; rw [h, rt_zero, rt_zero] at hP; exact hab (tnode_inj hP)
  obtain ⟨j, hj⟩ : ∃ j, s0 = j + 1 := ⟨s0 - 1, by omega⟩
  have hne : rt ea eb j a ≠ rt ea eb j b := Nat.find_min hex (by omega)
  rw [hj] at hP hle
  have hgt := fun x => rt_gt ea eb j (by omega) x
  rw [rt_succ, rt_succ] at hP
  have key : R12 ea eb j (rt ea eb j a) ∧ R12 ea eb j (rt ea eb j b) := by
    split_ifs at hP with h1 h2 h2
    · exact ⟨h1, h2⟩
    · have := congrArg Fin.val hP; have := hgt b; simp at *; omega
    · have := congrArg Fin.val hP; have := hgt a; simp at *; omega
    · exact absurd hP hne
  have hra : rt ea eb (j + 1) a = mnode m j := by rw [rt_succ, if_pos key.1]
  have hrb : rt ea eb (j + 1) b = mnode m j := by rw [rt_succ, if_pos key.2]
  refine ⟨j, by omega, ?_, ?_, exchange ea eb hM j (by omega) hab hne key.1 key.2⟩
  · obtain ⟨k, hk⟩ := rt_reach ea eb (j + 1) hle a
    refine ⟨k, ?_⟩
    unfold par
    rw [pa_iter_mono ea eb hle le_rfl k (by rw [hk, hra]; exact mnode_ne_zero (by omega)), hk, hra]
  · obtain ⟨k, hk⟩ := rt_reach ea eb (j + 1) hle b
    refine ⟨k, ?_⟩
    unfold par
    rw [pa_iter_mono ea eb hle le_rfl k (by rw [hk, hrb]; exact mnode_ne_zero (by omega)), hk, hrb]

end Exch

end MTSPGT

end ASM1

section ASM2
-- from Solutions.GT.MST

/-!
# Existence of a maximum spanning tree with a sorted edge list; the forest bound

* `exists_isMSTOrder`: for every `g`, a maximum spanning tree of the complete graph on `Fin (m+1)` exists
  (`Finset.exists_max_image` over all spanning trees), and its edges can be listed with non-increasing `g`
  (`List.mergeSort`).
* `forest_bound`: a nonempty set `F` of vertices contains at most `|F| - 1` edges of the tree `R`.
-/

open scoped Classical

namespace MTSPGT
open SimpleGraph

/-- A maximum spanning tree with a non-increasing edge list exists. -/
theorem exists_isMSTOrder {m : ℕ} (g : Sym2 (Fin (m + 1)) → ℝ) :
    ∃ ea eb : Fin m → Fin (m + 1), IsMSTOrder g ea eb := by
  set trees : Finset (SimpleGraph (Fin (m + 1))) := Finset.univ.filter (fun T => T.IsTree) with htrees
  have hne : trees.Nonempty := by
    obtain ⟨T, -, hT⟩ := (connected_top (V := Fin (m + 1))).exists_isTree_le
    exact ⟨T, by simp [htrees, hT]⟩
  obtain ⟨T0, hT0m, hT0max⟩ := Finset.exists_max_image trees (fun T => ∑ e ∈ T.edgeFinset, g e) hne
  have hT0 : T0.IsTree := by simpa [htrees] using hT0m
  set L := T0.edgeFinset.toList.mergeSort (fun e f => decide (g f ≤ g e)) with hL
  have hlen : L.length = m := by
    have := hT0.card_edgeFinset
    simp only [Fintype.card_fin] at this
    rw [hL, List.length_mergeSort, Finset.length_toList]; omega
  have hperm : L.Perm T0.edgeFinset.toList := List.mergeSort_perm _ _
  have hnodup : L.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList _)
  have hsorted : L.Pairwise (fun e f => decide (g f ≤ g e)) :=
    List.pairwise_mergeSort (fun a b c h1 h2 => by simp at *; linarith)
      (fun a b => by simp; exact le_total _ _) _
  set E : Fin m → Sym2 (Fin (m + 1)) := fun j => L.get ⟨j.val, by omega⟩ with hE
  have hEmem : ∀ e, e ∈ Set.range E ↔ e ∈ T0.edgeFinset := by
    intro e
    rw [← Finset.mem_toList, ← hperm.mem_iff, List.mem_iff_get]
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨⟨i.val, by omega⟩, rfl⟩
  have hEinj : Function.Injective E := by
    intro i j h
    have := (List.Nodup.get_inj_iff hnodup).mp h
    simp only [Fin.mk.injEq] at this
    exact Fin.ext this
  have hout : ∀ j, s((E j).out.1, (E j).out.2) = E j := fun j => Quot.out_eq _
  refine ⟨fun j => (E j).out.1, fun j => (E j).out.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro j h
    have hm : E j ∈ T0.edgeFinset := (hEmem _).mp ⟨j, rfl⟩
    rw [mem_edgeFinset] at hm
    have := T0.not_isDiag_of_mem_edgeSet hm
    rw [← hout j] at this
    exact this (by simp [h])
  · intro i j h; simp only [hout] at h; exact hEinj h
  · have : edgeGraph (fun j => (E j).out.1) (fun j => (E j).out.2) = T0 := by
      ext u v
      simp only [edgeGraph, hout, fromEdgeSet_adj]
      rw [hEmem, mem_edgeFinset, mem_edgeSet]
      exact ⟨fun h => h.1, fun h => ⟨h, h.ne⟩⟩
    rw [this]; exact hT0
  · intro T hT
    simp only [hout]
    have h1 := hT0max T (by simp [htrees, hT])
    have h2 : ∑ e ∈ T0.edgeFinset, g e = ∑ j, g (E j) := by
      rw [← Finset.sum_image (fun x _ y _ h => hEinj h)]
      congr 1
      ext e; rw [← hEmem]; simp
    exact h1.trans h2.le
  · intro i j hij
    simp only [hout]
    rcases hij.lt_or_eq with h | h
    · have := List.pairwise_iff_get.mp hsorted ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ (by simpa using h)
      simpa [E] using this
    · rw [h]

/-- **Forest bound.** -/
theorem forest_bound {m : ℕ} {g : Sym2 (Fin (m + 1)) → ℝ} {ea eb : Fin m → Fin (m + 1)}
    (hM : IsMSTOrder g ea eb) (F : Finset (Fin (m + 1))) (hF : F.Nonempty) :
    (Finset.univ.filter (fun j => ea j ∈ F ∧ eb j ∈ F)).card + 1 ≤ F.card := by
  obtain ⟨x0, hx0⟩ := hF
  set H := (edgeGraph ea eb).induce (F : Set (Fin (m + 1))) with hH
  have hHa : H.IsAcyclic := hM.tree.isAcyclic.induce _
  have : Nonempty (F : Set (Fin (m + 1))) := ⟨⟨x0, hx0⟩⟩
  obtain ⟨T, hHT, -, hT⟩ := (connected_top (V := (F : Set (Fin (m + 1))))).exists_isTree_le_of_le_of_isAcyclic
    le_top hHa
  have hcT := hT.card_edgeFinset
  have hcard : Fintype.card (F : Set (Fin (m + 1))) = F.card := by simp
  rw [hcard] at hcT
  rw [← hcT, add_le_add_iff_right]
  let f : Fin m → Sym2 (F : Set (Fin (m + 1))) := fun j =>
    if h : ea j ∈ F ∧ eb j ∈ F then s(⟨ea j, h.1⟩, ⟨eb j, h.2⟩) else s(⟨x0, hx0⟩, ⟨x0, hx0⟩)
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj
    simp only [f, dif_pos hj]
    rw [Finset.mem_coe, mem_edgeFinset, mem_edgeSet]
    apply hHT
    simp only [hH, comap_adj, Function.Embedding.subtype_apply, edgeGraph, fromEdgeSet_adj]
    exact ⟨⟨j, rfl⟩, hM.ne j⟩
  · intro i hi j hj h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
    simp only [f, dif_pos hi, dif_pos hj] at h
    have := congrArg (Sym2.map Subtype.val) h
    simp only [Sym2.map_mk] at this
    exact hM.inj this

end MTSPGT

end ASM2

section ASM3
-- from Solutions.GL.Tree

/-!
# Generic lemmas on trees and weighted trees (for the gluing claim 6.1)
-/

open scoped Classical

namespace MTSPGL
open SimpleGraph

section TreeLem
variable {V : Type*} {G : SimpleGraph V}
lemma reach_or_reach_aux {a b : V} : ∀ (w t : V), G.Walk w t → t = a →
    (G.deleteEdges {s(a, b)}).Reachable w a ∨ (G.deleteEdges {s(a, b)}).Reachable w b := by
  intro w t p
  induction p with
  | nil => intro h; subst h; exact Or.inl (Reachable.refl _)
  | @cons u u' _ h p ih =>
    intro ht
    have ih := ih ht
    by_cases he : s(u, u') = s(a, b)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (Reachable.refl _)
      · exact Or.inr (Reachable.refl _)
    · have hadj : (G.deleteEdges {s(a, b)}).Adj u u' := by
        rw [deleteEdges_adj]; exact ⟨h, by simpa using he⟩
      rcases ih with h1 | h1
      · exact Or.inl (hadj.reachable.trans h1)
      · exact Or.inr (hadj.reachable.trans h1)

/-- After deleting a tree edge `{a,b}`, every vertex is still connected to `a` or to `b`. -/
lemma reach_or_reach (hconn : G.Connected) {a b : V} (w : V) :
    (G.deleteEdges {s(a, b)}).Reachable w a ∨ (G.deleteEdges {s(a, b)}).Reachable w b := by
  obtain ⟨p⟩ := hconn.preconnected w a
  exact reach_or_reach_aux w a p rfl

lemma not_reach_of_adj (hac : G.IsAcyclic) {a b : V} (hadj : G.Adj a b) :
    ¬ (G.deleteEdges {s(a, b)}).Reachable a b :=
  isAcyclic_iff_forall_adj_isBridge.mp hac hadj

/-- In a tree, an edge lies on the path between `u` and `v` iff deleting it separates them. -/
lemma mem_path_edges_iff (hT : G.IsTree) {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (e : Sym2 V) : e ∈ p.edges ↔ ¬ (G.deleteEdges {e}).Reachable u v := by
  classical
  constructor
  · intro he hR
    obtain ⟨q⟩ := hR
    let q' := q.toPath
    have hq'p : (q'.val.mapLe (G.deleteEdges_le {e})).IsPath := q'.property.mapLe _
    have heq : q'.val.mapLe (G.deleteEdges_le {e}) = p := by
      have := (hT.existsUnique_path u v).unique hq'p hp
      exact this
    rw [← heq, Walk.edges_mapLe_eq_edges] at he
    have := q'.val.edges_subset_edgeSet he
    rw [edgeSet_deleteEdges] at this
    exact this.2 rfl
  · intro hR
    by_contra he
    exact hR ⟨p.toDeleteEdge e he⟩

/-- Reachability classes after deleting an edge of a tree. -/
lemma reach_iff_reach (hT : G.IsTree) {a b : V} (hadj : G.Adj a b) (x p q : V) :
    ((G.deleteEdges {s(a, b)}).Reachable x p ↔ (G.deleteEdges {s(a, b)}).Reachable x q) ↔
      (G.deleteEdges {s(a, b)}).Reachable p q := by
  set R := (G.deleteEdges {s(a, b)}).Reachable with hRdef
  have hab : ¬ R a b := not_reach_of_adj hT.isAcyclic hadj
  have hx := reach_or_reach hT.connected (a := a) (b := b) x
  have hp := reach_or_reach hT.connected (a := a) (b := b) p
  have hq := reach_or_reach hT.connected (a := a) (b := b) q
  constructor
  · intro h
    by_cases hxp : R x p
    · exact hxp.symm.trans (h.mp hxp)
    · have hxq : ¬ R x q := fun hh => hxp (h.mpr hh)
      rcases hx with hx | hx
      · have hpb : R p b := by
          rcases hp with hp | hp
          · exact absurd (hx.trans hp.symm) hxp
          · exact hp
        have hqb : R q b := by
          rcases hq with hq | hq
          · exact absurd (hx.trans hq.symm) hxq
          · exact hq
        exact hpb.trans hqb.symm
      · have hpa : R p a := by
          rcases hp with hp | hp
          · exact hp
          · exact absurd (hx.trans hp.symm) hxp
        have hqa : R q a := by
          rcases hq with hq | hq
          · exact hq
          · exact absurd (hx.trans hq.symm) hxq
        exact hpa.trans hqa.symm
  · intro h
    exact ⟨fun h1 => h1.trans h, fun h1 => h1.trans h.symm⟩

/-- In a finite tree, behind every edge `a → b` (on the side of `b`) there is a vertex of degree
at most one. -/
lemma exists_leaf_behind [Fintype V] [DecidableEq V] (hT : G.IsTree) {a b : V} (hadj : G.Adj a b) :
    ∃ c, (G.deleteEdges {s(a, b)}).Reachable b c ∧ ∀ y₁ y₂, G.Adj c y₁ → G.Adj c y₂ → y₁ = y₂ := by
  classical
  let s : Set ℕ := {k | ∃ (c : V) (q : G.Walk b c), q.IsPath ∧ a ∉ q.support ∧ q.length = k}
  have hfin : s.Finite := Set.Finite.subset (Set.finite_le_nat (Fintype.card V))
    (fun k ⟨_, q, hq, _, hk⟩ => hk ▸ le_of_lt hq.length_lt)
  have hb0 : (0 : ℕ) ∈ s := ⟨b, Walk.nil, Walk.IsPath.nil, by
    simp only [Walk.support_nil, List.mem_singleton]; exact hadj.ne, rfl⟩
  obtain ⟨k, ⟨c, q, hq, haq, hk⟩, hmax⟩ := hfin.exists_maximal ⟨0, hb0⟩
  have hext : ∀ y, G.Adj c y → y ∉ q.support → y ≠ a → False := by
    intro y hcy hy hya
    have hq2 : (q.concat hcy).IsPath := hq.concat hy hcy
    have hmem : (q.concat hcy).length ∈ s := ⟨y, q.concat hcy, hq2, by
      simp only [Walk.support_concat, List.mem_append, List.mem_singleton,
        not_or]
      exact ⟨haq, fun h => hya h.symm⟩, rfl⟩
    have := hmax hmem (by rw [Walk.length_concat, hk]; omega)
    rw [Walk.length_concat, hk] at this
    omega
  have hRq : (G.deleteEdges {s(a, b)}).Reachable b c := by
    refine ⟨q.toDeleteEdge (s(a, b)) ?_⟩
    intro hmem
    exact haq (q.fst_mem_support_of_mem_edges hmem)
  refine ⟨c, hRq, ?_⟩
  -- every neighbour of `c` is a fixed vertex
  have hnb : ∀ y, G.Adj c y → y = (if c = b then a else q.penultimate) := by
    intro y hcy
    by_cases hcb : c = b
    · subst hcb
      rw [if_pos rfl]
      have hqnil : q = Walk.nil := (Walk.isPath_iff_nil.mp hq).eq_nil
      by_contra hya
      apply hext y hcy _ hya
      rw [hqnil, Walk.support_nil, List.mem_singleton]
      exact hcy.ne.symm
    · rw [if_neg hcb]
      by_cases hy : y ∈ q.support
      · exact hT.isAcyclic.eq_penultimate_of_adj_end hq hcy hy
      · by_cases hya : y = a
        · exfalso
          subst hya
          -- two different paths from `y = a` to `c`
          have hP : (Walk.cons hadj q).IsPath := hq.cons haq
          have h1 : (⟨Walk.cons hadj q, hP⟩ : G.Path y c) = Path.singleton hcy.symm :=
            (hT.isAcyclic.subsingleton_path y c).elim _ _
          have hlen := congrArg (fun P : G.Path y c => P.val.length) h1
          simp only [Walk.length_cons, Path.singleton_coe, Walk.length_cons, Walk.length_nil] at hlen
          have : q.length = 0 := by omega
          exact hcb (Walk.eq_of_length_eq_zero this).symm
        · exact absurd (hext y hcy hy hya) id
  intro y₁ y₂ h1 h2
  rw [hnb y₁ h1, hnb y₂ h2]

/-- A walk between distinct vertices starts with an edge. -/
lemma exists_first_edge : ∀ {a b : V} (W : G.Walk a b), a ≠ b → ∃ z, G.Adj a z ∧ s(a, z) ∈ W.edges
  | _, _, .nil, h => absurd rfl h
  | _, _, .cons h _, _ => ⟨_, h, by simp⟩

end TreeLem

namespace WT
open TreeCoverLB

variable {X : Type*} (T : WeightedTree X)

lemma path_isPath (a b : X) : (T.path a b).IsPath :=
  (T.isTree.existsUnique_path a b).exists.choose_spec

lemma mem_path_edges (a b : X) (e : Sym2 X) :
    e ∈ (T.path a b).edges ↔ ¬ (T.G.deleteEdges {e}).Reachable a b :=
  mem_path_edges_iff T.isTree _ (path_isPath T a b) e

/-- The edges of the tree path lie on every walk with the same ends. -/
lemma path_edges_subset {a b : X} (W : T.G.Walk a b) {e : Sym2 X} (he : e ∈ (T.path a b).edges) :
    e ∈ W.edges := by
  by_contra h
  exact (mem_path_edges T a b e).mp he ⟨W.toDeleteEdge e h⟩

lemma dist_eq_sum [Fintype X] (a b : X) :
    T.dist a b = ∑ e ∈ T.G.edgeFinset, if e ∈ (T.path a b).edges then T.w e else 0 := by
  have hp := path_isPath T a b
  have h1 : T.dist a b = ((T.path a b).edges.map T.w).sum := by
    unfold TreeCoverLB.WeightedTree.dist KServer.walkWeight
    rw [Walk.edges, List.map_map]
    rfl
  rw [h1, ← List.sum_toFinset _ hp.isTrail.edges_nodup, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e
  simp only [List.mem_toFinset, Finset.mem_filter, mem_edgeFinset]
  exact ⟨fun h => ⟨(T.path a b).edges_subset_edgeSet h, h⟩, fun h => h.2⟩

lemma dist_comm [Fintype X] (a b : X) : T.dist a b = T.dist b a := by
  rw [dist_eq_sum, dist_eq_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  simp only [mem_path_edges, reachable_comm]

lemma dist_self [Fintype X] (a : X) : T.dist a a = 0 := by
  rw [dist_eq_sum]
  refine Finset.sum_eq_zero (fun e _ => ?_)
  rw [if_neg]
  rw [mem_path_edges]
  exact fun h => h (Reachable.refl _)

/-- Separation by the side of a tree edge = the edge lies on the path. -/
lemma sep_iff (r a b : X) {f : Sym2 X} (hf : f ∈ T.G.edgeSet) :
    ¬ ((¬ (T.G.deleteEdges {f}).Reachable r a) ↔ (¬ (T.G.deleteEdges {f}).Reachable r b)) ↔
      f ∈ (T.path a b).edges := by
  rw [mem_path_edges]
  induction f with
  | _ x y =>
    have := reach_iff_reach T.isTree (show T.G.Adj x y from hf) r a b
    tauto

/-- Each side of a tree edge (the side away from `r`) contains a leaf. -/
lemma exists_leaf_side [Fintype X] (r : X) {f : Sym2 X} (hf : f ∈ T.G.edgeSet) :
    ∃ c, (∀ y₁ y₂, T.G.Adj c y₁ → T.G.Adj c y₂ → y₁ = y₂) ∧
      ¬ (T.G.deleteEdges {f}).Reachable r c := by
  induction f with
  | _ a' b' =>
    have hadj : T.G.Adj a' b' := hf
    have key : ∀ a b : X, T.G.Adj a b → s(a, b) = s(a', b') →
        (T.G.deleteEdges {s(a, b)}).Reachable r a → ∃ c, (∀ y₁ y₂, T.G.Adj c y₁ → T.G.Adj c y₂ → y₁ = y₂) ∧
          ¬ (T.G.deleteEdges {s(a', b')}).Reachable r c := by
      intro a b hab heq hra
      obtain ⟨c, hbc, hleaf⟩ := exists_leaf_behind T.isTree hab
      refine ⟨c, hleaf, fun hrc => ?_⟩
      rw [← heq] at hrc
      exact not_reach_of_adj T.isTree.isAcyclic hab (hra.symm.trans (hrc.trans hbc.symm))
    rcases reach_or_reach T.isTree.connected (a := a') (b := b') r with h | h
    · exact key a' b' hadj rfl h
    · exact key b' a' hadj.symm Sym2.eq_swap (by rw [Sym2.eq_swap]; exact h)

end WT

end MTSPGL

end ASM3

section ASM4
-- from Solutions.CC.CellTree

/-!
# The local tree of a contracted cell (Azarmehr–Behnezhad, §7.1, Claim 7.1)

Encoding. The tree lives on `Fin (N+1)`. Node `0` is the common root `o_P`; every node `x ≠ 0` is the
lower endpoint of the segment `x`, which is the edge `{x, par x}` (`par x < x`, so the segment forest is
acyclic; `par x = 0` means the segment hangs at `o_P`). Segment `x` has weight `σ (1 - y x)`.
A vertex `v` of the cell is identified with the lower endpoint `att v` of the segment directly above it
(`att v = 0`: `v` sits at `o_P`), i.e. the zero-weight attachment edges are contracted; all ports are
identified with the root `o_P` (zero-weight attachment contracted). `path v = anc (att v)` is the list of
segments from `att v` up to the root.
-/

open scoped Classical

namespace MTSPCC
open SimpleGraph TreeCoverLB

/-! ## Part 0: the domination lemma (copied from `Sol_claim_7_1_domination`, any point type) -/

lemma card_le_of_bound {m : ℕ} (S : Finset (Fin m)) (k : ℕ) (h : ∀ i ∈ S, (i : ℕ) ≤ k) :
    S.card ≤ k + 1 := by
  have : S.map Fin.valEmbedding ⊆ Finset.range (k + 1) := by
    intro x hx
    simp only [Finset.mem_map, Fin.valEmbedding_apply] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (h i hi))
  simpa using Finset.card_le_card this

lemma sum_eq {Seg : Type*} (y : Seg → ℝ) (hy : ∀ e, y e = 0 ∨ y e = 1 / 2 ∨ y e = 1) (L : List Seg) :
    (L.map (fun e => 1 - y e)).sum =
      ((Finset.univ.filter (fun i : Fin L.length => y (L.get i) = 0)).card : ℝ) +
        ((Finset.univ.filter (fun i : Fin L.length => y (L.get i) = 1 / 2)).card : ℝ) / 2 := by
  have h1 : (L.map (fun e => 1 - y e)).sum = ∑ i : Fin L.length, (1 - y (L.get i)) := by
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_get
    · simp
    · intro k h1 h2; simp
  rw [h1]
  have h2 : ∀ i : Fin L.length, 1 - y (L.get i) =
      (if y (L.get i) = 0 then (1 : ℝ) else 0) + (if y (L.get i) = 1 / 2 then (1 : ℝ) / 2 else 0) := by
    intro i
    rcases hy (L.get i) with h | h | h <;> rw [h] <;> norm_num
  rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite]
  simp [Finset.sum_const, div_eq_mul_inv]

/-- Claim 7.1, domination across fragments (proof copied from `Solutions/Sol_claim_7_1_domination.lean`,
with the point type generalized from `Fin n` to any type `V`). -/
theorem domination {V : Type*} (d : V → V → ℝ) {ι Seg : Type*} (σ : ℝ) (hσ : 0 < σ)
    (frag : V → ι) (path : V → List Seg) (y : Seg → ℝ)
    (hsymm : ∀ u v, d u v = d v u) (hy : ∀ e, y e = 0 ∨ y e = 1 / 2 ∨ y e = 1)
    (hcover : ∀ u v, frag u ≠ frag v → ∀ (i : Fin (path u).length) (j : Fin (path v).length),
      d u v < ((i : ℝ) + 1 + ((j : ℝ) + 1)) * σ → 1 ≤ y ((path u).get i) + y ((path v).get j))
    (hout : ∀ u v, frag u ≠ frag v → ((path u).length : ℝ) * σ ≤ d u v) :
    ∀ u v, frag u ≠ frag v →
      σ * ((path u).map (fun e => 1 - y e)).sum + σ * ((path v).map (fun e => 1 - y e)).sum ≤ d u v := by
  let Z := fun u => Finset.univ.filter (fun i : Fin (path u).length => y ((path u).get i) = 0)
  let H := fun u => Finset.univ.filter (fun i : Fin (path u).length => y ((path u).get i) = 1 / 2)
  let Le := fun u => Finset.univ.filter (fun i : Fin (path u).length => y ((path u).get i) ≤ 1 / 2)
  have hLe : ∀ u, ((Le u).card : ℝ) = (Z u).card + (H u).card := by
    intro u
    have : Le u = Z u ∪ H u := by
      ext i; simp only [Le, Z, H, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro h; rcases hy ((path u).get i) with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
        · rw [h'] at h; norm_num at h
      · rintro (h | h) <;> rw [h] <;> norm_num
    rw [this, Finset.card_union_of_disjoint]
    · push_cast; ring
    · rw [Finset.disjoint_left]; intro i h1 h2
      simp only [Z, H, Finset.mem_filter] at h1 h2; rw [h1.2] at h2; norm_num at h2
  have hlen : ∀ u (A : Finset (Fin (path u).length)), (A.card : ℝ) ≤ (path u).length := by
    intro u A; exact_mod_cast (Finset.card_le_univ A).trans (by simp)
  have key : ∀ u v, frag u ≠ frag v → σ * (((Z u).card : ℝ) + (Le v).card) ≤ d u v := by
    intro u v huv
    by_cases hZ : (Z u).Nonempty
    · by_cases hL : (Le v).Nonempty
      · set i := (Z u).max' hZ
        set j := (Le v).max' hL
        have hi : y ((path u).get i) = 0 := (Finset.mem_filter.mp ((Z u).max'_mem hZ)).2
        have hj : y ((path v).get j) ≤ 1 / 2 := (Finset.mem_filter.mp ((Le v).max'_mem hL)).2
        have hnot : ¬ d u v < ((i : ℝ) + 1 + ((j : ℝ) + 1)) * σ := by
          intro hlt; have := hcover u v huv i j hlt; linarith
        have hci : ((Z u).card : ℝ) ≤ (i : ℝ) + 1 := by
          exact_mod_cast card_le_of_bound (Z u) i (fun k hk => Fin.le_def.mp ((Z u).le_max' k hk))
        have hcj : ((Le v).card : ℝ) ≤ (j : ℝ) + 1 := by
          exact_mod_cast card_le_of_bound (Le v) j (fun k hk => Fin.le_def.mp ((Le v).le_max' k hk))
        push Not at hnot
        nlinarith
      · rw [Finset.not_nonempty_iff_eq_empty] at hL
        rw [hL, Finset.card_empty]; push_cast
        have := hout u v huv; have := hlen u (Z u); nlinarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hZ
      rw [hZ, Finset.card_empty]; push_cast
      have := hout v u (Ne.symm huv); have := hlen v (Le v); rw [hsymm]; nlinarith
  intro u v huv
  have k1 := key u v huv
  have k2 := key v u (Ne.symm huv)
  rw [← hsymm u v] at k2
  rw [sum_eq y hy (path u), sum_eq y hy (path v)]
  rw [hLe] at k1 k2
  change σ * (((Z u).card : ℝ) + ((H u).card : ℝ) / 2) + σ * (((Z v).card : ℝ) + ((H v).card : ℝ) / 2) ≤ d u v
  nlinarith

/-- Tree distances are nonnegative. -/
lemma dist_nonneg {X : Type*} [Fintype X] (T : WeightedTree X) (a b : X) : 0 ≤ T.dist a b := by
  rw [MTSPGL.WT.dist_eq_sum]
  refine Finset.sum_nonneg (fun e he => ?_)
  split_ifs
  · exact T.w_nonneg e (mem_edgeFinset.mp he)
  · exact le_refl 0

/-! ## Part 1: trees given by a parent function -/

section PTree
variable {N : ℕ} (par : Fin (N + 1) → Fin (N + 1)) (hpar : ∀ x, x ≠ 0 → par x < x)

/-- The graph with edges `{x, par x}`, `x ≠ 0`. -/
def graph : SimpleGraph (Fin (N + 1)) := SimpleGraph.fromRel (fun a b => a ≠ 0 ∧ par a = b)

/-- Edge weights: the edge `{x, par x}` gets `c x`. -/
noncomputable def wt (c : Fin (N + 1) → ℝ) (e : Sym2 (Fin (N + 1))) : ℝ :=
  ∑ x, if x ≠ 0 ∧ s(x, par x) = e then c x else 0

/-- The list of non-root ancestors of `x` (including `x`), from `x` upwards. -/
def anc (par : Fin (N + 1) → Fin (N + 1)) (hpar : ∀ x, x ≠ 0 → par x < x) (x : Fin (N + 1)) :
    List (Fin (N + 1)) :=
  if h : x = 0 then [] else x :: anc par hpar (par x)
termination_by x.val
decreasing_by exact hpar x h

include hpar

lemma anc_zero : anc par hpar 0 = [] := by rw [anc]; simp

lemma anc_of_ne {x : Fin (N + 1)} (hx : x ≠ 0) : anc par hpar x = x :: anc par hpar (par x) := by
  rw [anc, dif_neg hx]

lemma mem_anc {z x : Fin (N + 1)} (h : z ∈ anc par hpar x) : z ≠ 0 ∧ z ≤ x := by
  revert h
  induction x using WellFoundedLT.induction with | _ x ih => ?_
  intro h
  by_cases hx : x = 0
  · rw [hx, anc_zero] at h; simp at h
  · rw [anc_of_ne par hpar hx] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨hx, le_refl _⟩
    · obtain ⟨h1, h2⟩ := ih _ (hpar x hx) h
      exact ⟨h1, h2.trans (hpar x hx).le⟩

lemma anc_nodup (x : Fin (N + 1)) : (anc par hpar x).Nodup := by
  induction x using WellFoundedLT.induction with | _ x ih => ?_
  by_cases hx : x = 0
  · rw [hx, anc_zero]; exact List.nodup_nil
  · rw [anc_of_ne par hpar hx]
    refine List.nodup_cons.mpr ⟨fun h => ?_, ih _ (hpar x hx)⟩
    exact absurd (mem_anc par hpar h).2 (not_le.mpr (hpar x hx))

lemma adj_iff (a b : Fin (N + 1)) :
    (graph par).Adj a b ↔ (a ≠ 0 ∧ par a = b) ∨ (b ≠ 0 ∧ par b = a) := by
  simp only [graph, fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact (lt_irrefl a) (by have := hpar a h1; rwa [h2] at this)

lemma adj_par {x : Fin (N + 1)} (hx : x ≠ 0) : (graph par).Adj x (par x) :=
  (adj_iff par hpar _ _).mpr (Or.inl ⟨hx, rfl⟩)

lemma reach_zero (x : Fin (N + 1)) : (graph par).Reachable x 0 := by
  induction x using WellFoundedLT.induction with | _ x ih => ?_
  by_cases hx : x = 0
  · rw [hx]
  · exact (adj_par par hpar hx).reachable.trans (ih _ (hpar x hx))

lemma s_ne {x z : Fin (N + 1)} (hx : x ≠ 0) (hz : z ≠ 0) (hxz : x ≠ z) :
    s(x, par x) ≠ s(z, par z) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact hxz h1
  · have a := hpar x hx
    have b := hpar z hz
    rw [h2] at a
    rw [← h1] at b
    exact lt_asymm a b

lemma edgeFinset_eq : (graph par).edgeFinset =
    (Finset.univ.filter (fun x : Fin (N + 1) => x ≠ 0)).image (fun x => s(x, par x)) := by
  ext e
  induction e with
  | _ a b =>
    simp only [mem_edgeFinset, mem_edgeSet, adj_iff par hpar, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h1, rfl⟩ | ⟨h1, rfl⟩)
      · exact ⟨a, h1, rfl⟩
      · exact ⟨b, h1, Sym2.eq_swap⟩
    · rintro ⟨x, hx, h⟩
      rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hx, rfl⟩
      · exact Or.inr ⟨hx, rfl⟩

lemma card_edgeSet : Nat.card (graph par).edgeSet = N := by
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, edgeFinset_eq par hpar, Finset.card_image_of_injOn]
  · rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
  · intro x hx z hz h
    by_contra hxz
    exact s_ne par hpar (by simpa using hx) (by simpa using hz) hxz h

lemma isTree : (graph par).IsTree :=
  isTree_iff_connected_and_card.mpr
    ⟨⟨fun a b => (reach_zero par hpar a).trans (reach_zero par hpar b).symm⟩, by
      rw [card_edgeSet par hpar]; simp⟩

/-- The weighted tree with edges `{x, par x}` of weight `c x`. -/
noncomputable def ptree (c : Fin (N + 1) → ℝ) (hc : ∀ x, 0 ≤ c x) : WeightedTree (Fin (N + 1)) where
  G := graph par
  isTree := isTree par hpar
  w := wt par c
  w_nonneg := fun e _ => Finset.sum_nonneg (fun x _ => by
    split_ifs
    · exact hc x
    · exact le_refl 0)

lemma del_adj {x z : Fin (N + 1)} (hx : x ≠ 0) (hz : z ≠ 0) (hxz : x ≠ z) :
    ((graph par).deleteEdges {s(z, par z)}).Adj x (par x) := by
  rw [deleteEdges_adj]
  exact ⟨adj_par par hpar hx, by simpa using s_ne par hpar hx hz hxz⟩

lemma reach_of_not_mem {z : Fin (N + 1)} (hz : z ≠ 0) (x : Fin (N + 1)) (h : z ∉ anc par hpar x) :
    ((graph par).deleteEdges {s(z, par z)}).Reachable x 0 := by
  revert h
  induction x using WellFoundedLT.induction with | _ x ih => ?_
  intro h
  by_cases hx : x = 0
  · rw [hx]
  · rw [anc_of_ne par hpar hx, List.mem_cons, not_or] at h
    exact (del_adj par hpar hx hz (Ne.symm h.1)).reachable.trans (ih _ (hpar x hx) h.2)

lemma reach_of_mem {z : Fin (N + 1)} (hz : z ≠ 0) (x : Fin (N + 1)) (h : z ∈ anc par hpar x) :
    ((graph par).deleteEdges {s(z, par z)}).Reachable x z := by
  revert h
  induction x using WellFoundedLT.induction with | _ x ih => ?_
  intro h
  by_cases hx : x = 0
  · rw [hx, anc_zero] at h; simp at h
  · by_cases hxz : x = z
    · rw [hxz]
    · rw [anc_of_ne par hpar hx, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h.symm hxz
      · exact (del_adj par hpar hx hz hxz).reachable.trans (ih _ (hpar x hx) h)

/-- Deleting the segment `z` separates `x` from the root iff `z` is above `x`. -/
lemma sep {z : Fin (N + 1)} (hz : z ≠ 0) (x : Fin (N + 1)) :
    ¬ ((graph par).deleteEdges {s(z, par z)}).Reachable 0 x ↔ z ∈ anc par hpar x := by
  constructor
  · intro h
    by_contra h'
    exact h (reach_of_not_mem par hpar hz x h').symm
  · intro h hr
    have h1 := reach_of_mem par hpar hz x h
    have h2 : z ∉ anc par hpar (par z) := fun hm =>
      absurd (mem_anc par hpar hm).2 (not_le.mpr (hpar z hz))
    have h3 := reach_of_not_mem par hpar hz (par z) h2
    exact MTSPGL.not_reach_of_adj (isTree par hpar).isAcyclic (adj_par par hpar hz)
      (h1.symm.trans (hr.symm.trans h3.symm))

variable (c : Fin (N + 1) → ℝ) (hc : ∀ x, 0 ≤ c x)

/-- The distance formula: sum of `c z` over segments above exactly one of the two nodes. -/
theorem ptree_dist (a b : Fin (N + 1)) : (ptree par hpar c hc).dist a b =
    ∑ z, if z ≠ 0 ∧ ¬ (z ∈ anc par hpar a ↔ z ∈ anc par hpar b) then c z else 0 := by
  rw [MTSPGL.WT.dist_eq_sum]
  calc _ = ∑ f ∈ (ptree par hpar c hc).G.edgeFinset, ∑ z,
        if f ∈ ((ptree par hpar c hc).path a b).edges then
          (if z ≠ 0 ∧ s(z, par z) = f then c z else 0) else 0 := by
        refine Finset.sum_congr rfl (fun f _ => ?_)
        split_ifs
        · rfl
        · simp
    _ = _ := ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases hz : z = 0
  · simp [hz]
  · rw [Finset.sum_eq_single (s(z, par z))]
    · have hsep := MTSPGL.WT.sep_iff (ptree par hpar c hc) 0 a b (f := s(z, par z)) (adj_par par hpar hz)
      have e1 : ¬ ((ptree par hpar c hc).G.deleteEdges {s(z, par z)}).Reachable 0 a ↔
          z ∈ anc par hpar a := sep par hpar hz a
      have e2 : ¬ ((ptree par hpar c hc).G.deleteEdges {s(z, par z)}).Reachable 0 b ↔
          z ∈ anc par hpar b := sep par hpar hz b
      rw [e1, e2] at hsep
      have hzz : z ≠ 0 ∧ s(z, par z) = s(z, par z) := ⟨hz, rfl⟩
      rw [if_pos hzz]
      by_cases hm : s(z, par z) ∈ ((ptree par hpar c hc).path a b).edges
      · rw [if_pos hm, if_pos ⟨hz, hsep.mpr hm⟩]
      · rw [if_neg hm, if_neg (fun h => hm (hsep.mp h.2))]
    · intro f _ hf
      split_ifs with h1 h2
      · exact absurd h2.2.symm hf
      · rfl
      · rfl
    · intro h
      exact absurd (by rw [mem_edgeFinset]; exact adj_par par hpar hz) h

theorem ptree_dist_symmDiff (a b : Fin (N + 1)) : (ptree par hpar c hc).dist a b =
    ∑ z ∈ symmDiff (anc par hpar a).toFinset (anc par hpar b).toFinset, c z := by
  rw [ptree_dist, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff, List.mem_toFinset]
  have ha := fun h => (mem_anc par hpar (z := z) (x := a) h).1
  have hb := fun h => (mem_anc par hpar (z := z) (x := b) h).1
  tauto

theorem ptree_dist_root (a : Fin (N + 1)) :
    (ptree par hpar c hc).dist a 0 = ((anc par hpar a).map c).sum := by
  rw [ptree_dist_symmDiff, anc_zero, List.toFinset_nil, ← Finset.bot_eq_empty, symmDiff_bot,
    List.sum_toFinset _ (anc_nodup par hpar a)]

theorem ptree_dist_le (a b : Fin (N + 1)) :
    (ptree par hpar c hc).dist a b ≤ ((anc par hpar a).map c).sum + ((anc par hpar b).map c).sum := by
  rw [ptree_dist_symmDiff, ← List.sum_toFinset _ (anc_nodup par hpar a),
    ← List.sum_toFinset _ (anc_nodup par hpar b), ← Finset.sum_union_inter]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg symmDiff_le_sup (fun x _ _ => hc x)) ?_
  have : 0 ≤ ∑ x ∈ (anc par hpar a).toFinset ∩ (anc par hpar b).toFinset, c x :=
    Finset.sum_nonneg (fun x _ => hc x)
  change ∑ x ∈ (anc par hpar a).toFinset ∪ (anc par hpar b).toFinset, c x ≤ _
  linarith

theorem ptree_dist_disjoint (a b : Fin (N + 1)) (hab : ∀ e, e ∈ anc par hpar a → e ∉ anc par hpar b) :
    (ptree par hpar c hc).dist a b = ((anc par hpar a).map c).sum + ((anc par hpar b).map c).sum := by
  have hd : Disjoint (anc par hpar a).toFinset (anc par hpar b).toFinset :=
    Finset.disjoint_left.mpr (fun e h1 h2 => hab e (List.mem_toFinset.mp h1) (List.mem_toFinset.mp h2))
  rw [ptree_dist_symmDiff, hd.symmDiff_eq_sup, ← List.sum_toFinset _ (anc_nodup par hpar a),
    ← List.sum_toFinset _ (anc_nodup par hpar b)]
  exact Finset.sum_union hd

theorem ptree_weight : ∑ e ∈ (ptree par hpar c hc).G.edgeFinset, (ptree par hpar c hc).w e =
    ∑ x ∈ Finset.univ.filter (fun x : Fin (N + 1) => x ≠ 0), c x := by
  rw [Finset.sum_filter]
  change ∑ e ∈ (ptree par hpar c hc).G.edgeFinset, wt par c e = _
  unfold wt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : x = 0
  · simp [hx]
  · have : ∀ e, (x ≠ 0 ∧ s(x, par x) = e) ↔ s(x, par x) = e := fun e => ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
    simp only [this]
    rw [Finset.sum_ite_eq, if_pos, if_pos hx]
    rw [mem_edgeFinset]; exact adj_par par hpar hx

/-- A non-root leaf has no child. -/
lemma ptree_leaf {x : Fin (N + 1)} (hx : x ≠ 0)
    (hleaf : ∀ y₁ y₂, (ptree par hpar c hc).G.Adj x y₁ → (ptree par hpar c hc).G.Adj x y₂ → y₁ = y₂) :
    ∀ z, z ≠ 0 → par z ≠ x := by
  intro z hz hzx
  have h1 : (graph par).Adj x (par x) := adj_par par hpar hx
  have h2 : (graph par).Adj x z := (adj_iff par hpar _ _).mpr (Or.inr ⟨hz, hzx⟩)
  have := hleaf _ _ h1 h2
  have a := hpar x hx
  have b := hpar z hz
  rw [this] at a
  rw [hzx] at b
  exact lt_asymm a b

end PTree

/-! ## Part 2: the local tree of a contracted cell -/

section Cell
variable {N : ℕ} (par : Fin (N + 1) → Fin (N + 1)) (hpar : ∀ x, x ≠ 0 → par x < x)
  (σ : ℝ) (y : Fin (N + 1) → ℝ) (hσ : 0 ≤ σ) (hy1 : ∀ x, y x ≤ 1)

/-- The local tree `t_P`: segment `x` (edge `{x, par x}`) has weight `σ (1 - y x)`. -/
noncomputable def cellTree : WeightedTree (Fin (N + 1)) :=
  ptree par hpar (fun x => σ * (1 - y x)) (fun x => mul_nonneg hσ (by linarith [hy1 x]))

/-- `dist(a, o_P) = σ Σ_{e ∈ path a} (1 - y e)`; ports are `o_P = 0`, so this is `dist (ev u) (ep p)`. -/
theorem cellTree_dist_root (a : Fin (N + 1)) :
    (cellTree par hpar σ y hσ hy1).dist a 0 = σ * ((anc par hpar a).map (fun e => 1 - y e)).sum := by
  rw [cellTree, ptree_dist_root, List.sum_map_mul_left]

theorem cellTree_dist_root' (a : Fin (N + 1)) :
    (cellTree par hpar σ y hσ hy1).dist 0 a = σ * ((anc par hpar a).map (fun e => 1 - y e)).sum := by
  rw [MTSPGL.WT.dist_comm, cellTree_dist_root]

/-- Port–port distances vanish. -/
theorem cellTree_dist_ports : (cellTree par hpar σ y hσ hy1).dist 0 0 = 0 :=
  MTSPGL.WT.dist_self _ _

theorem cellTree_dist_le (a b : Fin (N + 1)) :
    (cellTree par hpar σ y hσ hy1).dist a b ≤
      σ * ((anc par hpar a).map (fun e => 1 - y e)).sum +
        σ * ((anc par hpar b).map (fun e => 1 - y e)).sum := by
  rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
  exact ptree_dist_le par hpar _ _ a b

theorem cellTree_dist_disjoint (a b : Fin (N + 1))
    (hab : ∀ e, e ∈ anc par hpar a → e ∉ anc par hpar b) :
    (cellTree par hpar σ y hσ hy1).dist a b =
      σ * ((anc par hpar a).map (fun e => 1 - y e)).sum +
        σ * ((anc par hpar b).map (fun e => 1 - y e)).sum := by
  rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
  exact ptree_dist_disjoint par hpar _ _ a b hab

/-- Exact distance: `σ Σ (1 - y e)` over the symmetric difference of the two paths. -/
theorem cellTree_dist_symmDiff (a b : Fin (N + 1)) :
    (cellTree par hpar σ y hσ hy1).dist a b =
      σ * ∑ e ∈ symmDiff (anc par hpar a).toFinset (anc par hpar b).toFinset, (1 - y e) := by
  rw [Finset.mul_sum]
  exact ptree_dist_symmDiff par hpar _ _ a b

/-- Weight of `t_P`: `Σ_e σ (1 - y e)` over all segments `e` (= `A_P - τ_P`). -/
theorem cellTree_weight :
    ∑ e ∈ (cellTree par hpar σ y hσ hy1).G.edgeFinset, (cellTree par hpar σ y hσ hy1).w e =
      σ * ∑ x ∈ Finset.univ.filter (fun x : Fin (N + 1) => x ≠ 0), (1 - y x) := by
  rw [Finset.mul_sum]
  exact ptree_weight par hpar _ _

/-- Leaf condition: every leaf of `t_P` is (the image of) a vertex of the cell or a port, provided every
childless segment has a vertex of the cell attached at its lower end, and the cell has a port. -/
theorem cellTree_leaf {n m : ℕ} (inCell : Fin n → Prop) (att : Fin n → Fin (N + 1))
    (isPort : Fin m → Prop)
    (hleafSeg : ∀ x, x ≠ 0 → (∀ z, z ≠ 0 → par z ≠ x) → ∃ v, inCell v ∧ att v = x)
    (hport : ∃ p, isPort p) (c : Fin (N + 1))
    (hc : ∀ y₁ y₂, (cellTree par hpar σ y hσ hy1).G.Adj c y₁ →
      (cellTree par hpar σ y hσ hy1).G.Adj c y₂ → y₁ = y₂) :
    (∃ v, inCell v ∧ att v = c) ∨ (∃ p, isPort p ∧ (fun _ : Fin m => (0 : Fin (N + 1))) p = c) := by
  by_cases h0 : c = 0
  · obtain ⟨p, hp⟩ := hport
    exact Or.inr ⟨p, hp, h0.symm⟩
  · exact Or.inl (hleafSeg c h0 (ptree_leaf par hpar _ _ h0 hc))

/-- **The constraints (9) for `t_P`**, with `ev = att` and `ep = 0` (all ports at `o_P`).
* different fragments: the hypotheses of Claim 7.1 (cover of the conflict graph, outside constraint);
* same fragment: the undiscretized-weight domination `σ |path u Δ path v| ≤ d u v` of `t_F`;
* guard: `σ Σ_{path v} (1 - y) ≤ d_C(q_v, p)` for every port `p`;
* `d_C ≥ 0` on ports. -/
theorem cellTree_h9 {n m : ℕ} (d : Fin n → Fin n → ℝ) (hsymm : ∀ u v, d u v = d v u)
    (hσpos : 0 < σ) (hy : ∀ e, y e = 0 ∨ y e = 1 / 2 ∨ y e = 1)
    (inCell : Fin n → Prop) (att : Fin n → Fin (N + 1)) {ι : Type*} (frag : Fin n → ι)
    (hcover : ∀ u v, inCell u → inCell v → frag u ≠ frag v →
      ∀ (i : Fin (anc par hpar (att u)).length) (j : Fin (anc par hpar (att v)).length),
      d u v < ((i : ℝ) + 1 + ((j : ℝ) + 1)) * σ →
        1 ≤ y ((anc par hpar (att u)).get i) + y ((anc par hpar (att v)).get j))
    (hout : ∀ u v, inCell u → inCell v → frag u ≠ frag v →
      ((anc par hpar (att u)).length : ℝ) * σ ≤ d u v)
    (hsame : ∀ u v, inCell u → inCell v → frag u = frag v →
      σ * ((symmDiff (anc par hpar (att u)).toFinset (anc par hpar (att v)).toFinset).card : ℝ) ≤ d u v)
    (isPort : Fin m → Prop) (dCv : Fin n → Fin m → ℝ) (dC : Fin m → Fin m → ℝ)
    (hguard : ∀ v p, inCell v → isPort p →
      σ * ((anc par hpar (att v)).map (fun e => 1 - y e)).sum ≤ dCv v p)
    (hdC : ∀ p p', isPort p → isPort p' → 0 ≤ dC p p') :
    (∀ u v, inCell u → inCell v → (cellTree par hpar σ y hσ hy1).dist (att u) (att v) ≤ d u v) ∧
    (∀ v p, inCell v → isPort p → (cellTree par hpar σ y hσ hy1).dist (att v) 0 ≤ dCv v p) ∧
    (∀ p p', isPort p → isPort p' → (cellTree par hpar σ y hσ hy1).dist 0 0 ≤ dC p p') := by
  refine ⟨fun u v hu hv => ?_, fun v p hv hp => ?_, fun p p' hp hp' => ?_⟩
  · by_cases hf : frag u = frag v
    · rw [cellTree_dist_symmDiff]
      refine le_trans ?_ (hsame u v hu hv hf)
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun e _ => ?_)) hσ
      rcases hy e with h | h | h <;> rw [h] <;> norm_num
    · refine le_trans (cellTree_dist_le par hpar σ y hσ hy1 _ _) ?_
      exact domination (V := {w : Fin n // inCell w}) (fun a b => d a b) σ hσpos (fun a => frag a)
        (fun a => anc par hpar (att a)) y (fun a b => hsymm a b) hy
        (fun a b hab => hcover a b a.2 b.2 hab) (fun a b hab => hout a b a.2 b.2 hab)
        ⟨u, hu⟩ ⟨v, hv⟩ hf
  · rw [cellTree_dist_root]; exact hguard v p hv hp
  · rw [cellTree_dist_ports]; exact hdC p p' hp hp'

end Cell

end MTSPCC

end ASM4

section ASM5
-- from Solutions.GT.Claim912

/-!
# Claim 9.12 (Azarmehr–Behnezhad, arXiv:2611.04283, p.43–44): the Gromov-product Steiner tree of a dual

Given a dual `y` on cuts and a root `z`:
* loads `ρ(u,v) = ∑_{A : |A ∩ {u,v}| = 1} y_A` (`rho`), depths `h_u = ρ(z,u)` (`hgt`),
  Gromov products `g_uv = (h_u + h_v - ρ(u,v)) / 2` (`gromov`) `= ∑_{A : u, v on the far side of z} y_A`;
* terminals `t : Fin (m+1) → Fin n` (the points of `S \ {z}`), a maximum spanning tree for `g` with its edges
  listed in non-increasing order of `g` (`IsMSTOrder`);
* the tree `ctree`: parent array `par` from the merge process (`Solutions/GT/Merge.lean`), node depths `dep`
  (`0` for the root `z`, `g_{e_j}` for the node of merge `j`, `h_u` for terminal `u`), edge weights
  `wt x = dep x - dep (par x)`, assembled by the generic parent-array builder `MTSPCC.ptree`.

Main results: `gtTree_wt_nonneg`, `gtTree_dist_le` (`d_C(u,v) ≤ ρ(u,v)`), `gtTree_weight_ge`
(`w(C) ≥ ∑_A y_A`), and the existential corollary `claim_9_12`.
-/

open scoped Classical

namespace MTSPGT
open SimpleGraph MetricTSPSublinear

section Loads
variable {n : ℕ} (y : Finset (Fin n) → ℝ) (z : Fin n)

/-- The load `ρ(u, v) = ∑_{A separating u, v} y_A`. -/
noncomputable def rho (u v : Fin n) : ℝ :=
  ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => ¬ ((u ∈ A) ↔ (v ∈ A))), y A

/-- The depth `h_u = ρ(z, u)`. -/
noncomputable def hgt (u : Fin n) : ℝ := rho y z u

/-- The Gromov product `g_uv = (h_u + h_v - ρ(u, v)) / 2`. -/
noncomputable def gromov (u v : Fin n) : ℝ := (hgt y z u + hgt y z v - rho y u v) / 2

/-- `u` lies on the side of the cut `A` not containing `z`. -/
def far (A : Finset (Fin n)) (u : Fin n) : Prop := ¬ ((u ∈ A) ↔ (z ∈ A))

lemma rho_eq (u v : Fin n) : rho y u v = ∑ A, if ¬ ((u ∈ A) ↔ (v ∈ A)) then y A else 0 :=
  Finset.sum_filter _ _

lemma hgt_eq (u : Fin n) : hgt y z u = ∑ A, if far z A u then y A else 0 := by
  rw [hgt, rho_eq]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  by_cases h1 : u ∈ A <;> by_cases h2 : z ∈ A <;> simp [far, h1, h2]

lemma gromov_eq (u v : Fin n) : gromov y z u v = ∑ A, if far z A u ∧ far z A v then y A else 0 := by
  rw [gromov, hgt_eq, hgt_eq, rho_eq, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  by_cases h1 : u ∈ A <;> by_cases h2 : v ∈ A <;> by_cases h3 : z ∈ A <;> simp [far, h1, h2, h3]

lemma rho_comm (u v : Fin n) : rho y u v = rho y v u := by
  rw [rho_eq, rho_eq]; refine Finset.sum_congr rfl (fun A _ => ?_)
  by_cases h1 : u ∈ A <;> by_cases h2 : v ∈ A <;> simp [h1, h2]

lemma rho_self (u : Fin n) : rho y u u = 0 := by simp [rho]

lemma gromov_comm (u v : Fin n) : gromov y z u v = gromov y z v u := by
  rw [gromov, gromov, rho_comm]; ring

variable {y}

lemma hgt_nonneg (hy : ∀ A, 0 ≤ y A) (u : Fin n) : 0 ≤ hgt y z u := by
  rw [hgt, rho]; exact Finset.sum_nonneg (fun A _ => hy A)

lemma gromov_nonneg (hy : ∀ A, 0 ≤ y A) (u v : Fin n) : 0 ≤ gromov y z u v := by
  rw [gromov_eq]; exact Finset.sum_nonneg (fun A _ => by split_ifs <;> simp [hy A])

/-- `g_uv ≤ h_u`. -/
lemma gromov_le (hy : ∀ A, 0 ≤ y A) (u v : Fin n) : gromov y z u v ≤ hgt y z u := by
  rw [gromov_eq, hgt_eq]
  refine Finset.sum_le_sum (fun A _ => ?_)
  split_ifs with h1 h2 <;> simp_all

end Loads

section Tree
variable {n : ℕ} (y : Finset (Fin n) → ℝ) (z : Fin n) {m : ℕ} (t : Fin (m + 1) → Fin n)
  (ea eb : Fin m → Fin (m + 1))

/-- The Gromov product on terminal pairs, as a function of an (unordered) edge. -/
noncomputable def gT : Sym2 (Fin (m + 1)) → ℝ :=
  Sym2.lift ⟨fun a b => gromov y z (t a) (t b), fun _ _ => gromov_comm y z _ _⟩

@[simp] lemma gT_mk (a b : Fin (m + 1)) : gT y z t s(a, b) = gromov y z (t a) (t b) := rfl

/-- Depth of the node with index `k`. -/
noncomputable def depN (k : ℕ) : ℝ :=
  if k = 0 then 0 else if k ≤ m then gT y z t s(ext ea (m - k), ext eb (m - k))
  else if h : k - (m + 1) < m + 1 then hgt y z (t ⟨k - (m + 1), h⟩) else 0

/-- Node depths: `0` at the root `z`, `g_{e_j}` at the node of merge `j`, `h_u` at terminal `u`. -/
noncomputable def dep (x : Fin (2 * m + 1 + 1)) : ℝ := depN y z t ea eb x.val

/-- The edge weight of the edge `{x, par x}`: `h_x - h_{par x}`. -/
noncomputable def wt (x : Fin (2 * m + 1 + 1)) : ℝ := dep y z t ea eb x - dep y z t ea eb (par ea eb x)

lemma dep_zero : dep y z t ea eb 0 = 0 := by simp [dep, depN]

lemma dep_mnode {j : ℕ} (hj : j < m) : dep y z t ea eb (mnode m j) = gT y z t s(ext ea j, ext eb j) := by
  show depN y z t ea eb (m - j) = _
  unfold depN
  rw [if_neg (by omega), if_pos (by omega), show m - (m - j) = j by omega]

lemma dep_tnode (i : Fin (m + 1)) : dep y z t ea eb (tnode i) = hgt y z (t i) := by
  show depN y z t ea eb (m + 1 + i.val) = _
  unfold depN
  rw [if_neg (by omega), if_neg (by omega), dif_pos (by omega)]
  congr 2; ext; simp

lemma node_cases (x : Fin (2 * m + 1 + 1)) : x = 0 ∨ (∃ j < m, x = mnode m j) ∨ ∃ i, x = tnode i := by
  by_cases h0 : x.val = 0
  · exact Or.inl (Fin.ext h0)
  · by_cases h1 : x.val ≤ m
    · exact Or.inr (Or.inl ⟨m - x.val, by omega, Fin.ext (by simp; omega)⟩)
    · exact Or.inr (Or.inr ⟨⟨x.val - (m + 1), by omega⟩, Fin.ext (by simp; omega)⟩)

lemma par_zero : par ea eb 0 = 0 := pa_zero_zero ea eb m le_rfl

variable {y}

lemma dep_nonneg (hy : ∀ A, 0 ≤ y A) (x : Fin (2 * m + 1 + 1)) : 0 ≤ dep y z t ea eb x := by
  rcases node_cases x with rfl | ⟨j, hj, rfl⟩ | ⟨i, rfl⟩
  · rw [dep_zero]
  · rw [dep_mnode y z t ea eb hj, gT_mk]; exact gromov_nonneg z hy _ _
  · rw [dep_tnode]; exact hgt_nonneg z hy _

/-- Depth is monotone along parent edges: `0 ≤ g_{uv} ≤ min(h_u, h_v)` and the merge order is non-increasing. -/
lemma dep_par_le (hM : IsMSTOrder (gT y z t) ea eb) (hy : ∀ A, 0 ≤ y A) (x : Fin (2 * m + 1 + 1)) :
    dep y z t ea eb (par ea eb x) ≤ dep y z t ea eb x := by
  rcases (inv ea eb m le_rfl).2.1 x with h | h
  · change dep y z t ea eb (par ea eb x) ≤ _
    unfold par; rw [h, dep_zero]; exact dep_nonneg z t ea eb hy x
  · set j := m - (pa ea eb m x).val with hjdef
    have hj : j < m := by omega
    have hpx : pa ea eb m x = mnode m j := Fin.ext (by simp [hjdef]; omega)
    have hR := pa_child ea eb m le_rfl x j hj hpx
    change dep y z t ea eb (pa ea eb m x) ≤ _
    rw [hpx, dep_mnode y z t ea eb hj, gT_mk]
    have key : ∀ p, (p = ext ea j ∨ p = ext eb j) → x = rt ea eb j p →
        gromov y z (t (ext ea j)) (t (ext eb j)) ≤ dep y z t ea eb x := by
      intro p hp hx
      rcases rt_cases ea eb j hj.le p with h' | ⟨j', hj', h'⟩ <;> rw [hx, h']
      · rw [dep_tnode]
        rcases hp with rfl | rfl
        · exact gromov_le z hy _ _
        · rw [gromov_comm]; exact gromov_le z hy _ _
      · rw [dep_mnode y z t ea eb (by omega), gT_mk]
        have := hM.anti ⟨j', by omega⟩ ⟨j, hj⟩ (by rw [Fin.le_def]; simp; omega)
        rw [← ext_fin ea, ← ext_fin eb, ← ext_fin ea, ← ext_fin eb] at this
        simpa using this
    rcases hR with hx | hx
    · exact key _ (Or.inl rfl) hx
    · exact key _ (Or.inr rfl) hx

lemma wt_nonneg (hM : IsMSTOrder (gT y z t) ea eb) (hy : ∀ A, 0 ≤ y A) (x : Fin (2 * m + 1 + 1)) :
    0 ≤ wt y z t ea eb x := by
  have := dep_par_le z t ea eb hM hy x
  unfold wt; linarith

/-- **The constructed tree** (as a weighted tree on the nodes `Fin (2m+2)`). -/
noncomputable def ctree (hM : IsMSTOrder (gT y z t) ea eb) (hy : ∀ A, 0 ≤ y A) :
    TreeCoverLB.WeightedTree (Fin (2 * m + 1 + 1)) :=
  MTSPCC.ptree (par ea eb) (par_lt ea eb) (wt y z t ea eb) (wt_nonneg z t ea eb hM hy)

/-- Telescoping: the root distance of a node is its depth. -/
lemma anc_sum (x : Fin (2 * m + 1 + 1)) :
    ((MTSPCC.anc (par ea eb) (par_lt ea eb) x).map (wt y z t ea eb)).sum = dep y z t ea eb x := by
  induction x using WellFoundedLT.induction with | _ x ih => ?_
  by_cases hx : x = 0
  · rw [hx, MTSPCC.anc_zero _ (par_lt ea eb), dep_zero]; simp
  · rw [MTSPCC.anc_of_ne _ (par_lt ea eb) hx, List.map_cons, List.sum_cons, ih _ (par_lt ea eb x hx), wt]
    ring

lemma anc_sub {w x : Fin (2 * m + 1 + 1)} (h : w ∈ MTSPCC.anc (par ea eb) (par_lt ea eb) x) :
    ∀ v ∈ MTSPCC.anc (par ea eb) (par_lt ea eb) w, v ∈ MTSPCC.anc (par ea eb) (par_lt ea eb) x := by
  induction x using WellFoundedLT.induction with | _ x ih => ?_
  by_cases hx : x = 0
  · rw [hx, MTSPCC.anc_zero _ (par_lt ea eb)] at h; simp at h
  · rw [MTSPCC.anc_of_ne _ (par_lt ea eb) hx] at h ⊢
    rcases List.mem_cons.mp h with rfl | h
    · rw [MTSPCC.anc_of_ne _ (par_lt ea eb) hx]; exact fun v hv => hv
    · exact fun v hv => List.mem_cons_of_mem _ (ih _ (par_lt ea eb x hx) h v hv)

lemma iter_mem (k : ℕ) (x : Fin (2 * m + 1 + 1)) (h : (par ea eb)^[k] x ≠ 0) :
    (par ea eb)^[k] x ∈ MTSPCC.anc (par ea eb) (par_lt ea eb) x := by
  induction k generalizing x with
  | zero =>
    simp only [Function.iterate_zero, id] at h ⊢
    rw [MTSPCC.anc_of_ne _ (par_lt ea eb) h]; exact List.mem_cons_self
  | succ k ih =>
    have hx : x ≠ 0 := by
      intro hx; rw [hx, Function.iterate_fixed (par_zero ea eb)] at h; exact h rfl
    rw [Function.iterate_succ_apply] at h ⊢
    rw [MTSPCC.anc_of_ne _ (par_lt ea eb) hx]
    exact List.mem_cons_of_mem _ (ih _ h)

variable (hM : IsMSTOrder (gT y z t) ea eb) (hy : ∀ A, 0 ≤ y A)

/-- Distance through a common ancestor. -/
lemma dist_le_common {a b w : Fin (2 * m + 1 + 1)}
    (ha : w ∈ MTSPCC.anc (par ea eb) (par_lt ea eb) a) (hb : w ∈ MTSPCC.anc (par ea eb) (par_lt ea eb) b) :
    (ctree z t ea eb hM hy).dist a b ≤
      (dep y z t ea eb a - dep y z t ea eb w) + (dep y z t ea eb b - dep y z t ea eb w) := by
  unfold ctree
  rw [MTSPCC.ptree_dist_symmDiff]
  set A := (MTSPCC.anc (par ea eb) (par_lt ea eb) a).toFinset
  set B := (MTSPCC.anc (par ea eb) (par_lt ea eb) b).toFinset
  set W := (MTSPCC.anc (par ea eb) (par_lt ea eb) w).toFinset
  have hWA : W ⊆ A := fun v hv => List.mem_toFinset.mpr (anc_sub ea eb ha v (List.mem_toFinset.mp hv))
  have hWB : W ⊆ B := fun v hv => List.mem_toFinset.mpr (anc_sub ea eb hb v (List.mem_toFinset.mp hv))
  have hc := wt_nonneg z t ea eb hM hy
  have hsum : ∀ x, ∑ v ∈ (MTSPCC.anc (par ea eb) (par_lt ea eb) x).toFinset, wt y z t ea eb v =
      dep y z t ea eb x := fun x => by
    rw [List.sum_toFinset _ (MTSPCC.anc_nodup _ (par_lt ea eb) x), anc_sum]
  have h1 : symmDiff A B ⊆ (A \ W) ∪ (B \ W) := by
    intro v hv
    rcases Finset.mem_symmDiff.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h1, fun h => h2 (hWB h)⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h1, fun h => h2 (hWA h)⟩)
  refine (Finset.sum_le_sum_of_subset_of_nonneg h1 (fun v _ _ => hc v)).trans ?_
  have h2 := Finset.sum_union_inter (s₁ := A \ W) (s₂ := B \ W) (f := wt y z t ea eb)
  have h3 : 0 ≤ ∑ v ∈ (A \ W) ∩ (B \ W), wt y z t ea eb v := Finset.sum_nonneg (fun v _ => hc v)
  rw [Finset.sum_sdiff_eq_sub hWA, Finset.sum_sdiff_eq_sub hWB] at h2
  rw [hsum a, hsum w] at h2; rw [hsum b] at h2
  linarith

/-- `d_C(u, v) ≤ ρ(u, v)` for two terminals (uses the maximum spanning tree property). -/
theorem dist_tnode (a b : Fin (m + 1)) :
    (ctree z t ea eb hM hy).dist (tnode a) (tnode b) ≤ rho y (t a) (t b) := by
  by_cases hab : a = b
  · rw [hab, MTSPGL.WT.dist_self, rho_self]
  · obtain ⟨j, hj, ⟨ka, hka⟩, ⟨kb, hkb⟩, hg⟩ := exists_common ea eb hM hab
    have hw0 : mnode m j ≠ 0 := mnode_ne_zero hj
    have ha := iter_mem ea eb ka _ (by rw [hka]; exact hw0)
    have hb := iter_mem ea eb kb _ (by rw [hkb]; exact hw0)
    rw [hka] at ha; rw [hkb] at hb
    refine (dist_le_common z t ea eb hM hy ha hb).trans ?_
    rw [dep_tnode, dep_tnode, dep_mnode y z t ea eb hj]
    rw [gT_mk] at hg
    have : rho y (t a) (t b) = hgt y z (t a) + hgt y z (t b) - 2 * gromov y z (t a) (t b) := by
      rw [gromov]; ring
    rw [this]; linarith

/-- `d_C(u, z) = h_u = ρ(z, u)`. -/
theorem dist_tnode_root (a : Fin (m + 1)) : (ctree z t ea eb hM hy).dist (tnode a) 0 = hgt y z (t a) := by
  unfold ctree
  rw [MTSPCC.ptree_dist_root, anc_sum, dep_tnode]

/-- The sum of all node depths. -/
lemma sum_dep : ∑ x, dep y z t ea eb x = ∑ j, gT y z t s(ea j, eb j) + ∑ i, hgt y z (t i) := by
  unfold dep
  rw [Fin.sum_univ_eq_sum_range (depN y z t ea eb), show 2 * m + 1 + 1 = (m + 1) + (m + 1) by ring,
    Finset.sum_range_add, Finset.sum_range_succ']
  have e1 : ∑ k ∈ Finset.range m, depN y z t ea eb (k + 1) =
      ∑ k ∈ Finset.range m, (fun j => gT y z t s(ext ea j, ext eb j)) (m - 1 - k) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_range] at hk
    simp only [depN]
    rw [if_neg (by omega), if_pos (by omega), show m - (k + 1) = m - 1 - k by omega]
  have e2 : ∑ k ∈ Finset.range (m + 1), depN y z t ea eb (m + 1 + k) =
      ∑ k ∈ Finset.range (m + 1), (fun k => if h : k < m + 1 then hgt y z (t ⟨k, h⟩) else 0) k := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_range] at hk
    simp only [depN]
    rw [if_neg (by omega), if_neg (by omega), dif_pos (by omega), dif_pos hk]
    congr 3; omega
  rw [e1, e2, Finset.sum_range_reflect (fun j => gT y z t s(ext ea j, ext eb j)) m, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  simp only [depN, if_pos, Fin.is_lt, dif_pos, ext_fin]
  simp

/-- Each merge node has at most two children, so `∑_x h_{par x} ≤ 2 ∑_j g_{e_j}`. -/
lemma sum_dep_par (hy : ∀ A, 0 ≤ y A) : ∑ x, dep y z t ea eb (par ea eb x) ≤ 2 * ∑ j, gT y z t s(ea j, eb j) := by
  have hper : ∀ x, dep y z t ea eb (par ea eb x) =
      ∑ j : Fin m, if par ea eb x = mnode m j then gT y z t s(ea j, eb j) else 0 := by
    intro x
    rcases (inv ea eb m le_rfl).2.1 x with h | h
    · change dep y z t ea eb (pa ea eb m x) = ∑ j : Fin m, if pa ea eb m x = mnode m j then _ else _
      rw [h, dep_zero]
      refine (Finset.sum_eq_zero (fun j _ => ?_)).symm
      rw [if_neg (Ne.symm (mnode_ne_zero j.isLt))]
    · set j0 : Fin m := ⟨m - (pa ea eb m x).val, by omega⟩ with hj0
      have hpx : pa ea eb m x = mnode m j0 := Fin.ext (by simp [hj0]; omega)
      change dep y z t ea eb (pa ea eb m x) = ∑ j : Fin m, if pa ea eb m x = mnode m j then _ else _
      rw [Finset.sum_eq_single j0, if_pos hpx, hpx, dep_mnode y z t ea eb j0.isLt, ext_fin, ext_fin]
      · intro j _ hj
        rw [if_neg]
        rw [hpx]; intro h
        have := congrArg Fin.val h; simp at this
        exact hj (Fin.ext (by omega))
      · simp
  rw [Finset.sum_congr rfl (fun x _ => hper x), Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun x => par ea eb x = mnode m j)).card ≤ 2 := by
    have hsub : Finset.univ.filter (fun x => par ea eb x = mnode m j) ⊆
        {rt ea eb j (ext ea j), rt ea eb j (ext eb j)} := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases pa_child ea eb m le_rfl x j j.isLt hx with h | h <;> simp [h]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have hg : 0 ≤ gT y z t s(ea j, eb j) := by rw [gT_mk]; exact gromov_nonneg z hy _ _
  have : ((Finset.univ.filter (fun x => par ea eb x = mnode m j)).card : ℝ) ≤ 2 := by exact_mod_cast hc
  nlinarith

/-- `∑_x wt x ≥ ∑_{u ≠ z} h_u - ∑_{(u,v) ∈ R} g_uv`. -/
theorem sum_wt_ge (hy : ∀ A, 0 ≤ y A) : ∑ i, hgt y z (t i) - ∑ j, gT y z t s(ea j, eb j) ≤ ∑ x, wt y z t ea eb x := by
  unfold wt
  rw [Finset.sum_sub_distrib, sum_dep]
  have := sum_dep_par z t ea eb hy
  linarith

include hM hy in
/-- `∑_{u ≠ z} h_u - ∑_{(u,v) ∈ R} g_uv = ∑_A y_A (|A| - |R[A]|) ≥ ∑_A y_A` (forest bound). -/
theorem sum_y_le (hF : ∀ A, y A ≠ 0 → ∃ i, far z A (t i)) :
    ∑ A, y A ≤ ∑ i, hgt y z (t i) - ∑ j, gT y z t s(ea j, eb j) := by
  simp only [hgt_eq, gT_mk, gromov_eq]
  rw [Finset.sum_comm (f := fun i A => if far z A (t i) then y A else 0),
    Finset.sum_comm (f := fun j A => if far z A (t (ea j)) ∧ far z A (t (eb j)) then y A else 0),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun A _ => ?_)
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
    nsmul_eq_mul, ← sub_mul]
  by_cases hA : y A = 0
  · rw [hA]; simp
  · obtain ⟨i, hi⟩ := hF A hA
    set F := Finset.univ.filter (fun i => far z A (t i)) with hFdef
    have hb := forest_bound hM F ⟨i, by simp [hFdef, hi]⟩
    have he : Finset.univ.filter (fun j => far z A (t (ea j)) ∧ far z A (t (eb j))) =
        Finset.univ.filter (fun j => ea j ∈ F ∧ eb j ∈ F) := by
      ext j; simp [hFdef]
    rw [he]
    have : (1 : ℝ) ≤ (F.card : ℝ) - ((Finset.univ.filter (fun j => ea j ∈ F ∧ eb j ∈ F)).card : ℝ) := by
      have : ((Finset.univ.filter (fun j => ea j ∈ F ∧ eb j ∈ F)).card : ℝ) + 1 ≤ (F.card : ℝ) := by
        exact_mod_cast hb
      linarith
    nlinarith [hy A]

end Tree

/-! ## The Steiner tree on `S` -/

section Steiner
variable {n : ℕ} {y : Finset (Fin n) → ℝ} {z : Fin n} {m : ℕ} {t : Fin (m + 1) → Fin n}
  {ea eb : Fin m → Fin (m + 1)}

/-- The embedding of points into nodes: `z ↦ 0`, `t i ↦ tnode i`. -/
noncomputable def emb (t : Fin (m + 1) → Fin n) (u : Fin n) : Fin (2 * m + 1 + 1) :=
  if h : ∃ i, t i = u then tnode h.choose else 0

lemma emb_t (ht : Function.Injective t) (i : Fin (m + 1)) : emb t (t i) = tnode i := by
  have h : ∃ i', t i' = t i := ⟨i, rfl⟩
  rw [emb, dif_pos h, ht h.choose_spec]

lemma emb_z (hz : ∀ i, t i ≠ z) : emb t z = 0 := by
  rw [emb, dif_neg]; rintro ⟨i, hi⟩; exact hz i hi

lemma mem_S {S : Finset (Fin n)} (hS : S = insert z (Finset.univ.image t)) {u : Fin n} :
    u ∈ S ↔ u = z ∨ ∃ i, t i = u := by
  rw [hS]; simp

lemma tnode_ne_zero (i : Fin (m + 1)) : tnode i ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp at this

/-- **The Steiner tree of Claim 9.12** on `S = {z} ∪ {t i}`. -/
noncomputable def gtTree (S : Finset (Fin n)) (hS : S = insert z (Finset.univ.image t))
    (ht : Function.Injective t) (hz : ∀ i, t i ≠ z)
    (hM : IsMSTOrder (gT y z t) ea eb) (hy : ∀ A, 0 ≤ y A) : SteinerTree S where
  m := 2 * m + 1 + 1
  ι := emb t
  inj := by
    intro u hu v hv huv
    rw [Finset.mem_coe, mem_S hS] at hu hv
    rcases hu with hu | ⟨i, rfl⟩ <;> rcases hv with hv | ⟨j, rfl⟩
    · rw [hu, hv]
    · rw [hu, emb_z hz, emb_t ht] at huv; exact absurd huv.symm (tnode_ne_zero j)
    · rw [hv, emb_z hz, emb_t ht] at huv; exact absurd huv (tnode_ne_zero i)
    · rw [emb_t ht, emb_t ht] at huv; rw [tnode_inj huv]
  T := ctree z t ea eb hM hy
  leaves := by
    intro a ha
    rcases node_cases a with rfl | ⟨j, hj, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨z, by rw [mem_S hS]; exact Or.inl rfl, emb_z hz⟩
    · exfalso
      have := MTSPCC.ptree_leaf (par ea eb) (par_lt ea eb) (wt y z t ea eb) (wt_nonneg z t ea eb hM hy)
        (mnode_ne_zero hj) ha _ (rt_ne_zero ea eb j hj.le (ext ea j))
      exact this (par_child ea eb j hj)
    · exact ⟨t i, by rw [mem_S hS]; exact Or.inr ⟨i, rfl⟩, emb_t ht i⟩

variable (S : Finset (Fin n)) (hS : S = insert z (Finset.univ.image t))
  (ht : Function.Injective t) (hz : ∀ i, t i ≠ z)
  (hM : IsMSTOrder (gT y z t) ea eb) (hy : ∀ A, 0 ≤ y A)

/-- The tree is the parent-array tree with parent `par` and edge weights `wt x = h_x - h_{par x}`; the points are
embedded by `emb` (`z ↦ 0`, `t i ↦ tnode i`). -/
theorem gtTree_eq : (gtTree S hS ht hz hM hy).m = 2 * m + 1 + 1 ∧
    HEq (gtTree S hS ht hz hM hy).ι (emb t) ∧
    HEq (gtTree S hS ht hz hM hy).T
      (MTSPCC.ptree (par ea eb) (par_lt ea eb) (wt y z t ea eb) (wt_nonneg z t ea eb hM hy)) :=
  ⟨rfl, HEq.rfl, HEq.rfl⟩

include hM hy in
/-- **Nonnegative weights**: `wt x = h_x - h_{par x} ≥ 0`. -/
theorem gtTree_wt_nonneg (x : Fin (2 * m + 1 + 1)) : 0 ≤ wt y z t ea eb x := wt_nonneg z t ea eb hM hy x

/-- **`d_C(u, v) ≤ ρ(u, v)`** for all `u, v ∈ S`. -/
theorem gtTree_dist_le : ∀ u ∈ S, ∀ v ∈ S,
    (gtTree S hS ht hz hM hy).pathWt ((gtTree S hS ht hz hM hy).ι u) ((gtTree S hS ht hz hM hy).ι v) ≤
      rho y u v := by
  intro u hu v hv
  rw [mem_S hS] at hu hv
  show (ctree z t ea eb hM hy).dist (emb t u) (emb t v) ≤ rho y u v
  rcases hu with hu | ⟨a, rfl⟩ <;> rcases hv with hv | ⟨b, rfl⟩
  · rw [hu, hv, emb_z hz, MTSPGL.WT.dist_self, rho_self]
  · rw [hu, emb_z hz, emb_t ht, MTSPGL.WT.dist_comm]
    exact (dist_tnode_root z t ea eb hM hy b).le
  · rw [hv, emb_z hz, emb_t ht, rho_comm]
    exact (dist_tnode_root z t ea eb hM hy a).le
  · rw [emb_t ht, emb_t ht]
    exact dist_tnode z t ea eb hM hy a b

/-- The weight of the tree is `∑_x (h_x - h_{par x})`. -/
theorem gtTree_weight : (gtTree S hS ht hz hM hy).weight = ∑ x, wt y z t ea eb x := by
  unfold SteinerTree.weight SteinerTree.edges
  have h := MTSPCC.ptree_weight (par ea eb) (par_lt ea eb) (wt y z t ea eb) (wt_nonneg z t ea eb hM hy)
  have e : ∑ e ∈ Finset.univ.filter (fun e => e ∈ (gtTree S hS ht hz hM hy).T.G.edgeSet),
      (gtTree S hS ht hz hM hy).T.w e =
      ∑ e ∈ (MTSPCC.ptree (par ea eb) (par_lt ea eb) (wt y z t ea eb) (wt_nonneg z t ea eb hM hy)).G.edgeFinset,
      (MTSPCC.ptree (par ea eb) (par_lt ea eb) (wt y z t ea eb) (wt_nonneg z t ea eb hM hy)).w e := by
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.edgeFinset]
    exact Set.mem_toFinset.symm
  rw [e, h, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs with hx
  · rfl
  · push Not at hx; rw [hx, wt, par_zero, sub_self]

/-- **`w(C) ≥ ∑_{u ≠ z} h_u - ∑_{(u,v) ∈ R} g_uv`.** -/
theorem gtTree_weight_ge' :
    ∑ i, hgt y z (t i) - ∑ j, gT y z t s(ea j, eb j) ≤ (gtTree S hS ht hz hM hy).weight := by
  rw [gtTree_weight]; exact sum_wt_ge z t ea eb hy

/-- **`w(C) ≥ ∑_A y_A`**, provided every cut with `y_A ≠ 0` has a point of `S` on its far side from `z`. -/
theorem gtTree_weight_ge (hF : ∀ A, y A ≠ 0 → ∃ u ∈ S, far z A u) :
    ∑ A, y A ≤ (gtTree S hS ht hz hM hy).weight := by
  refine le_trans ?_ (gtTree_weight_ge' S hS ht hz hM hy)
  refine sum_y_le z t ea eb hM hy (fun A hA => ?_)
  obtain ⟨u, hu, hfu⟩ := hF A hA
  rw [mem_S hS] at hu
  rcases hu with hu | ⟨i, rfl⟩
  · rw [hu] at hfu; exact absurd Iff.rfl hfu
  · exact ⟨i, hfu⟩

end Steiner

end MTSPGT

end ASM5

section ASM6
-- from Solutions.GT.Main

/-!
# Claim 9.12: a dominated Steiner tree of weight at least the dual value

`gtTree_dominated`, `gtTree_weight_ge_of_feasible`: the explicit tree of `Solutions/GT/Claim912.lean` is dominated
by `d` and has weight `≥ ∑_A y_A` for every feasible dual `y` on `S`.
`claim_9_12`: the existential corollary for an arbitrary nonempty `S`.
-/

open scoped Classical

namespace MTSPGT
open SimpleGraph MetricTSPSublinear

variable {n : ℕ} {d : Fin n → Fin n → ℝ} {S : Finset (Fin n)} {y : Finset (Fin n) → ℝ}

/-- A feasible dual: `ρ(u, v) ≤ d(u, v)` on `S`. -/
lemma rho_le_d (hfeas : IsDualFeasible d S y) (hd : ∀ u ∈ S, 0 ≤ d u u) {u v : Fin n} (hu : u ∈ S)
    (hv : v ∈ S) : rho y u v ≤ d u v := by
  by_cases huv : u = v
  · rw [huv, rho_self]; exact hd v hv
  · exact hfeas.2.2 u hu v hv huv

/-- A feasible dual: every cut with `y_A ≠ 0` has a point of `S` on the side away from `z`. -/
lemma far_of_feasible (hfeas : IsDualFeasible d S y) (z : Fin n) (A : Finset (Fin n))
    (hA : y A ≠ 0) : ∃ u ∈ S, far z A u := by
  have h : A ⊆ S ∧ A.Nonempty ∧ A ≠ S := by
    by_contra h; exact hA (hfeas.2.1 A h)
  obtain ⟨hAS, ⟨a, ha⟩, hne⟩ := h
  by_cases hzA : z ∈ A
  · obtain ⟨u, hu, huA⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hAS, hne⟩)
    exact ⟨u, hu, by simp [far, huA, hzA]⟩
  · exact ⟨a, hAS ha, by simp [far, ha, hzA]⟩

section Explicit
variable {z : Fin n} {m : ℕ} {t : Fin (m + 1) → Fin n} {ea eb : Fin m → Fin (m + 1)}
  (hS : S = insert z (Finset.univ.image t)) (ht : Function.Injective t) (hz : ∀ i, t i ≠ z)
  (hM : IsMSTOrder (gT y z t) ea eb)

/-- **The constructed tree is dominated** by `d` (for any feasible dual). -/
theorem gtTree_dominated (hfeas : IsDualFeasible d S y) (hd : ∀ u ∈ S, 0 ≤ d u u) :
    Dominated d (gtTree S hS ht hz hM hfeas.1) := fun u hu v hv =>
  (gtTree_dist_le S hS ht hz hM hfeas.1 u hu v hv).trans (rho_le_d hfeas hd hu hv)

/-- **The constructed tree has weight at least `∑_A y_A`** (for any feasible dual). -/
theorem gtTree_weight_ge_of_feasible (hfeas : IsDualFeasible d S y) :
    ∑ A, y A ≤ (gtTree S hS ht hz hM hfeas.1).weight :=
  gtTree_weight_ge S hS ht hz hM hfeas.1
    (far_of_feasible hfeas z)

end Explicit

/-- The one-node Steiner tree on `S = {z}`. -/
noncomputable def pointTree (z : Fin n) (hS : S = {z}) : SteinerTree S where
  m := 1
  ι := fun _ => 0
  inj := by
    intro u hu v hv _
    rw [Finset.mem_coe, hS, Finset.mem_singleton] at hu hv
    rw [hu, hv]
  T := MTSPCC.ptree (N := 0) (fun _ => 0) (fun x hx => absurd (Fin.ext (by have := x.isLt; simp)) hx) (fun _ => 0)
    (fun _ => le_rfl)
  leaves := fun a _ => ⟨z, by rw [hS]; exact Finset.mem_singleton_self z, Fin.ext (by have := a.isLt; simp)⟩

/-- **Claim 9.12 (existential form).** For every nonempty `S` and every feasible dual `y` on `S` (with
`d u u ≥ 0` on `S`), there is a Steiner tree on `S` dominated by `d` with weight `≥ ∑_A y_A`. -/
theorem claim_9_12 (d : Fin n → Fin n → ℝ) (S : Finset (Fin n)) (hSne : S.Nonempty) (hd : ∀ u ∈ S, 0 ≤ d u u)
    (y : Finset (Fin n) → ℝ) (hfeas : IsDualFeasible d S y) :
    ∃ C : SteinerTree S, Dominated d C ∧ ∑ A, y A ≤ C.weight := by
  obtain ⟨z, hzS⟩ := hSne
  by_cases hS' : (S.erase z).Nonempty
  · obtain ⟨m, hk⟩ : ∃ m, (S.erase z).card = m + 1 :=
      ⟨(S.erase z).card - 1, by have := hS'.card_pos; omega⟩
    set t : Fin (m + 1) → Fin n := fun i => (S.erase z).orderEmbOfFin hk i with htdef
    have ht : Function.Injective t := ((S.erase z).orderEmbOfFin hk).injective
    have hmem : ∀ i, t i ∈ S.erase z := fun i => Finset.orderEmbOfFin_mem _ hk i
    have hz : ∀ i, t i ≠ z := fun i => Finset.ne_of_mem_erase (hmem i)
    have hS : S = insert z (Finset.univ.image t) := by
      ext u
      by_cases huz : u = z
      · rw [huz]; simp [hzS]
      · have hr := Finset.range_orderEmbOfFin (S.erase z) hk
        have : u ∈ S ↔ u ∈ Set.range t := by
          rw [htdef, hr, Finset.mem_coe, Finset.mem_erase]; exact ⟨fun h => ⟨huz, h⟩, fun h => h.2⟩
        rw [this]; simp [huz]
    obtain ⟨ea, eb, hM⟩ := exists_isMSTOrder (gT y z t)
    exact ⟨gtTree S hS ht hz hM hfeas.1, gtTree_dominated hS ht hz hM hfeas hd,
      gtTree_weight_ge_of_feasible hS ht hz hM hfeas⟩
  · have hS : S = {z} := by
      ext u
      rw [Finset.mem_singleton]
      constructor
      · intro hu; by_contra h; exact hS' ⟨u, Finset.mem_erase.mpr ⟨h, hu⟩⟩
      · rintro rfl; exact hzS
    refine ⟨pointTree z hS, ?_, ?_⟩
    · intro u hu v hv
      rw [hS, Finset.mem_singleton] at hu hv
      rw [hu, hv]
      unfold SteinerTree.pathWt
      rw [MTSPGL.WT.dist_self]
      exact hd z hzS
    · have hy0 : ∀ A, y A = 0 := by
        intro A
        by_contra hA
        obtain ⟨u, hu, hfu⟩ := far_of_feasible hfeas z A hA
        rw [hS, Finset.mem_singleton] at hu
        rw [hu] at hfu; exact hfu Iff.rfl
      simp only [hy0, Finset.sum_const_zero]
      unfold SteinerTree.weight
      refine Finset.sum_nonneg (fun e he => ?_)
      simp only [SteinerTree.edges, Finset.mem_filter, Finset.mem_univ, true_and] at he
      exact (pointTree z hS).T.w_nonneg e he

end MTSPGT

end ASM6

open MetricTSPSublinear in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (S : Finset (Fin n))
    (hSne : S.Nonempty) (y : Finset (Fin n) → ℝ) (hfeas : IsDualFeasible d S y) :
    ∃ C : SteinerTree S, Dominated d C ∧ ∑ A, y A ≤ C.weight :=
  MTSPGT.claim_9_12 d S hSne (fun u _ => le_of_eq ((hd.1 u u).mpr rfl).symm) y hfeas
