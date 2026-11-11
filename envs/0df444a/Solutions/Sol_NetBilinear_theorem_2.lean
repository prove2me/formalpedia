-- Prove2me | solution 1 for NetBilinear.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T14:24:07.38592+00:00
-- url     : https://prove2.me/submissions/0b26b2ff-b508-44b9-be0c-2431df1f6472

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_NetBilinear_Network_IsECRAssignment

set_option autoImplicit false

namespace NetBilinear

variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]

omit [Fintype V] in
lemma rowsWith_card (s : Sign) (X : Finset V) : (rowsWith s X).card = X.card := by
  exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)

omit [Fintype V] [Fintype A] [DecidableEq A] in
lemma sum_rowsWith_inc (G : Network V A) (s : Sign) (X : Finset V) (k : A) :
    ∑ t ∈ rowsWith s X, G.incRow t k =
      s.toReal * ((if G.tail k ∈ X then 1 else 0) - (if G.head k ∈ X then 1 else 0)) := by
  rw [rowsWith, Finset.sum_image]
  · simp only [Network.incRow]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp
  · intro a ha b hb hab
    exact (Prod.mk.inj hab).1

lemma Sign.flip_toReal (s : Sign) : s.flip.toReal = -s.toReal := by
  cases s <;> norm_num [Sign.flip, Sign.toReal]

omit [Fintype V] in
lemma sum_partition_indicator (I1 I2 : Finset V) (hdisj : Disjoint I1 I2) (v : V) :
    ((if v ∈ I1 then (1 : ℝ) else 0) + (if v ∈ I2 then 1 else 0)) =
      (if v ∈ I1 ∪ I2 then 1 else 0) := by
  have hd := Finset.disjoint_left.mp hdisj
  by_cases h1 : v ∈ I1 <;> by_cases h2 : v ∈ I2 <;>
    simp_all

omit [Fintype V] [Fintype A] in
lemma agg_unit (G : Network V A) (l k : A) (σ s : Sign)
    (I1 I2 : Finset V) (hdisj : Disjoint I1 I2) :
    aggCoef G.incRow l σ (rowsWith s I1) (rowsWith s.flip I2)
      (fun _ => 1) (fun _ => 1) k =
    baseContrib l σ k + s.toReal *
      ((if G.tail k ∈ I1 ∪ I2 then 1 else 0) -
        (if G.head k ∈ I1 ∪ I2 then 1 else 0)) := by
  simp only [aggCoef, one_mul, sum_rowsWith_inc, Sign.flip_toReal]
  rw [← sum_partition_indicator I1 I2 hdisj (G.tail k),
    ← sum_partition_indicator I1 I2 hdisj (G.head k)]
  ring

lemma Sign.toReal_ne_zero (s : Sign) : s.toReal ≠ 0 := by
  cases s <;> norm_num [Sign.toReal]

omit [Fintype V] [Fintype A] [DecidableEq A] in
lemma incRow_ne_zero_of_incident (G : Network V A) (s : Sign) (v : V) (k : A)
    (hv : G.tail k = v ∨ G.head k = v) : G.incRow (v, s) k ≠ 0 := by
  rcases hv with rfl | rfl
  · simpa [Network.incRow, (G.loopless k).symm] using s.toReal_ne_zero
  · simpa [Network.incRow, G.loopless k] using neg_ne_zero.mpr s.toReal_ne_zero

omit [Fintype V] [Fintype A] in
lemma created_of_incident (G : Network V A) (l k : A) (σ s : Sign)
    (I1 I2 : Finset V) (v : V) (hv : v ∈ I1 ∪ I2)
    (hk : G.tail k = v ∨ G.head k = v) :
    IsCreated G.incRow l σ (rowsWith s I1) (rowsWith s.flip I2)
      (fun _ => 1) (fun _ => 1) k := by
  rcases Finset.mem_union.mp hv with hv | hv
  · right; left
    refine ⟨(v, s), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    · simpa using incRow_ne_zero_of_incident G s v k hk
  · right; right
    refine ⟨(v, s.flip), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    · simpa using incRow_ne_zero_of_incident G s.flip v k hk

omit [Fintype V] [Fintype A] in
lemma internal_cancelled (G : Network V A) (l k : A) (σ s : Sign)
    (I1 I2 : Finset V) (hdisj : Disjoint I1 I2) (hkl : k ≠ l)
    (ht : G.tail k ∈ I1 ∪ I2) (hh : G.head k ∈ I1 ∪ I2) :
    IsCancelled G.incRow l σ (rowsWith s I1) (rowsWith s.flip I2)
      (fun _ => 1) (fun _ => 1) k := by
  refine ⟨created_of_incident G l k σ s I1 I2 (G.tail k) ht (Or.inl rfl), ?_⟩
  rw [agg_unit G l k σ s I1 I2 hdisj]
  simp [ht, hh, baseContrib, hkl]

omit [Fintype V] [Fintype A] in
lemma base_cancelled (G : Network V A) (l : A) (σ s : Sign)
    (I1 I2 : Finset V) (hdisj : Disjoint I1 I2)
    (hz : σ.toReal + s.toReal *
      ((if G.tail l ∈ I1 ∪ I2 then 1 else 0) -
        (if G.head l ∈ I1 ∪ I2 then 1 else 0)) = 0) :
    IsCancelled G.incRow l σ (rowsWith s I1) (rowsWith s.flip I2)
      (fun _ => 1) (fun _ => 1) l := by
  refine ⟨Or.inl ?_, ?_⟩
  · simpa [baseContrib] using σ.toReal_ne_zero
  · simpa [agg_unit G l l σ s I1 I2 hdisj, baseContrib] using hz

omit [DecidableEq V] [DecidableEq A] in
/-- Every tree edge is represented by an internal arc. Taking the image of all
internal arcs avoids choosing representatives when the network has parallel arcs. -/
lemma tree_card_le_internal (G : Network V A) (I : Finset V)
    (T : G.underlying.Subgraph) (hT : T.verts = (I : Set V)) (hTree : T.coe.IsTree) :
    I.card ≤ {k : A | G.tail k ∈ I ∧ G.head k ∈ I}.ncard + 1 := by
  classical
  let U : Set A := {k | G.tail k ∈ I ∧ G.head k ∈ I}
  have hsub : T.edgeSet ⊆ (fun k => s(G.tail k, G.head k)) '' U := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : T.Adj a b := he
      have ha : a ∈ I := by simpa [hT] using T.edge_vert hab
      have hb : b ∈ I := by simpa [hT] using T.edge_vert hab.symm
      have habG := T.adj_sub hab
      change a ≠ b ∧ ((∃ k, G.tail k = a ∧ G.head k = b) ∨
        (∃ k, G.tail k = b ∧ G.head k = a)) at habG
      rcases habG.2 with ⟨k, ht, hh⟩ | ⟨k, ht, hh⟩
      · exact ⟨k, by simpa [U, ht, hh] using And.intro ha hb, by simp [ht, hh]⟩
      · exact ⟨k, by simpa [U, ht, hh] using And.intro hb ha, by simp [ht, hh, Sym2.eq_swap]⟩
  have hcard : T.edgeSet.ncard + 1 = I.card := by
    let : Fintype T.verts := Fintype.ofFinite _
    let : Fintype T.coe.edgeSet := Fintype.ofFinite _
    have hc : T.coe.edgeSet.ncard + 1 = Fintype.card T.verts := by
      simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] using
        hTree.card_edgeFinset
    calc
      T.edgeSet.ncard + 1 = T.coe.edgeSet.ncard + 1 := by
        rw [← T.image_coe_edgeSet_coe,
          Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
      _ = Fintype.card T.verts := hc
      _ = I.card := by rw [Set.fintypeCard_eq_ncard, hT, Set.ncard_coe_finset]
  rw [← hcard]
  exact Nat.add_le_add_right ((Set.ncard_le_ncard hsub).trans (Set.ncard_image_le)) 1

omit [Fintype V] [Fintype A] [DecidableEq A] in
/-- The boundary endpoint uses the base arc. Every other vertex uses the first
edge of a path to that endpoint. This also covers a tree with only one vertex. -/
lemma vertex_has_cancelled_arc (G : Network V A) (I : Finset V)
    (T : G.underlying.Subgraph) (hT : T.verts = (I : Set V)) (hTree : T.coe.IsTree)
    (l : A) (b : V) (hb : b ∈ I) (hbl : G.tail l = b ∨ G.head l = b)
    (v : V) (hv : v ∈ I) :
    ∃ k, (G.tail k = v ∨ G.head k = v) ∧
      (k = l ∨ (G.tail k ∈ I ∧ G.head k ∈ I)) := by
  classical
  by_cases hvb : v = b
  · exact ⟨l, hvb ▸ hbl, Or.inl rfl⟩
  let vv : T.verts := ⟨v, by simpa [hT] using hv⟩
  let bb : T.verts := ⟨b, by simpa [hT] using hb⟩
  have hne : vv ≠ bb := by
    intro h
    exact hvb (congrArg Subtype.val h)
  obtain ⟨u, hu⟩ := (hTree.connected.preconnected vv bb).nonempty_neighborSet_left hne
  have huI : u.val ∈ I := by simpa [hT] using u.property
  have hadj : T.Adj v u.val := hu
  have hadjG := T.adj_sub hadj
  change v ≠ u.val ∧ ((∃ k, G.tail k = v ∧ G.head k = u.val) ∨
    (∃ k, G.tail k = u.val ∧ G.head k = v)) at hadjG
  rcases hadjG.2 with ⟨k, ht, hh⟩ | ⟨k, ht, hh⟩
  · exact ⟨k, Or.inl ht, Or.inr ⟨ht ▸ hv, hh ▸ huI⟩⟩
  · exact ⟨k, Or.inr hh, Or.inr ⟨ht ▸ huI, hh ▸ hv⟩⟩

/-- Unit weights cancel all internal arcs and the base arc. Counting and
coverage prove both EC&R conditions uniformly for all four sign cases. -/
lemma unit_assignment (G : Network V A) (I : Finset V)
    (T : G.underlying.Subgraph) (hT : T.verts = (I : Set V)) (hTree : T.coe.IsTree)
    (l : A) (hl : Xor (G.tail l ∈ I) (G.head l ∈ I))
    (I1 I2 : Finset V) (hdisj : Disjoint I1 I2) (hunion : I1 ∪ I2 = I)
    (σ s : Sign)
    (hz : σ.toReal + s.toReal *
      ((if G.tail l ∈ I1 ∪ I2 then 1 else 0) -
        (if G.head l ∈ I1 ∪ I2 then 1 else 0)) = 0) :
    G.IsECRAssignment l σ (rowsWith s I1) (rowsWith s.flip I2) := by
  classical
  let U : Set A := {k | G.tail k ∈ I ∧ G.head k ∈ I}
  let C : Set A := {k | IsCancelled G.incRow l σ (rowsWith s I1) (rowsWith s.flip I2)
    (fun _ => 1) (fun _ => 1) k}
  have hlnot : l ∉ U := by
    intro h
    rcases hl with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · exact hh h.2
    · exact hh h.1
  have hcancel : insert l U ⊆ C := by
    intro k hk
    rcases Set.mem_insert_iff.mp hk with hkl | hk
    · subst k
      exact base_cancelled G l σ s I1 I2 hdisj hz
    · apply internal_cancelled G l k σ s I1 I2 hdisj
      · intro hkl
        exact hlnot (hkl ▸ hk)
      · simpa [hunion] using hk.1
      · simpa [hunion] using hk.2
  obtain ⟨b, hb, hbl⟩ : ∃ b, b ∈ I ∧ (G.tail l = b ∨ G.head l = b) := by
    rcases hl with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · exact ⟨G.tail l, ht, Or.inl rfl⟩
    · exact ⟨G.head l, ht, Or.inr rfl⟩
  have hcoverage : ∀ v ∈ I, ∃ k, (G.tail k = v ∨ G.head k = v) ∧ k ∈ C := by
    intro v hv
    obtain ⟨k, hi, hk⟩ := vertex_has_cancelled_arc G I T hT hTree l b hb hbl v hv
    exact ⟨k, hi, hcancel (Set.mem_insert_iff.mpr hk)⟩
  constructor
  · apply Finset.disjoint_left.mpr
    intro t ht1 ht2
    rcases Finset.mem_image.mp ht1 with ⟨v, hv, rfl⟩
    rcases Finset.mem_image.mp ht2 with ⟨u, hu, he⟩
    have huv : u = v := (Prod.mk.inj he).1
    exact Finset.disjoint_left.mp hdisj hv (huv ▸ hu)
  · refine ⟨(fun _ => 1), (fun _ => 1), ?_, ?_, ?_, ?_⟩
    · intro t ht; norm_num
    · intro t ht; norm_num
    · change (rowsWith s I1).card + (rowsWith s.flip I2).card ≤ C.ncard
      calc
        (rowsWith s I1).card + (rowsWith s.flip I2).card = I.card := by
          rw [rowsWith_card, rowsWith_card, ← Finset.card_union_of_disjoint hdisj, hunion]
        _ ≤ U.ncard + 1 := tree_card_le_internal G I T hT hTree
        _ = (insert l U).ncard := (Set.ncard_insert_of_notMem hlnot).symm
        _ ≤ C.ncard := Set.ncard_le_ncard hcancel
    · intro hnonempty
      refine ⟨⟨l, ?_, ?_⟩, ?_, ?_⟩
      · simpa [baseContrib] using σ.toReal_ne_zero
      · exact hcancel (Set.mem_insert l U)
      · intro t ht
        rcases Finset.mem_image.mp ht with ⟨v, hv, rfl⟩
        have hvI : v ∈ I := hunion ▸ Finset.mem_union_left I2 hv
        obtain ⟨k, hi, hk⟩ := hcoverage v hvI
        exact ⟨k, by simpa using incRow_ne_zero_of_incident G s v k hi, hk⟩
      · intro t ht
        rcases Finset.mem_image.mp ht with ⟨v, hv, rfl⟩
        have hvI : v ∈ I := hunion ▸ Finset.mem_union_right I1 hv
        obtain ⟨k, hi, hk⟩ := hcoverage v hvI
        exact ⟨k, by simpa using incRow_ne_zero_of_incident G s.flip v k hi, hk⟩

end NetBilinear

open NetBilinear

theorem solution {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (G : Network V A) (Itil : Finset V) (T : G.underlying.Subgraph)
    (hT : T.verts = (Itil : Set V)) (hTree : T.coe.IsTree) (l : A)
    (hl : Xor (G.tail l ∈ Itil) (G.head l ∈ Itil))
    (I1 I2 : Finset V) (hdisj : Disjoint I1 I2) (hunion : I1 ∪ I2 = Itil) :
    (G.head l ∈ Itil →
        G.IsECRAssignment l .pos (rowsWith .pos I1) (rowsWith .neg I2)) ∧
    (G.head l ∈ Itil →
        G.IsECRAssignment l .neg (rowsWith .neg I1) (rowsWith .pos I2)) ∧
    (G.tail l ∈ Itil →
        G.IsECRAssignment l .pos (rowsWith .neg I1) (rowsWith .pos I2)) ∧
    (G.tail l ∈ Itil →
        G.IsECRAssignment l .neg (rowsWith .pos I1) (rowsWith .neg I2)) := by
  have hhead : G.head l ∈ Itil → G.tail l ∉ Itil := by
    intro hh
    rcases hl with ⟨ht, hn⟩ | ⟨_, hn⟩
    · exact False.elim (hn hh)
    · exact hn
  have htail : G.tail l ∈ Itil → G.head l ∉ Itil := by
    intro ht
    rcases hl with ⟨_, hn⟩ | ⟨hh, hn⟩
    · exact hn
    · exact False.elim (hn ht)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hh
    simpa only [Sign.flip] using
      unit_assignment G Itil T hT hTree l hl I1 I2 hdisj hunion .pos .pos
        (by simp [hunion, hh, hhead hh, Sign.toReal])
  · intro hh
    simpa only [Sign.flip] using
      unit_assignment G Itil T hT hTree l hl I1 I2 hdisj hunion .neg .neg
        (by simp [hunion, hh, hhead hh, Sign.toReal])
  · intro ht
    simpa only [Sign.flip] using
      unit_assignment G Itil T hT hTree l hl I1 I2 hdisj hunion .pos .neg
        (by simp [hunion, ht, htail ht, Sign.toReal])
  · intro ht
    simpa only [Sign.flip] using
      unit_assignment G Itil T hT hTree l hl I1 I2 hdisj hunion .neg .pos
        (by simp [hunion, ht, htail ht, Sign.toReal])

#print axioms solution
