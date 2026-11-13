-- Prove2me | solution 1 for LowDiameterNashWilliams.Main.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T19:19:20.959957+00:00
-- url     : https://prove2.me/submissions/cfb337db-1f5e-4377-a242-013c30dd2341

import Mathlib
import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Definitions.Def_LowDiameterNashWilliams_Main_Geometry
import Theorems.Thm_LowDiameterNashWilliams_Main_lemma_3_2

section
set_option autoImplicit false
open Classical
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn
namespace LowDiameterNashWilliams.Dev.Forest

theorem edgeGraph_mono {V E : Type*} [DecidableEq E] (ends : E → Sym2 V) {F F' : Finset E} (h : F ⊆ F') :
    edgeGraph ends F ≤ edgeGraph ends F' := by
  unfold edgeGraph
  apply SimpleGraph.fromEdgeSet_mono
  exact Set.image_mono (by exact_mod_cast h)

theorem isForest_mono {V E : Type*} [DecidableEq E] (ends : E → Sym2 V) {F F' : Finset E} (h : F ⊆ F')
    (hF : IsForest ends F') : IsForest ends F := by
  intro e he u v huv hr
  exact hF e (h he) u v huv
    (hr.mono (edgeGraph_mono ends (Finset.erase_subset_erase e h)))

theorem forest_nondiag {V E : Type*} [DecidableEq E] (ends : E → Sym2 V) {F : Finset E}
    (hF : IsForest ends F) : ∀ e ∈ F, ¬ (ends e).IsDiag := by
  intro e he hd
  obtain ⟨u, v, huv⟩ : ∃ u v, ends e = s(u, v) := by
    induction h' : ends e using Sym2.ind with
    | _ u v => exact ⟨u, v, rfl⟩
  rw [huv, Sym2.mk_isDiag_iff] at hd
  subst hd
  exact hF e he u u huv (SimpleGraph.Reachable.refl _)

theorem forest_inj {V E : Type*} [DecidableEq E] (ends : E → Sym2 V) {F : Finset E}
    (hF : IsForest ends F) : Set.InjOn ends (F : Set E) := by
  intro e he e' he' h
  by_contra hne
  have hnd := forest_nondiag ends hF e he
  obtain ⟨u, v, huv⟩ : ∃ u v, ends e = s(u, v) := by
    induction h' : ends e using Sym2.ind with
    | _ u v => exact ⟨u, v, rfl⟩
  apply hF e he u v huv
  have hne' : u ≠ v := by
    intro h2; apply hnd; rw [huv, h2]; simp
  apply SimpleGraph.Adj.reachable
  unfold edgeGraph
  rw [SimpleGraph.fromEdgeSet_adj]
  refine ⟨⟨e', ?_, ?_⟩, hne'⟩
  · simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
    exact ⟨he', fun h3 => hne h3.symm⟩
  · rw [← h, huv]

theorem acyc_card {V : Type*} [Fintype V] [Nonempty V] (H : SimpleGraph V) [Fintype H.edgeSet] (hH : H.IsAcyclic) :
    H.edgeFinset.card + 1 ≤ Fintype.card V := by
  obtain ⟨F, hle, -, hT⟩ := (SimpleGraph.connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic
    (le_top : H ≤ ⊤) hH
  have := hT.card_edgeFinset
  have : H.edgeFinset.card ≤ F.edgeFinset.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [SimpleGraph.mem_edgeFinset] at hx ⊢
    exact SimpleGraph.edgeSet_mono ‹H ≤ F› hx
  omega

theorem inner_card_lt {n m : ℕ} (ends : Fin m → Sym2 (Fin n)) (T : Finset (Fin m))
    (hT : IsSpanningTree ends T) (A : Finset (Fin n)) (hA : A.Nonempty) :
    (T.filter fun e => ∀ v ∈ ends e, v ∈ A).card < A.card := by
  set F := T.filter fun e => ∀ v ∈ ends e, v ∈ A with hFdef
  have hTf : IsForest ends T := hT.2.2.2.1
  have hF : IsForest ends F := isForest_mono ends (Finset.filter_subset _ _) hTf
  have hnd := forest_nondiag ends hF
  have hinj := forest_inj ends hF
  set G := edgeGraph ends F with hG
  have hGe : G.edgeSet = ends '' (F : Set (Fin m)) := by
    rw [hG, edgeGraph, SimpleGraph.edgeSet_fromEdgeSet]
    ext x
    simp only [Set.mem_sdiff, Set.mem_image, Finset.mem_coe]
    constructor
    · exact fun h => h.1
    · rintro ⟨e, he, rfl⟩; exact ⟨⟨e, he, rfl⟩, hnd e he⟩
  have hcard : G.edgeFinset.card = F.card := by
    have : G.edgeFinset = F.image ends := by
      ext x
      rw [SimpleGraph.mem_edgeFinset, hGe]; simp
    rw [this, Finset.card_image_of_injOn hinj]
  have hac : G.IsAcyclic := by
    rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
    intro v w hvw
    have hvw' := hvw
    rw [hG, edgeGraph, SimpleGraph.fromEdgeSet_adj] at hvw'
    obtain ⟨⟨e', he', hee'⟩, hne⟩ := hvw'
    rw [SimpleGraph.isBridge_iff]
    intro hr
    apply hF e' he' v w hee'
    refine hr.mono ?_
    intro a b hab
    rw [SimpleGraph.deleteEdges_adj] at hab
    obtain ⟨hab1, hab2⟩ := hab
    have hab1' := hab1
    rw [hG, edgeGraph, SimpleGraph.fromEdgeSet_adj] at hab1'
    obtain ⟨⟨f, hf, hfab⟩, hne2⟩ := hab1'
    unfold edgeGraph
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨f, ?_, hfab⟩, hne2⟩
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
    refine ⟨hf, fun hfe => hab2 ?_⟩
    rw [← hfab, hfe, hee']
    rfl
  have hsupp : G.support ⊆ (A : Set (Fin n)) := by
    rintro v ⟨w, hvw⟩
    have hvw : G.Adj v w := hvw
    rw [hG, edgeGraph, SimpleGraph.fromEdgeSet_adj] at hvw
    obtain ⟨⟨f, hf, hfe⟩, -⟩ := hvw
    have hfF := Finset.mem_coe.mp hf
    rw [hFdef, Finset.mem_filter] at hfF
    exact hfF.2 v (by rw [hfe]; simp)
  have hind := SimpleGraph.card_edgeFinset_induce_of_support_subset hsupp
  have hac2 := hac.induce (A : Set (Fin n))
  have : Nonempty (A : Set (Fin n)) := hA.coe_sort
  have := acyc_card _ hac2
  have hc : Fintype.card (A : Set (Fin n)) = A.card := Fintype.card_coe A
  rw [← hcard]
  rw [hc] at this
  have h5 : G.edgeFinset.card + 1 ≤ A.card := by
    convert this using 2
    convert hind.symm
  omega

end LowDiameterNashWilliams.Dev.Forest
end

section
set_option autoImplicit false
open scoped BigOperators
namespace LowDiameterNashWilliams.Dev.Laminar

end LowDiameterNashWilliams.Dev.Laminar
end

section
set_option autoImplicit false
open scoped BigOperators
open Classical
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Dev.L32
open LowDiameterNashWilliams.Main

variable {n m k : ℕ}

structure Hyp {n m k : ℕ} (ends : Fin m → Sym2 (Fin n)) (T : Trees k m)
    (D : Fin k → Direction n m) (r : Fin n) : Prop where
  simple : Simple ends
  part : TreePartition ends T
  toward : ∀ i, Toward ends (T i) (D i) r

theorem sum_fiber (F : Finset (Fin m)) (f : Fin m → Fin n) (A : Finset (Fin n)) (P : Fin m → Prop) :
    ∑ v ∈ A, (F.filter fun e => f e = v ∧ P e).card
      = (F.filter fun e => f e ∈ A ∧ P e).card := by
  have := Finset.card_eq_sum_card_fiberwise (s := F.filter fun e => f e ∈ A ∧ P e) (f := f)
    (t := A) (fun e he => (Finset.mem_filter.mp he).2.1)
  rw [this]
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, hf, hP⟩
    exact ⟨⟨he, hf ▸ hv, hP⟩, hf⟩
  · rintro ⟨⟨he, _, hP⟩, hf⟩
    exact ⟨he, hf, hP⟩

theorem inner_iff {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (i : Fin k) {e : Fin m} (he : e ∈ T i) (A : Finset (Fin n)) :
    (∀ v ∈ ends e, v ∈ A) ↔ ((D i e).1 ∈ A ∧ (D i e).2 ∈ A) := by
  have := (h.toward i).1 e he
  rw [this]
  simp [Sym2.mem_iff]

theorem tail_card {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (i : Fin k) (A : Finset (Fin n)) :
    ((T i).filter fun e => (D i e).1 ∈ A).card + (if r ∈ A then 1 else 0) = A.card := by
  have h1 := sum_fiber (T i) (fun e => (D i e).1) A (fun _ => True)
  simp only [and_true] at h1
  rw [← h1]
  have h2 : ∀ v ∈ A, ((T i).filter fun e => (D i e).1 = v).card = if v = r then 0 else 1 := by
    intro v _
    by_cases hv : v = r
    · subst hv; rw [if_pos rfl]; exact (h.toward i).2.1
    · rw [if_neg hv]; exact (h.toward i).2.2 v hv
  rw [Finset.sum_congr rfl h2]
  rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, smul_eq_mul, mul_one, zero_add]
  have : (A.filter fun v => ¬ v = r) = A.erase r := by
    ext v; simp [Finset.mem_erase, and_comm]
  rw [this]
  by_cases hr : r ∈ A
  · rw [Finset.card_erase_of_mem hr, if_pos hr]
    have := Finset.card_pos.mpr ⟨r, hr⟩
    omega
  · rw [Finset.erase_eq_of_notMem hr, if_neg hr]; rfl

/-- inner edges of tree `i` -/
def inner (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (i : Fin k) (A : Finset (Fin n)) : ℕ :=
  ((T i).filter fun e => ∀ v ∈ ends e, v ∈ A).card

theorem inner_lt {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (i : Fin k) (A : Finset (Fin n)) (hA : A.Nonempty) :
    inner ends T i A < A.card :=
  LowDiameterNashWilliams.Dev.Forest.inner_card_lt ends (T i) (h.part.1.1 i) A hA

theorem cover {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (e : Fin m) : ∃ i, e ∈ T i := by
  have : e ∈ Finset.univ.biUnion T := by rw [h.part.2]; exact Finset.mem_univ e
  simpa using this

theorem edgeCount_eq {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (A : Finset (Fin n)) :
    (edgesIn ends A).card = ∑ i, inner ends T i A := by
  have : edgesIn ends A = Finset.univ.biUnion fun i => (T i).filter fun e => ∀ v ∈ ends e, v ∈ A := by
    ext e
    simp only [edgesIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro he
      obtain ⟨i, hi⟩ := cover h e
      exact ⟨i, hi, he⟩
    · rintro ⟨i, _, he⟩
      exact he
  rw [this, Finset.card_biUnion]
  · rfl
  · intro i _ j _ hij
    exact Finset.disjoint_filter_filter (h.part.1.2 i j hij)

theorem edgeCount_add_le {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (A : Finset (Fin n)) (hA : A.Nonempty) :
    (edgesIn ends A).card + k ≤ k * A.card := by
  rw [edgeCount_eq h]
  have : ∀ i ∈ (Finset.univ : Finset (Fin k)), inner ends T i A + 1 ≤ A.card :=
    fun i _ => inner_lt h i A hA
  have h2 := Finset.sum_le_sum this
  rw [Finset.sum_add_distrib] at h2
  simpa using h2

theorem tight_iff (ends : Fin m → Sym2 (Fin n)) (A : Finset (Fin n)) :
    tight ends k A ↔ A.Nonempty ∧ (edgesIn ends A).card + k = k * A.card := by
  unfold tight
  constructor
  · rintro ⟨hA, he⟩
    refine ⟨hA, ?_⟩
    have hc := Finset.card_pos.mpr hA
    have : (((edgesIn ends A).card + k : ℕ) : ℤ) = ((k * A.card : ℕ) : ℤ) := by
      push_cast; rw [he]; ring
    exact_mod_cast this
  · rintro ⟨hA, he⟩
    refine ⟨hA, ?_⟩
    have : (((edgesIn ends A).card + k : ℕ) : ℤ) = ((k * A.card : ℕ) : ℤ) := by rw [he]
    push_cast at this
    linarith

end LowDiameterNashWilliams.Dev.L32
end

section
set_option autoImplicit false
open scoped BigOperators
open Classical
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Dev.L32
open LowDiameterNashWilliams.Main

variable {n m k : ℕ}

theorem outgoingTo_le_card {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (v : Fin n) (S : Finset (Fin n)) :
    outgoingTo T D v S ≤ S.card := by
  unfold outgoingTo
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun x => (D x.1 x.2).2)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter] at hx
    exact hx.2.2.2
  · rintro ⟨i, e⟩ hx ⟨i', e'⟩ hx' hxx
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx hx'
    have h1 := (h.toward i).1 e hx.1
    have h2 := (h.toward i').1 e' hx'.1
    have hxx' : (D i e).2 = (D i' e').2 := hxx
    rw [hx.2.1, hxx'] at h1
    rw [hx'.2.1] at h2
    have he : e = e' := h.simple.1 (h1.trans h2.symm)
    subst he
    by_cases hi : i = i'
    · subst hi; rfl
    · exact absurd (Finset.disjoint_left.mp (h.part.1.2 i i' hi) hx.1) (not_not.mpr hx'.1)

end LowDiameterNashWilliams.Dev.L32
end

section
/-! Lemma 3.3, part A: reachability, connected components as vertex sets, the component
count bound `n ≤ |A| + c(A)`, forest insertion, and the Kruskal tree: for integer weights
`0 ≤ f < N` there is a spanning tree `B` such that, for every threshold `j`, the edges of `B`
of weight `≥ j` connect everything that the edges of `G` of weight `≥ j` connect. -/

set_option autoImplicit false
open Classical
open scoped BigOperators
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L33
open LowDiameterNashWilliams.Main

variable {n m : ℕ}

/-- reachability by `F`-edges -/
abbrev Rch (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) (a b : Fin n) : Prop :=
  (edgeGraph ends F).Reachable a b

theorem exists_ends (ends : Fin m → Sym2 (Fin n)) (e : Fin m) : ∃ u v, ends e = s(u, v) := by
  induction h' : ends e using Sym2.ind with
  | _ u v => exact ⟨u, v, rfl⟩

theorem adj_iff (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) (a b : Fin n) :
    (edgeGraph ends F).Adj a b ↔ (∃ e ∈ F, ends e = s(a, b)) ∧ a ≠ b := by
  unfold edgeGraph
  rw [SimpleGraph.fromEdgeSet_adj]
  simp [Set.mem_image]

theorem rch_of_edge (ends : Fin m → Sym2 (Fin n)) {F : Finset (Fin m)} {e : Fin m} (he : e ∈ F)
    {a b : Fin n} (hab : ends e = s(a, b)) : Rch ends F a b := by
  by_cases h : a = b
  · subst h; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ((adj_iff ends F a b).2 ⟨⟨e, he, hab⟩, h⟩)

theorem rch_mono (ends : Fin m → Sym2 (Fin n)) {F F' : Finset (Fin m)} (h : F ⊆ F') {a b : Fin n}
    (hr : Rch ends F a b) : Rch ends F' a b :=
  hr.mono (LowDiameterNashWilliams.Dev.Forest.edgeGraph_mono ends h)

/-- `B` connects the ends of every edge of `F` -/
def Spans (ends : Fin m → Sym2 (Fin n)) (B F : Finset (Fin m)) : Prop :=
  ∀ e ∈ F, ∀ a b, ends e = s(a, b) → Rch ends B a b

theorem spans_mono (ends : Fin m → Sym2 (Fin n)) {B B' F : Finset (Fin m)} (h : B ⊆ B')
    (hs : Spans ends B F) : Spans ends B' F :=
  fun e he a b hab => rch_mono ends h (hs e he a b hab)

theorem rch_lift (ends : Fin m → Sym2 (Fin n)) {B F : Finset (Fin m)} (hs : Spans ends B F)
    {x y : Fin n} (h : Rch ends F x y) : Rch ends B x y := by
  rw [Rch, SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hbc ih =>
    obtain ⟨⟨e, he, hee⟩, -⟩ := (adj_iff ends F _ _).1 hbc
    exact ih.trans (hs e he _ _ hee)

theorem rch_insert (ends : Fin m → Sym2 (Fin n)) {S : Finset (Fin m)} {e : Fin m} {u v : Fin n}
    (huv : ends e = s(u, v)) {x y : Fin n} (h : Rch ends (insert e S) x y) :
    Rch ends S x y ∨ ((Rch ends S x u ∨ Rch ends S x v) ∧ (Rch ends S y u ∨ Rch ends S y v)) := by
  rw [Rch, SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl (SimpleGraph.Reachable.refl _)
  | @tail b c _ hbc ih =>
    obtain ⟨⟨g, hg, hgbc⟩, -⟩ := (adj_iff ends _ _ _).1 hbc
    rcases Finset.mem_insert.1 hg with rfl | hg
    · rw [huv, Sym2.eq_iff] at hgbc
      have hc : Rch ends S c u ∨ Rch ends S c v := by
        rcases hgbc with ⟨-, h2⟩ | ⟨h1, -⟩
        · rw [h2]; exact Or.inr (SimpleGraph.Reachable.refl _)
        · rw [h1]; exact Or.inl (SimpleGraph.Reachable.refl _)
      rcases ih with hxb | ⟨hx, -⟩
      · right
        refine ⟨?_, hc⟩
        rcases hgbc with ⟨h1, -⟩ | ⟨-, h2⟩
        · rw [h1]; exact Or.inl hxb
        · rw [h2]; exact Or.inr hxb
      · exact Or.inr ⟨hx, hc⟩
    · have hbc' : Rch ends S b c := rch_of_edge ends hg hgbc
      rcases ih with hxb | ⟨hx, hb⟩
      · exact Or.inl (hxb.trans hbc')
      · right
        refine ⟨hx, ?_⟩
        rcases hb with hb | hb
        · exact Or.inl (hbc'.symm.trans hb)
        · exact Or.inr (hbc'.symm.trans hb)

/-! ### Components as vertex sets -/

noncomputable def cc (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) (v : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun x => Rch ends F v x

noncomputable def comps (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) :
    Finset (Finset (Fin n)) :=
  Finset.univ.image (cc ends F)

theorem mem_cc (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) (v x : Fin n) :
    x ∈ cc ends F v ↔ Rch ends F v x := by
  simp [cc]

theorem self_mem_cc (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) (v : Fin n) :
    v ∈ cc ends F v := (mem_cc ends F v v).2 (SimpleGraph.Reachable.refl _)

theorem cc_eq_iff (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) (v x : Fin n) :
    cc ends F v = cc ends F x ↔ Rch ends F v x := by
  constructor
  · intro h
    have := self_mem_cc ends F x
    rw [← h, mem_cc] at this
    exact this
  · intro h
    ext y
    rw [mem_cc, mem_cc]
    exact ⟨fun hy => h.symm.trans hy, fun hy => h.trans hy⟩

theorem cc_eq_of_mem (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) {v x : Fin n}
    (h : x ∈ cc ends F v) : cc ends F x = cc ends F v :=
  ((cc_eq_iff ends F v x).2 ((mem_cc ends F v x).1 h)).symm

theorem mem_comps (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) (S : Finset (Fin n)) :
    S ∈ comps ends F ↔ ∃ v, cc ends F v = S := by
  simp [comps]

theorem rch_empty (ends : Fin m → Sym2 (Fin n)) {x y : Fin n} (h : Rch ends ∅ x y) : x = y := by
  rw [Rch, SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hbc _ =>
    obtain ⟨⟨e, he, -⟩, -⟩ := (adj_iff ends _ _ _).1 hbc
    simp at he

theorem card_comps_empty (ends : Fin m → Sym2 (Fin n)) : (comps ends ∅).card = n := by
  unfold comps
  rw [Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    exact rch_empty ends ((cc_eq_iff ends ∅ x y).1 hxy)

theorem card_comps_insert (ends : Fin m → Sym2 (Fin n)) (A : Finset (Fin m)) (e : Fin m) :
    (comps ends A).card ≤ (comps ends (insert e A)).card + 1 := by
  obtain ⟨u, v, huv⟩ := exists_ends ends e
  set A' := insert e A with hA'
  have hsub : A ⊆ A' := Finset.subset_insert e A
  let Φ : Finset (Fin n) → Finset (Fin n) := fun S =>
    Finset.univ.filter fun y => ∃ x ∈ S, Rch ends A' x y
  have hΦ : ∀ x, Φ (cc ends A x) = cc ends A' x := by
    intro x
    ext y
    simp only [Φ, Finset.mem_filter, Finset.mem_univ, true_and, mem_cc]
    constructor
    · rintro ⟨z, hz, hzy⟩
      exact (rch_mono ends hsub hz).trans hzy
    · intro h
      exact ⟨x, SimpleGraph.Reachable.refl _, h⟩
  have h1 : ((comps ends A).erase (cc ends A u)).card ≤ (comps ends A').card := by
    apply Finset.card_le_card_of_injOn Φ
    · intro S hS
      rw [Finset.mem_coe, Finset.mem_erase, mem_comps] at hS
      obtain ⟨-, x, rfl⟩ := hS
      rw [Finset.mem_coe, hΦ, mem_comps]
      exact ⟨x, rfl⟩
    · intro S hS S' hS' hSS
      rw [Finset.mem_coe, Finset.mem_erase, mem_comps] at hS hS'
      obtain ⟨hne, x, rfl⟩ := hS
      obtain ⟨hne', y, rfl⟩ := hS'
      rw [hΦ, hΦ, cc_eq_iff] at hSS
      rw [cc_eq_iff]
      rcases rch_insert ends huv hSS with h | ⟨hx, hy⟩
      · exact h
      · have hx' : Rch ends A x v := by
          rcases hx with hx | hx
          · exact absurd ((cc_eq_iff ends A x u).2 hx) hne
          · exact hx
        have hy' : Rch ends A y v := by
          rcases hy with hy | hy
          · exact absurd ((cc_eq_iff ends A y u).2 hy) hne'
          · exact hy
        exact hx'.trans hy'.symm
  have h2 := Finset.pred_card_le_card_erase (s := comps ends A) (a := cc ends A u)
  omega

/-- every edge reduces the number of components by at most one -/
theorem le_card_add_comps (ends : Fin m → Sym2 (Fin n)) (A : Finset (Fin m)) :
    n ≤ A.card + (comps ends A).card := by
  induction A using Finset.induction_on with
  | empty => simp [card_comps_empty]
  | insert e A he ih =>
    have := card_comps_insert ends A e
    rw [Finset.card_insert_of_notMem he]
    omega

theorem cc_eq_of_spans (ends : Fin m → Sym2 (Fin n)) {B F : Finset (Fin m)} (hBF : B ⊆ F)
    (hs : Spans ends B F) (v : Fin n) : cc ends B v = cc ends F v := by
  ext x
  rw [mem_cc, mem_cc]
  exact ⟨rch_mono ends hBF, rch_lift ends hs⟩

theorem comps_eq_of_spans (ends : Fin m → Sym2 (Fin n)) {B F : Finset (Fin m)} (hBF : B ⊆ F)
    (hs : Spans ends B F) : comps ends B = comps ends F := by
  unfold comps
  congr 1
  funext v
  exact cc_eq_of_spans ends hBF hs v

/-- rank bound: a subset spanning `F` has at least `n - c(F)` edges -/
theorem rank_le (ends : Fin m → Sym2 (Fin n)) {B F : Finset (Fin m)} (hBF : B ⊆ F)
    (hs : Spans ends B F) : n ≤ B.card + (comps ends F).card := by
  rw [← comps_eq_of_spans ends hBF hs]
  exact le_card_add_comps ends B

/-! ### Forests -/

theorem isForest_empty (ends : Fin m → Sym2 (Fin n)) : IsForest ends ∅ := by
  intro e he; simp at he

theorem isForest_insert (ends : Fin m → Sym2 (Fin n)) {B : Finset (Fin m)} (hB : IsForest ends B)
    {e : Fin m} (he : e ∉ B) {u v : Fin n} (huv : ends e = s(u, v)) (hr : ¬ Rch ends B u v) :
    IsForest ends (insert e B) := by
  intro g hg a b hab hreach
  by_cases hge : g = e
  · subst hge
    rw [Finset.erase_insert he] at hreach
    rw [huv, Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hr hreach
    · exact hr hreach.symm
  · have hgB : g ∈ B := (Finset.mem_insert.1 hg).resolve_left hge
    rw [Finset.erase_insert_of_ne (Ne.symm hge)] at hreach
    have hSB : B.erase g ⊆ B := Finset.erase_subset g B
    have hab' : Rch ends B a b := rch_of_edge ends hgB hab
    have hf := hB g hgB a b hab
    rcases rch_insert ends huv hreach with h | ⟨ha, hb⟩
    · exact hf h
    · rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hf (ha.trans hb.symm)
      · exact hr ((rch_mono ends hSB ha).symm.trans (hab'.trans (rch_mono ends hSB hb)))
      · exact hr ((rch_mono ends hSB hb).symm.trans (hab'.symm.trans (rch_mono ends hSB ha)))
      · exact hf (ha.trans hb.symm)

theorem extend (ends : Fin m → Sym2 (Fin n)) {A F : Finset (Fin m)} (hA : IsForest ends A)
    (hAF : A ⊆ F) : ∃ B, A ⊆ B ∧ B ⊆ F ∧ IsForest ends B ∧ Spans ends B F := by
  set P := F.powerset.filter fun B => A ⊆ B ∧ IsForest ends B with hP
  have hAP : A ∈ P := by
    rw [hP, Finset.mem_filter, Finset.mem_powerset]; exact ⟨hAF, le_refl _, hA⟩
  obtain ⟨B, hB, hmax⟩ := Finset.exists_max_image P Finset.card ⟨A, hAP⟩
  rw [hP, Finset.mem_filter, Finset.mem_powerset] at hB
  refine ⟨B, hB.2.1, hB.1, hB.2.2, ?_⟩
  intro e heF a b hab
  by_cases heB : e ∈ B
  · exact rch_of_edge ends heB hab
  by_contra hn
  have hins : insert e B ∈ P := by
    rw [hP, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset heF hB.1, hB.2.1.trans (Finset.subset_insert e B), ?_⟩
    exact isForest_insert ends hB.2.2 heB hab hn
  have := hmax _ hins
  rw [Finset.card_insert_of_notMem heB] at this
  omega

/-! ### Thresholds and the Kruskal tree -/

/-- edges of weight at least `j` -/
noncomputable def Gt (f : Fin m → ℤ) (j : ℤ) : Finset (Fin m) :=
  Finset.univ.filter fun e => j ≤ f e

theorem Gt_anti (f : Fin m → ℤ) {i j : ℤ} (h : i ≤ j) : Gt f j ⊆ Gt f i := by
  intro e he
  simp only [Gt, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  omega

theorem kchain (ends : Fin m → Sym2 (Fin n)) (f : Fin m → ℤ) (N : ℕ) (hfN : ∀ e, f e < N) :
    ∀ d : ℕ, ∃ B, IsForest ends B ∧ B ⊆ Gt f ((N - d : ℕ) : ℤ) ∧
      ∀ j : ℕ, N - d ≤ j → Spans ends (B.filter fun e => (j : ℤ) ≤ f e) (Gt f j) := by
  intro d
  induction d with
  | zero =>
    refine ⟨∅, isForest_empty ends, Finset.empty_subset _, ?_⟩
    intro j hj e he
    simp only [Gt, Finset.mem_filter, Finset.mem_univ, true_and] at he
    have := hfN e
    omega
  | succ d ih =>
    obtain ⟨B, hB, hBG, hsp⟩ := ih
    have hmono : Gt f ((N - d : ℕ) : ℤ) ⊆ Gt f ((N - (d + 1) : ℕ) : ℤ) :=
      Gt_anti f (by omega)
    obtain ⟨B', hBB', hB'G, hB', hsp'⟩ := extend ends hB (hBG.trans hmono)
    refine ⟨B', hB', hB'G, ?_⟩
    intro j hj
    by_cases hj' : N - d ≤ j
    · exact spans_mono ends (Finset.filter_subset_filter _ hBB') (hsp j hj')
    · have hjeq : j = N - (d + 1) := by omega
      subst hjeq
      have : (B'.filter fun e => ((N - (d + 1) : ℕ) : ℤ) ≤ f e) = B' := by
        apply Finset.filter_true_of_mem
        intro e he
        have := hB'G he
        simp only [Gt, Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this
      rw [this]
      exact hsp'

theorem kruskal (ends : Fin m → Sym2 (Fin n)) (hn : 0 < n)
    (hconn : ∀ a b, Rch ends Finset.univ a b) (f : Fin m → ℤ) (hf0 : ∀ e, 0 ≤ f e)
    (N : ℕ) (hfN : ∀ e, f e < N) :
    ∃ B, IsSpanningTree ends B ∧
      ∀ j : ℕ, Spans ends (B.filter fun e => (j : ℤ) ≤ f e) (Gt f j) := by
  obtain ⟨B, hB, -, hsp⟩ := kchain ends f N hfN N
  refine ⟨B, ?_, fun j => hsp j (by omega)⟩
  have h0 := hsp 0 (by omega)
  have hfil : (B.filter fun e => ((0 : ℕ) : ℤ) ≤ f e) = B :=
    Finset.filter_true_of_mem (fun e _ => by simpa using hf0 e)
  have hG0 : Gt f ((0 : ℕ) : ℤ) = Finset.univ :=
    Finset.filter_true_of_mem (fun e _ => by simpa using hf0 e)
  rw [hfil, hG0] at h0
  refine ⟨Finset.subset_univ _, ⟨⟨0, hn⟩, Finset.mem_univ _⟩, fun _ _ _ _ => Finset.mem_univ _,
    hB, fun a _ b _ => rch_lift ends h0 (hconn a b)⟩

/-- threshold expansion of a weight -/
theorem weight_eq_sum (f : Fin m → ℤ) (M : ℕ) (hf0 : ∀ e, 0 ≤ f e) (hfM : ∀ e, f e ≤ M)
    (B : Finset (Fin m)) :
    weight f B = ∑ i ∈ Finset.range M, ((B.filter fun e => ((i + 1 : ℕ) : ℤ) ≤ f e).card : ℤ) := by
  unfold weight
  have : ∀ i ∈ Finset.range M, ((B.filter fun e => ((i + 1 : ℕ) : ℤ) ≤ f e).card : ℤ)
      = ∑ e ∈ B, if ((i + 1 : ℕ) : ℤ) ≤ f e then (1 : ℤ) else 0 := by
    intro i _
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hfil : (Finset.range M).filter (fun i : ℕ => ((i + 1 : ℕ) : ℤ) ≤ f e)
      = Finset.range (f e).toNat := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    have := hf0 e
    have := hfM e
    omega
  rw [hfil, Finset.card_range]
  have := hf0 e
  omega

/-! ### Spanning trees -/

theorem connected_of_tree (ends : Fin m → Sym2 (Fin n)) {T : Finset (Fin m)}
    (hT : IsSpanningTree ends T) (a b : Fin n) : Rch ends T a b :=
  hT.2.2.2.2 a (Finset.mem_univ _) b (Finset.mem_univ _)

theorem tree_card (ends : Fin m → Sym2 (Fin n)) {T : Finset (Fin m)}
    (hT : IsSpanningTree ends T) : T.card + 1 = n := by
  have h1 := LowDiameterNashWilliams.Dev.Forest.inner_card_lt ends T hT Finset.univ
    hT.2.1
  have hfil : (T.filter fun e => ∀ v ∈ ends e, v ∈ (Finset.univ : Finset (Fin n))) = T :=
    Finset.filter_true_of_mem (fun _ _ _ _ => Finset.mem_univ _)
  rw [hfil, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := le_card_add_comps ends T
  have h3 : (comps ends T).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro S hS S' hS'
    rw [mem_comps] at hS hS'
    obtain ⟨x, rfl⟩ := hS
    obtain ⟨y, rfl⟩ := hS'
    exact (cc_eq_iff ends T x y).2 (connected_of_tree ends hT x y)
  omega

theorem le_maxTreeWeight (ends : Fin m → Sym2 (Fin n)) (f : Fin m → ℤ) {B : Finset (Fin m)}
    (hB : IsSpanningTree ends B) : weight f B ≤ maxTreeWeight ends f := by
  unfold maxTreeWeight
  have hmem : weight f B ∈ ((Finset.univ : Edges m).powerset.filter (IsSpanningTree ends)).image
      (weight f) := by
    apply Finset.mem_image_of_mem
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ _, hB⟩
  dsimp only
  rw [dif_pos ⟨_, hmem⟩]
  exact Finset.le_max' _ _ hmem

end LowDiameterNashWilliams.Main.Dev.L33
end

section
/-! Lemma 3.3, part B: sums over components, the potential `Ψ` and the splitting inequality.

`ψ(U) = 1` if `U` is large (`|U| ≥ k/8` or `U` meets `R`), and `ψ(U) = 8|U|/k` otherwise;
`Ψ(F) = Σ_{components C of F} ψ(C)`. When the components of `F' ⊆ F` refine a component `C` of
`F` with `b` large pieces, `max(b - 1, 0) ≤ Σ_pieces ψ - ψ(C)`. Also `0 ≤ Ψ ≤ 8n/k + |R|`. -/

set_option autoImplicit false
open Classical
open scoped BigOperators
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L33
open LowDiameterNashWilliams.Main

variable {n m : ℕ}

theorem cc_card_pos (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) (x : Fin n) :
    (0 : ℝ) < (cc ends F x).card := by
  exact_mod_cast Finset.card_pos.2 ⟨x, self_mem_cc ends F x⟩

/-- sum over the components meeting a closed set `s` -/
theorem sum_image_cc (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) (s : Finset (Fin n))
    (hs : ∀ x ∈ s, ∀ y, Rch ends F x y → y ∈ s) (φ : Finset (Fin n) → ℝ) :
    ∑ U ∈ s.image (cc ends F), φ U = ∑ x ∈ s, φ (cc ends F x) / (cc ends F x).card := by
  apply Finset.sum_image'
  intro x hx
  have hfib : s.filter (fun y => cc ends F y = cc ends F x) = cc ends F x := by
    ext y
    simp only [Finset.mem_filter, cc_eq_iff, mem_cc]
    constructor
    · rintro ⟨_, h⟩; exact h.symm
    · intro h; exact ⟨hs x hx y h, h.symm⟩
  have hc : ∀ y ∈ s.filter (fun y => cc ends F y = cc ends F x),
      φ (cc ends F y) / (cc ends F y).card = φ (cc ends F x) / (cc ends F x).card :=
    fun y hy => by rw [(Finset.mem_filter.1 hy).2]
  rw [Finset.sum_congr rfl hc, hfib, Finset.sum_const, nsmul_eq_mul]
  have := cc_card_pos ends F x
  field_simp

theorem sum_comps (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) (g : Fin n → ℝ) :
    ∑ C ∈ comps ends F, ∑ x ∈ C, g x = ∑ x, g x := by
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true, mem_comps]
    exact ⟨_, ⟨x, rfl⟩, self_mem_cc ends F x⟩
  · intro C hC C' hC' hne
    rw [Finset.mem_coe, mem_comps] at hC hC'
    obtain ⟨a, rfl⟩ := hC
    obtain ⟨b, rfl⟩ := hC'
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxa hxb
    apply hne
    rw [← cc_eq_of_mem ends F hxa, ← cc_eq_of_mem ends F hxb]

theorem comps_closed (ends : Fin m → Sym2 (Fin n)) {F F' : Finset (Fin m)} (h : F' ⊆ F)
    {C : Finset (Fin n)} (hC : C ∈ comps ends F) :
    ∀ x ∈ C, ∀ y, Rch ends F' x y → y ∈ C := by
  rw [mem_comps] at hC
  obtain ⟨z, rfl⟩ := hC
  intro x hx y hxy
  rw [mem_cc] at hx ⊢
  exact hx.trans (rch_mono ends h hxy)

/-- the pieces of all components of `F` are the components of `F' ⊆ F` -/
theorem sum_imgs (ends : Fin m → Sym2 (Fin n)) {F F' : Finset (Fin m)} (h : F' ⊆ F)
    (φ : Finset (Fin n) → ℝ) :
    ∑ C ∈ comps ends F, ∑ U ∈ C.image (cc ends F'), φ U = ∑ U ∈ comps ends F', φ U := by
  rw [Finset.sum_congr rfl (fun C hC => sum_image_cc ends F' C (comps_closed ends h hC) φ),
    sum_comps]
  unfold comps
  rw [sum_image_cc ends F' Finset.univ (fun _ _ _ _ => Finset.mem_univ _)]

/-! ### The potential -/

def Large (k : ℕ) (R : Finset (Fin n)) (U : Finset (Fin n)) : Prop :=
  (k : ℝ) / 8 ≤ U.card ∨ (U ∩ R).Nonempty

noncomputable def psi (k : ℕ) (R : Finset (Fin n)) (U : Finset (Fin n)) : ℝ :=
  if Large k R U then 1 else 8 * U.card / k

noncomputable def Psi (ends : Fin m → Sym2 (Fin n)) (k : ℕ) (R : Finset (Fin n))
    (F : Finset (Fin m)) : ℝ :=
  ∑ C ∈ comps ends F, psi k R C

theorem large_mono {k : ℕ} {R U V : Finset (Fin n)} (h : U ⊆ V) (hU : Large k R U) :
    Large k R V := by
  rcases hU with hU | hU
  · left
    have : (U.card : ℝ) ≤ V.card := by exact_mod_cast Finset.card_le_card h
    linarith
  · right
    exact hU.mono (Finset.inter_subset_inter_right h)

theorem psi_nonneg (k : ℕ) (R U : Finset (Fin n)) : 0 ≤ psi k R U := by
  unfold psi
  split_ifs
  · norm_num
  · positivity

theorem psi_le {k : ℕ} (hk : 0 < k) (R U : Finset (Fin n)) :
    psi k R U ≤ ∑ x ∈ U, ((8 : ℝ) / k + if x ∈ R then 1 else 0) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_boole]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hR0 : (0 : ℝ) ≤ ((U.filter fun x => x ∈ R).card : ℝ) := by positivity
  have h8 : (U.card : ℝ) * (8 / k) = 8 * U.card / k := by ring
  unfold psi
  split_ifs with hL
  · rcases hL with hL | hL
    · have : (1 : ℝ) ≤ 8 * U.card / k := by
        rw [le_div_iff₀ hkpos]; linarith
      linarith
    · have : (1 : ℝ) ≤ ((U.filter fun x => x ∈ R).card : ℝ) := by
        have : (U.filter fun x => x ∈ R).Nonempty := by
          rw [Finset.filter_mem_eq_inter]; exact hL
        exact_mod_cast Finset.card_pos.2 this
      have : (0 : ℝ) ≤ 8 * U.card / k := by positivity
      linarith
  · linarith

theorem Psi_nonneg (ends : Fin m → Sym2 (Fin n)) (k : ℕ) (R : Finset (Fin n))
    (F : Finset (Fin m)) : 0 ≤ Psi ends k R F :=
  Finset.sum_nonneg (fun _ _ => psi_nonneg k R _)

theorem Psi_le (ends : Fin m → Sym2 (Fin n)) {k : ℕ} (hk : 0 < k) (R : Finset (Fin n))
    (F : Finset (Fin m)) : Psi ends k R F ≤ 8 * (n : ℝ) / k + R.card := by
  unfold Psi
  calc ∑ C ∈ comps ends F, psi k R C
      ≤ ∑ C ∈ comps ends F, ∑ x ∈ C, ((8 : ℝ) / k + if x ∈ R then 1 else 0) :=
        Finset.sum_le_sum (fun C _ => psi_le hk R C)
    _ = ∑ x, ((8 : ℝ) / k + if x ∈ R then 1 else 0) := sum_comps ends F _
    _ = 8 * (n : ℝ) / k + R.card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_boole]
        simp only [Finset.card_univ, Fintype.card_fin, Finset.filter_mem_eq_inter,
          Finset.univ_inter]
        ring

/-- the splitting inequality for one component -/
theorem split_ineq (ends : Fin m → Sym2 (Fin n)) {k : ℕ} (hk : 0 < k) (R : Finset (Fin n))
    {F F' : Finset (Fin m)} (h : F' ⊆ F) {C : Finset (Fin n)} (hC : C ∈ comps ends F) :
    (((C.image (cc ends F')).filter (Large k R)).card : ℝ) - 1
        ≤ ∑ U ∈ C.image (cc ends F'), psi k R U - psi k R C ∧
      0 ≤ ∑ U ∈ C.image (cc ends F'), psi k R U - psi k R C := by
  have hcl := comps_closed ends h hC
  have hsub : ∀ U ∈ C.image (cc ends F'), U ⊆ C := by
    intro U hU
    rw [Finset.mem_image] at hU
    obtain ⟨x, hx, rfl⟩ := hU
    intro y hy
    exact hcl x hx y ((mem_cc ends F' x y).1 hy)
  have hcard : ∑ U ∈ C.image (cc ends F'), (U.card : ℝ) = C.card := by
    rw [sum_image_cc ends F' C hcl (fun U => (U.card : ℝ))]
    rw [Finset.sum_congr rfl (fun x _ => div_self (cc_card_pos ends F' x).ne')]
    simp
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set b := ((C.image (cc ends F')).filter (Large k R)).card with hb
  have hge_b : (b : ℝ) ≤ ∑ U ∈ C.image (cc ends F'), psi k R U := by
    calc (b : ℝ) = ∑ U ∈ (C.image (cc ends F')).filter (Large k R), psi k R U := by
          rw [Finset.sum_congr rfl (fun U hU => by
            rw [psi, if_pos (Finset.mem_filter.1 hU).2])]
          simp [hb]
      _ ≤ ∑ U ∈ C.image (cc ends F'), psi k R U :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => psi_nonneg k R _)
  have hsmall : (∀ U ∈ C.image (cc ends F'), ¬ Large k R U) →
      ∑ U ∈ C.image (cc ends F'), psi k R U = 8 * C.card / k := by
    intro hs
    rw [Finset.sum_congr rfl (fun U hU => by rw [psi, if_neg (hs U hU)])]
    rw [← Finset.sum_div, ← Finset.mul_sum, hcard]
  by_cases hCL : Large k R C
  · have hpC : psi k R C = 1 := by rw [psi, if_pos hCL]
    rw [hpC]
    by_cases hb0 : b = 0
    · have hs : ∀ U ∈ C.image (cc ends F'), ¬ Large k R U := by
        intro U hU hUL
        have : U ∈ (C.image (cc ends F')).filter (Large k R) := Finset.mem_filter.2 ⟨hU, hUL⟩
        have := Finset.card_pos.2 ⟨U, this⟩
        rw [← hb] at this
        omega
      rw [hsmall hs]
      rcases hCL with hCL | hCL
      · have : (1 : ℝ) ≤ 8 * C.card / k := by rw [le_div_iff₀ hkpos]; linarith
        rw [hb0]; constructor <;> push_cast <;> linarith
      · exfalso
        obtain ⟨x, hx⟩ := hCL
        rw [Finset.mem_inter] at hx
        apply hs (cc ends F' x) (Finset.mem_image_of_mem _ hx.1)
        right
        exact ⟨x, Finset.mem_inter.2 ⟨self_mem_cc ends F' x, hx.2⟩⟩
    · have : (1 : ℝ) ≤ b := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb0
      constructor <;> linarith
  · have hpC : psi k R C = 8 * C.card / k := by rw [psi, if_neg hCL]
    have hs : ∀ U ∈ C.image (cc ends F'), ¬ Large k R U :=
      fun U hU hUL => hCL (large_mono (hsub U hU) hUL)
    rw [hpC, hsmall hs]
    have hb0 : b = 0 := by
      rw [hb, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact hs
    rw [hb0]
    constructor <;> simp

/-- `Ψ` can only grow when edges are removed -/
theorem Psi_anti (ends : Fin m → Sym2 (Fin n)) {k : ℕ} (hk : 0 < k) (R : Finset (Fin n))
    {F F' : Finset (Fin m)} (h : F' ⊆ F) : Psi ends k R F ≤ Psi ends k R F' := by
  unfold Psi
  rw [← sum_imgs ends h]
  apply Finset.sum_le_sum
  intro C hC
  have := (split_ineq ends hk R h hC).2
  linarith

theorem telescope (a : ℕ → ℝ) (M : ℕ) :
    ∑ i ∈ Finset.range M, (a (i + 3) - a (i + 1)) = a (M + 2) + a (M + 1) - a 2 - a 1 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    ring

end LowDiameterNashWilliams.Main.Dev.L33
end

section
/-! Lemma 3.3, part C: the component bound at one threshold `j`.

`G = {e : p e ≥ j}`, `H = {e : p e - w e ≥ j}` (`w` the incidence weight of `L`), `R` the
exceptional set. For a component `C` of `G` with `q` pieces in `H`, `b` of them large:
`q - 1 - σ(C) ≤ |C ∩ T_j| + max(b - 1, 0)`, where `σ(C) = k(|C|-1) - |E(G[C])|` and
`T_j` is the set of `v ∈ L` whose heaviest edge to `V \ L` has weight exactly `j`.
Summing over components gives the per-threshold inequality `threshold`. -/

set_option autoImplicit false
open Classical
open scoped BigOperators
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L33
open LowDiameterNashWilliams.Main
open LowDiameterNashWilliams.Dev.L32

variable {n m k : ℕ}

/-! ### The incidence weight -/

theorem iw_nonneg (ends : Fin m → Sym2 (Fin n)) (L : Finset (Fin n)) (e : Fin m) :
    0 ≤ incidenceWeight ends L e := by
  unfold incidenceWeight; positivity

theorem iw_le_two (ends : Fin m → Sym2 (Fin n)) (L : Finset (Fin n)) (e : Fin m) :
    incidenceWeight ends L e ≤ 2 := by
  unfold incidenceWeight
  obtain ⟨a, b, hab⟩ := exists_ends ends e
  have : (L.filter fun v => v ∈ ends e) ⊆ {a, b} := by
    intro v hv
    rw [Finset.mem_filter, hab, Sym2.mem_iff] at hv
    rcases hv.2 with rfl | rfl <;> simp
  have h2 := (Finset.card_le_card this).trans Finset.card_le_two
  exact_mod_cast h2

theorem iw_zero (ends : Fin m → Sym2 (Fin n)) (L : Finset (Fin n)) {e : Fin m} {a b : Fin n}
    (hab : ends e = s(a, b)) (ha : a ∉ L) (hb : b ∉ L) : incidenceWeight ends L e = 0 := by
  unfold incidenceWeight
  have : (L.filter fun v => v ∈ ends e) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro v hv hve
    rw [hab, Sym2.mem_iff] at hve
    rcases hve with rfl | rfl
    · exact ha hv
    · exact hb hv
  rw [this]; rfl

theorem iw_one (ends : Fin m → Sym2 (Fin n)) (L : Finset (Fin n)) {e : Fin m} {a b : Fin n}
    (hab : ends e = s(a, b)) (ha : a ∈ L) (hb : b ∉ L) : incidenceWeight ends L e = 1 := by
  unfold incidenceWeight
  have : (L.filter fun v => v ∈ ends e) = {a} := by
    ext v
    rw [Finset.mem_filter, hab, Sym2.mem_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, rfl | rfl⟩
      · rfl
      · exact absurd hv hb
    · rintro rfl; exact ⟨ha, Or.inl rfl⟩
  rw [this]; rfl

/-- `p - w` -/
noncomputable def qf (ends : Fin m → Sym2 (Fin n)) (L : Finset (Fin n)) (p : Fin m → ℤ) :
    Fin m → ℤ := fun e => p e - incidenceWeight ends L e

theorem H_sub_G (ends : Fin m → Sym2 (Fin n)) (L : Finset (Fin n)) (p : Fin m → ℤ) (j : ℤ) :
    Gt (qf ends L p) j ⊆ Gt p j := by
  intro e he
  simp only [Gt, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  have h' : j ≤ p e - incidenceWeight ends L e := he
  have := iw_nonneg ends L e
  omega

theorem G2_sub_H (ends : Fin m → Sym2 (Fin n)) (L : Finset (Fin n)) (p : Fin m → ℤ) (j : ℤ) :
    Gt p (j + 2) ⊆ Gt (qf ends L p) j := by
  intro e he
  simp only [Gt, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  show j ≤ p e - incidenceWeight ends L e
  have := iw_le_two ends L e
  omega

/-- vertices of `L` whose heaviest edge to `V \ L` has weight exactly `j` -/
noncomputable def Tset (ends : Fin m → Sym2 (Fin n)) (L : Finset (Fin n)) (p : Fin m → ℤ)
    (j : ℤ) : Finset (Fin n) :=
  L.filter fun v => (∃ e, v ∈ ends e ∧ (∃ x ∈ ends e, x ∉ L) ∧ p e = j) ∧
    ∀ e, v ∈ ends e → (∃ x ∈ ends e, x ∉ L) → p e ≤ j

theorem Tset_disj (ends : Fin m → Sym2 (Fin n)) (L : Finset (Fin n)) (p : Fin m → ℤ)
    {i j : ℤ} (hij : i ≠ j) : Disjoint (Tset ends L p i) (Tset ends L p j) := by
  rw [Finset.disjoint_left]
  intro v hi hj
  simp only [Tset, Finset.mem_filter] at hi hj
  obtain ⟨-, ⟨e, hve, hx, hpe⟩, hmax⟩ := hi
  obtain ⟨-, ⟨e', hve', hx', hpe'⟩, hmax'⟩ := hj
  have h1 := hmax' e hve hx
  have h2 := hmax e' hve' hx'
  omega

/-- an edge from a representative to `V \ (L ∪ U)` is absent from `G` -/
theorem edge_excl (ends : Fin m → Sym2 (Fin n)) (L : Finset (Fin n)) (p : Fin m → ℤ) (j : ℤ)
    {v x : Fin n} {e : Fin m} (hends : ends e = s(v, x)) (hx : x ∉ L)
    (hxU : x ∉ cc ends (Gt (qf ends L p) j) v)
    (hcase : v ∉ L ∨ cc ends (Gt (qf ends L p) j) v ⊆ L)
    (hT : ¬ ∃ y ∈ cc ends (Gt (qf ends L p) j) v, y ∈ Tset ends L p j) :
    e ∉ Gt p j := by
  intro heG
  simp only [Gt, Finset.mem_filter, Finset.mem_univ, true_and] at heG
  have hreach : ∀ e', j ≤ qf ends L p e' → ∀ y, ends e' = s(v, y) →
      y ∈ cc ends (Gt (qf ends L p) j) v := by
    intro e' he' y hy
    rw [mem_cc]
    apply rch_of_edge ends _ hy
    simp only [Gt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact he'
  by_cases hvL : v ∈ L
  · have hUL := hcase.resolve_left (not_not.2 hvL)
    have hw1 := iw_one ends L hends hvL hx
    have hqe : ¬ j ≤ qf ends L p e := fun h' => hx (hUL (hreach e h' x hends))
    simp only [qf] at hqe
    rw [hw1] at hqe
    apply hT
    refine ⟨v, self_mem_cc _ _ v, ?_⟩
    simp only [Tset, Finset.mem_filter]
    refine ⟨hvL, ⟨e, by rw [hends]; exact Sym2.mem_mk_left _ _,
      ⟨x, by rw [hends]; exact Sym2.mem_mk_right _ _, hx⟩, by omega⟩, ?_⟩
    intro e' hve' ⟨y, hy, hyL⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨y', hy'⟩ := Sym2.mem_iff_exists.1 hve'
    rw [hy', Sym2.mem_iff] at hy
    have hyy : y = y' := by
      rcases hy with rfl | rfl
      · exact absurd hvL hyL
      · rfl
    subst hyy
    have hw1' := iw_one ends L hy' hvL hyL
    have : j ≤ qf ends L p e' := by simp only [qf]; rw [hw1']; omega
    exact hyL (hUL (hreach e' this y hy'))
  · have hw0 := iw_zero ends L hends hvL hx
    have : j ≤ qf ends L p e := by simp only [qf]; rw [hw0]; omega
    exact hxU (hreach e this x hends)

/-- arcs out of `v` whose edges are absent from `G` -/
noncomputable def outNot (T : Trees k m) (D : Fin k → Direction n m) (G : Finset (Fin m))
    (v : Fin n) : ℕ :=
  ∑ i, ((T i).filter fun e => (D i e).1 = v ∧ e ∉ G).card

theorem out_bound {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (L : Finset (Fin n)) (p : Fin m → ℤ) (j : ℤ) {v : Fin n}
    (hout : (outgoingTo T D v L : ℝ) ≤ (k : ℝ) / 8) (hvr : v ≠ r)
    (hU : ((cc ends (Gt (qf ends L p) j) v).card : ℝ) < (k : ℝ) / 8)
    (hcase : v ∉ L ∨ cc ends (Gt (qf ends L p) j) v ⊆ L)
    (hT : ¬ ∃ y ∈ cc ends (Gt (qf ends L p) j) v, y ∈ Tset ends L p j) :
    (3 : ℝ) * k / 4 < outNot T D (Gt p j) v := by
  set U := cc ends (Gt (qf ends L p) j) v with hUdef
  have hper : ∀ i : Fin k, ((T i).filter fun e => (D i e).1 = v).card ≤
      ((T i).filter fun e => (D i e).1 = v ∧ (D i e).2 ∈ L).card +
      ((T i).filter fun e => (D i e).1 = v ∧ (D i e).2 ∈ U).card +
      ((T i).filter fun e => (D i e).1 = v ∧ e ∉ Gt p j).card := by
    intro i
    refine (Finset.card_le_card ?_).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    intro e he
    rw [Finset.mem_filter] at he
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases h1 : (D i e).2 ∈ L
    · exact Or.inl (Or.inl ⟨he.1, he.2, h1⟩)
    by_cases h2 : (D i e).2 ∈ U
    · exact Or.inl (Or.inr ⟨he.1, he.2, h2⟩)
    refine Or.inr ⟨he.1, he.2, ?_⟩
    have hends := (h.toward i).1 e he.1
    rw [he.2] at hends
    exact edge_excl ends L p j hends h1 h2 hcase hT
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hper i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hk : ∑ i : Fin k, ((T i).filter fun e => (D i e).1 = v).card = k := by
    have : ∀ i : Fin k, ((T i).filter fun e => (D i e).1 = v).card = 1 :=
      fun i => (h.toward i).2.2 v hvr
    simp [this]
  rw [hk] at hsum
  have hUc := outgoingTo_le_card h v U
  have hsum' : (k : ℝ) ≤ outgoingTo T D v L + outgoingTo T D v U + outNot T D (Gt p j) v := by
    unfold outgoingTo outNot
    exact_mod_cast hsum
  have : (outgoingTo T D v U : ℝ) ≤ U.card := by exact_mod_cast hUc
  linarith

/-- an edge set is partitioned by the trees -/
theorem card_eq_sum_trees {ends : Fin m → Sym2 (Fin n)} {T : Trees k m}
    {D : Fin k → Direction n m} {r : Fin n} (h : Hyp ends T D r) (S : Finset (Fin m)) :
    S.card = ∑ i, ((T i).filter (· ∈ S)).card := by
  have : S = Finset.univ.biUnion fun i => (T i).filter (· ∈ S) := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · intro he
      obtain ⟨i, hi⟩ := cover h e
      exact ⟨i, hi, he⟩
    · rintro ⟨_, _, he⟩; exact he
  conv_lhs => rw [this]
  rw [Finset.card_biUnion]
  intro i _ j _ hij
  exact Finset.disjoint_filter_filter (h.part.1.2 i j hij)

/-- edges of `G` inside `C` -/
noncomputable def eIn (ends : Fin m → Sym2 (Fin n)) (G : Finset (Fin m)) (C : Finset (Fin n)) : ℕ :=
  ((edgesIn ends C).filter (· ∈ G)).card

theorem sum_outNot_add {ends : Fin m → Sym2 (Fin n)} {T : Trees k m}
    {D : Fin k → Direction n m} {r : Fin n} (h : Hyp ends T D r) (G : Finset (Fin m))
    (C : Finset (Fin n)) :
    ∑ v ∈ C, outNot T D G v + eIn ends G C ≤ k * C.card := by
  unfold outNot eIn
  rw [Finset.sum_comm, card_eq_sum_trees h, ← Finset.sum_add_distrib]
  have : ∀ i : Fin k, ∑ v ∈ C, ((T i).filter fun e => (D i e).1 = v ∧ e ∉ G).card +
      ((T i).filter (· ∈ (edgesIn ends C).filter (· ∈ G))).card ≤ C.card := by
    intro i
    have hsf : ∑ v ∈ C, ((T i).filter fun e => (D i e).1 = v ∧ e ∉ G).card
        = ((T i).filter fun e => (D i e).1 ∈ C ∧ e ∉ G).card := by
      convert sum_fiber (T i) (fun e => (D i e).1) C (fun e => e ∉ G)
    rw [hsf]
    have ht := tail_card h i C
    refine le_trans ?_ (le_trans (Nat.le_add_right _ _) ht.le)
    rw [← Finset.card_union_of_disjoint]
    · apply Finset.card_le_card
      intro e he
      simp only [Finset.mem_union, Finset.mem_filter] at he ⊢
      rcases he with ⟨he, ht, _⟩ | ⟨he, hin, _⟩
      · exact ⟨he, ht⟩
      · refine ⟨he, ((inner_iff h i he C).1 ?_).1⟩
        simpa [edgesIn] using hin
    · rw [Finset.disjoint_left]
      intro e he he'
      simp only [Finset.mem_filter] at he he'
      exact he.2.2 he'.2.2
  calc ∑ i, (∑ v ∈ C, ((T i).filter fun e => (D i e).1 = v ∧ e ∉ G).card +
        ((T i).filter (· ∈ (edgesIn ends C).filter (· ∈ G))).card)
      ≤ ∑ _i : Fin k, C.card := Finset.sum_le_sum (fun i _ => this i)
    _ = k * C.card := by simp

theorem eIn_add_le {ends : Fin m → Sym2 (Fin n)} {T : Trees k m}
    {D : Fin k → Direction n m} {r : Fin n} (h : Hyp ends T D r) (G : Finset (Fin m))
    {C : Finset (Fin n)} (hC : C.Nonempty) : eIn ends G C + k ≤ k * C.card := by
  have h1 := edgeCount_add_le h C hC
  have h2 : eIn ends G C ≤ (edgesIn ends C).card := Finset.card_le_card (Finset.filter_subset _ _)
  omega

theorem r_mem_exc (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (D : Fin k → Direction n m)
    (r : Fin n) : r ∈ exceptional ends T D r := by
  simp [exceptional]

theorem comps_nonempty (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) {C : Finset (Fin n)}
    (hC : C ∈ comps ends F) : C.Nonempty := by
  rw [mem_comps] at hC
  obtain ⟨v, rfl⟩ := hC
  exact ⟨v, self_mem_cc _ _ v⟩

/-- representatives of the components counted by neither `b` nor `t` -/
noncomputable def Reps (ends : Fin m → Sym2 (Fin n)) (k : ℕ) (R L : Finset (Fin n))
    (p : Fin m → ℤ) (j : ℤ) (C : Finset (Fin n)) : Finset (Fin n) :=
  C.filter fun v => ¬ Large k R (cc ends (Gt (qf ends L p) j) v) ∧
    ¬ (∃ y ∈ cc ends (Gt (qf ends L p) j) v, y ∈ Tset ends L p j) ∧
    (v ∉ L ∨ cc ends (Gt (qf ends L p) j) v ⊆ L)

theorem reps_le {ends : Fin m → Sym2 (Fin n)} {T : Trees k m}
    {D : Fin k → Direction n m} {r : Fin n} (h : Hyp ends T D r) (hk : 8 ≤ k)
    (L : Finset (Fin n)) (hout : ∀ v, (outgoingTo T D v L : ℝ) ≤ (k : ℝ) / 8)
    (p : Fin m → ℤ) (j : ℤ) {C : Finset (Fin n)} (hC2 : 2 ≤ C.card) :
    (((Reps ends k (exceptional ends T D r) L p j C).card : ℕ) : ℤ)
      ≤ (k : ℤ) * ((C.card : ℤ) - 1) - eIn ends (Gt p j) C := by
  set R := exceptional ends T D r with hRdef
  set Rp := Reps ends k R L p j C with hRp
  set G := Gt p j with hG
  have hCne : C.Nonempty := Finset.card_pos.1 (by omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  -- each representative has more than `3k/4` arcs outside `G`
  have hrep : ∀ v ∈ Rp, v ∉ R ∧ (3 : ℝ) * k / 4 < outNot T D G v := by
    intro v hv
    rw [hRp, Reps, Finset.mem_filter] at hv
    obtain ⟨_, hnl, hnt, hcase⟩ := hv
    have hvR : v ∉ R := by
      intro hvR
      exact hnl (Or.inr ⟨v, Finset.mem_inter.2 ⟨self_mem_cc _ _ v, hvR⟩⟩)
    refine ⟨hvR, ?_⟩
    have hvr : v ≠ r := by
      rintro rfl; exact hvR (r_mem_exc ends T D v)
    have hU : ((cc ends (Gt (qf ends L p) j) v).card : ℝ) < (k : ℝ) / 8 := by
      by_contra hc; push Not at hc; exact hnl (Or.inl hc)
    exact out_bound h L p j (hout v) hvr hU hcase hnt
  have hsumR : ((Rp.card : ℕ) : ℝ) * ((3 : ℝ) * k / 4) ≤ ∑ v ∈ Rp, (outNot T D G v : ℝ) := by
    have : ∑ _v ∈ Rp, ((3 : ℝ) * k / 4) = ((Rp.card : ℕ) : ℝ) * ((3 : ℝ) * k / 4) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← this]
    exact Finset.sum_le_sum (fun v hv => (hrep v hv).2.le)
  have hsub : Rp ⊆ C := Finset.filter_subset _ _
  have hsumC : ∑ v ∈ Rp, (outNot T D G v : ℝ) ≤ ∑ v ∈ C, (outNot T D G v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have htot := sum_outNot_add h G C
  have htot' : ∑ v ∈ C, (outNot T D G v : ℝ) + eIn ends G C ≤ k * C.card := by
    exact_mod_cast htot
  have hE := eIn_add_le h G hCne
  by_contra hlt
  push Not at hlt
  -- `σ = 0`
  have hσ : eIn ends G C + k = k * C.card := by
    by_contra hne
    have hE' : eIn ends G C + k + 1 ≤ k * C.card := by omega
    have hE'' : ((eIn ends G C : ℕ) : ℝ) + k + 1 ≤ k * C.card := by exact_mod_cast hE'
    have hlt' : (k : ℝ) * ((C.card : ℝ) - 1) - eIn ends G C + 1 ≤ Rp.card := by
      have : (k : ℤ) * ((C.card : ℤ) - 1) - eIn ends G C + 1 ≤ Rp.card := by omega
      exact_mod_cast this
    set σ : ℝ := (k : ℝ) * ((C.card : ℝ) - 1) - eIn ends G C
    have hσ1 : 1 ≤ σ := by simp only [σ]; linarith
    have hk8 : (8 : ℝ) ≤ k := by exact_mod_cast hk
    have h1 : (σ + 1) * ((3 : ℝ) * k / 4) ≤ (Rp.card : ℝ) * ((3 : ℝ) * k / 4) :=
      mul_le_mul_of_nonneg_right hlt' (by positivity)
    have h2 : (Rp.card : ℝ) * ((3 : ℝ) * k / 4) ≤ σ + k := by simp only [σ]; linarith
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ σ - 1 by linarith)
      (show (0 : ℝ) ≤ 3 * k / 4 - 1 by linarith)]
  -- hence every edge inside `C` lies in `G`, and `C` is tight
  have hfull : (edgesIn ends C).filter (· ∈ G) = edgesIn ends C := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    have h1 := edgeCount_add_le h C hCne
    unfold eIn at hσ
    omega
  have htight : tight ends k C := by
    rw [tight_iff]
    refine ⟨hCne, ?_⟩
    unfold eIn at hσ
    rw [hfull] at hσ
    exact hσ
  have hRpne : Rp.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℤ) ≤ (k : ℤ) * ((C.card : ℤ) - 1) - eIn ends G C := by
      have : ((eIn ends G C + k : ℕ) : ℤ) = ((k * C.card : ℕ) : ℤ) := by rw [hσ]
      push_cast at this
      linarith
    omega
  obtain ⟨v, hv⟩ := hRpne
  have hvC := hsub hv
  obtain ⟨hvR, hvout⟩ := hrep v hv
  have hle : outNot T D G v ≤ outgoingTo T D v (Finset.univ \ C) := by
    unfold outNot outgoingTo
    apply Finset.sum_le_sum
    intro i _
    apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_filter] at he ⊢
    refine ⟨he.1, he.2.1, ?_⟩
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, fun hhd => he.2.2 ?_⟩
    have hin : e ∈ edgesIn ends C := by
      simp only [edgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (inner_iff h i he.1 C).2 ⟨he.2.1 ▸ hvC, hhd⟩
    rw [← hfull] at hin
    exact (Finset.mem_filter.1 hin).2
  apply hvR
  rw [hRdef, exceptional, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, Or.inr ⟨C, hvC, hC2, htight, ?_⟩⟩
  have : (outNot T D G v : ℝ) ≤ outgoingTo T D v (Finset.univ \ C) := by exact_mod_cast hle
  linarith

end LowDiameterNashWilliams.Main.Dev.L33
end

section
/-! Lemma 3.3, part D: the component bound and its sum over the components at one threshold. -/

set_option autoImplicit false
open Classical
open scoped BigOperators
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L33
open LowDiameterNashWilliams.Main
open LowDiameterNashWilliams.Dev.L32

variable {n m k : ℕ}

theorem typeT_le (ends : Fin m → Sym2 (Fin n)) (L : Finset (Fin n)) (p : Fin m → ℤ) (j : ℤ)
    {C : Finset (Fin n)} (hC : C ∈ comps ends (Gt p j)) :
    ((C.image (cc ends (Gt (qf ends L p) j))).filter
        (fun U => ∃ y ∈ U, y ∈ Tset ends L p j)).card
      ≤ (C.filter (· ∈ Tset ends L p j)).card := by
  have hcl := comps_closed ends (H_sub_G ends L p j) hC
  apply Finset.card_le_card_of_surjOn (cc ends (Gt (qf ends L p) j))
  intro U hU
  rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hU
  obtain ⟨⟨x, hx, rfl⟩, y, hy, hyT⟩ := hU
  refine ⟨y, ?_, cc_eq_of_mem ends _ hy⟩
  rw [Finset.mem_coe, Finset.mem_filter]
  exact ⟨hcl x hx y ((mem_cc _ _ _ _).1 hy), hyT⟩

theorem neither_le (ends : Fin m → Sym2 (Fin n)) (R L : Finset (Fin n)) (p : Fin m → ℤ)
    (j : ℤ) {C : Finset (Fin n)} (hC : C ∈ comps ends (Gt p j)) :
    ((C.image (cc ends (Gt (qf ends L p) j))).filter
        (fun U => ¬ Large k R U ∧ ¬ ∃ y ∈ U, y ∈ Tset ends L p j)).card
      ≤ (Reps ends k R L p j C).card := by
  have hcl := comps_closed ends (H_sub_G ends L p j) hC
  apply Finset.card_le_card_of_surjOn (cc ends (Gt (qf ends L p) j))
  intro U hU
  rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hU
  obtain ⟨⟨x, hx, rfl⟩, hnl, hnt⟩ := hU
  by_cases hX : ∃ y ∈ cc ends (Gt (qf ends L p) j) x, y ∉ L
  · obtain ⟨y, hy, hyL⟩ := hX
    have hyx := cc_eq_of_mem ends _ hy
    refine ⟨y, ?_, hyx⟩
    rw [Finset.mem_coe, Reps, Finset.mem_filter, hyx]
    exact ⟨hcl x hx y ((mem_cc _ _ _ _).1 hy), hnl, hnt, Or.inl hyL⟩
  · push Not at hX
    refine ⟨x, ?_, rfl⟩
    rw [Finset.mem_coe, Reps, Finset.mem_filter]
    exact ⟨hx, hnl, hnt, Or.inr hX⟩

theorem split_three {α : Type*} (s : Finset α) (P Q : α → Prop) [DecidablePred P]
    [DecidablePred Q] :
    s.card ≤ (s.filter P).card + (s.filter Q).card + (s.filter fun U => ¬ P U ∧ ¬ Q U).card := by
  have : s ⊆ s.filter P ∪ s.filter Q ∪ s.filter (fun U => ¬ P U ∧ ¬ Q U) := by
    intro U hU
    by_cases hP : P U
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hU, hP⟩))
    by_cases hQ : Q U
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hU, hQ⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hU, hP, hQ⟩)
  have h1 := (Finset.card_le_card this).trans (Finset.card_union_le _ _)
  have h2 := Finset.card_union_le (s.filter P) (s.filter Q)
  omega

/-- the component bound (3.3 in the paper's proof), with `max(b-1,0)` replaced by the
potential increase -/
theorem comp_bound {ends : Fin m → Sym2 (Fin n)} {T : Trees k m}
    {D : Fin k → Direction n m} {r : Fin n} (h : Hyp ends T D r) (hk : 8 ≤ k)
    (L : Finset (Fin n)) (hout : ∀ v, (outgoingTo T D v L : ℝ) ≤ (k : ℝ) / 8)
    (p : Fin m → ℤ) (j : ℤ) {C : Finset (Fin n)} (hC : C ∈ comps ends (Gt p j)) :
    ((C.image (cc ends (Gt (qf ends L p) j))).card : ℝ) + eIn ends (Gt p j) C + k
      ≤ (C.filter (· ∈ Tset ends L p j)).card + k * C.card + 1 +
        (∑ U ∈ C.image (cc ends (Gt (qf ends L p) j)), psi k (exceptional ends T D r) U
          - psi k (exceptional ends T D r) C) := by
  set R := exceptional ends T D r with hRdef
  set H := Gt (qf ends L p) j with hH
  have hk0 : 0 < k := by omega
  obtain ⟨hsi1, hsi0⟩ := split_ineq ends hk0 R (H_sub_G ends L p j) hC
  set S := ∑ U ∈ C.image (cc ends H), psi k R U - psi k R C
  have hCne := comps_nonempty ends _ hC
  have hE := eIn_add_le h (Gt p j) hCne
  have hE' : ((eIn ends (Gt p j) C : ℕ) : ℝ) + k ≤ k * C.card := by exact_mod_cast hE
  have ht0 : (0 : ℝ) ≤ (C.filter (· ∈ Tset ends L p j)).card := by positivity
  by_cases hC2 : 2 ≤ C.card
  · have h3 := split_three (C.image (cc ends H)) (Large k R)
      (fun U => ∃ y ∈ U, y ∈ Tset ends L p j)
    have h4 := typeT_le ends L p j hC
    have h5 := neither_le (k := k) ends R L p j hC
    have h6 := reps_le h hk L hout p j hC2
    rw [← hH] at h4 h5
    rw [← hRdef] at h6
    have hq : ((C.image (cc ends H)).card : ℤ) ≤
        (((C.image (cc ends H)).filter (Large k R)).card : ℤ) +
        (C.filter (· ∈ Tset ends L p j)).card +
        ((k : ℤ) * ((C.card : ℤ) - 1) - eIn ends (Gt p j) C) := by
      have : ((C.image (cc ends H)).card : ℤ) ≤
          (((C.image (cc ends H)).filter (Large k R)).card : ℤ) +
          (C.filter (· ∈ Tset ends L p j)).card + (Reps ends k R L p j C).card := by
        exact_mod_cast (h3.trans (by omega))
      linarith
    have hq' : ((C.image (cc ends H)).card : ℝ) ≤
        (((C.image (cc ends H)).filter (Large k R)).card : ℝ) +
        (C.filter (· ∈ Tset ends L p j)).card +
        ((k : ℝ) * ((C.card : ℝ) - 1) - eIn ends (Gt p j) C) := by
      exact_mod_cast hq
    linarith
  · have hq : (C.image (cc ends H)).card ≤ 1 :=
      Finset.card_image_le.trans (by omega)
    have hq' : ((C.image (cc ends H)).card : ℝ) ≤ 1 := by exact_mod_cast hq
    linarith

/-- the per-threshold inequality -/
theorem threshold {ends : Fin m → Sym2 (Fin n)} {T : Trees k m}
    {D : Fin k → Direction n m} {r : Fin n} (h : Hyp ends T D r) (hk : 8 ≤ k)
    (L : Finset (Fin n)) (hout : ∀ v, (outgoingTo T D v L : ℝ) ≤ (k : ℝ) / 8)
    (p : Fin m → ℤ) (j : ℤ) :
    ((Gt p j).card : ℝ) - ((k : ℝ) - 1) * ((n : ℝ) - (comps ends (Gt p j)).card)
        - ((n : ℝ) - (comps ends (Gt (qf ends L p) j)).card)
      ≤ (Tset ends L p j).card + Psi ends k (exceptional ends T D r) (Gt (qf ends L p) j)
        - Psi ends k (exceptional ends T D r) (Gt p j) := by
  set R := exceptional ends T D r with hRdef
  set G := Gt p j with hG
  set H := Gt (qf ends L p) j with hH
  have hHG : H ⊆ G := H_sub_G ends L p j
  have hsum := Finset.sum_le_sum (fun C (hC : C ∈ comps ends G) =>
    comp_bound h hk L hout p j hC)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  -- the five sums
  have s1 : ∑ C ∈ comps ends G, ((C.image (cc ends H)).card : ℝ) = (comps ends H).card := by
    have := sum_imgs ends hHG (fun _ => (1 : ℝ))
    simpa using this
  have s2 : ∑ C ∈ comps ends G, (C.card : ℝ) = n := by
    have := sum_comps ends G (fun _ => (1 : ℝ))
    simpa using this
  have s3 : ∑ C ∈ comps ends G, ((C.filter (· ∈ Tset ends L p j)).card : ℝ)
      = (Tset ends L p j).card := by
    have := sum_comps ends G (fun x => if x ∈ Tset ends L p j then (1 : ℝ) else 0)
    simp only [Finset.sum_boole] at this
    rw [this]
    simp
  have s4 : ∑ C ∈ comps ends G, ∑ U ∈ C.image (cc ends H), psi k R U = Psi ends k R H :=
    sum_imgs ends hHG _
  have s5 : (G.card : ℝ) ≤ ∑ C ∈ comps ends G, (eIn ends G C : ℝ) := by
    have : G ⊆ (comps ends G).biUnion fun C => (edgesIn ends C).filter (· ∈ G) := by
      intro e he
      obtain ⟨a, b, hab⟩ := exists_ends ends e
      rw [Finset.mem_biUnion]
      refine ⟨cc ends G a, (mem_comps ends G _).2 ⟨a, rfl⟩, ?_⟩
      rw [Finset.mem_filter]
      refine ⟨?_, he⟩
      simp only [edgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      intro v hv
      rw [hab, Sym2.mem_iff] at hv
      rw [mem_cc]
      rcases hv with rfl | rfl
      · exact SimpleGraph.Reachable.refl _
      · exact rch_of_edge ends he hab
    have h1 := (Finset.card_le_card this).trans Finset.card_biUnion_le
    unfold eIn
    exact_mod_cast h1
  have s6 : ∑ C ∈ comps ends G, psi k R C = Psi ends k R G := rfl
  rw [s1, s2, s3, s4, s6] at hsum
  nlinarith [hsum, s5]

end LowDiameterNashWilliams.Main.Dev.L33
end

section
/-! Lemma 3.3, part E: summing over thresholds (Kruskal trees, charging `Σ_j |T_j| ≤ |L|`,
telescoping the potential), normalization by an additive constant, and the final theorem. -/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L33
open LowDiameterNashWilliams.Main
open LowDiameterNashWilliams.Dev.L32

variable {n m k : ℕ}

theorem Tset_sum (ends : Fin m → Sym2 (Fin n)) (L : Finset (Fin n)) (p : Fin m → ℤ) (M : ℕ) :
    ∑ i ∈ Finset.range M, ((Tset ends L p ((i + 1 : ℕ) : ℤ)).card : ℝ) ≤ L.card := by
  have hd : Set.PairwiseDisjoint (↑(Finset.range M))
      (fun i : ℕ => Tset ends L p ((i + 1 : ℕ) : ℤ)) := by
    intro i _ i' _ hii
    exact Tset_disj ends L p (by push_cast; omega)
  have h1 := Finset.card_biUnion hd
  have h2 : (Finset.range M).biUnion (fun i : ℕ => Tset ends L p ((i + 1 : ℕ) : ℤ)) ⊆ L :=
    Finset.biUnion_subset.2 (fun _ _ => Finset.filter_subset _ _)
  have h3 := Finset.card_le_card h2
  rw [h1] at h3
  exact_mod_cast h3

theorem weight_add_const (f : Fin m → ℤ) (c : ℤ) (B : Finset (Fin m)) :
    weight (fun e => f e + c) B = weight f B + c * B.card := by
  unfold weight
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

theorem m_eq {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) : (m : ℤ) = k * ((n : ℤ) - 1) := by
  have h1 := card_eq_sum_trees h Finset.univ
  simp only [Finset.mem_univ, Finset.filter_true, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ∀ i, (T i).card + 1 = n := fun i => tree_card ends (h.part.1.1 i)
  have h3 : ∀ i, ((T i).card : ℤ) = (n : ℤ) - 1 := by
    intro i; have := h2 i; omega
  rw [h1]
  push_cast
  rw [Finset.sum_congr rfl (fun i _ => h3 i)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- the inequality for normalized weights, witnessed by two spanning trees -/
theorem core {ends : Fin m → Sym2 (Fin n)} {T : Trees k m}
    {D : Fin k → Direction n m} {r : Fin n} (h : Hyp ends T D r) (hk : 8 ≤ k) (hn : 2 ≤ n)
    (L : Finset (Fin n)) (hout : ∀ v, (outgoingTo T D v L : ℝ) ≤ (k : ℝ) / 8)
    (p : Fin m → ℤ) (M : ℕ) (hq1 : ∀ e, 1 ≤ qf ends L p e) (hpM : ∀ e, p e ≤ M) :
    ∃ B1 B2, IsSpanningTree ends B1 ∧ IsSpanningTree ends B2 ∧
      (((weight p Finset.univ - ((k : ℤ) - 1) * weight p B1 - weight (qf ends L p) B2 : ℤ)) : ℝ)
        ≤ L.card + 2 * (8 * (n : ℝ) / k + (exceptional ends T D r).card) := by
  set R := exceptional ends T D r with hRdef
  set q := qf ends L p with hqdef
  have hk0 : 0 < k := by omega
  have hconn : ∀ a b, Rch ends Finset.univ a b := fun a b =>
    rch_mono ends (Finset.subset_univ _) (connected_of_tree ends (h.part.1.1 ⟨0, hk0⟩) a b)
  have hqp : ∀ e, q e ≤ p e := fun e => by
    have := iw_nonneg ends L e; simp only [hqdef, qf]; omega
  have hp0 : ∀ e, 0 ≤ p e := fun e => by have := hq1 e; have := hqp e; omega
  have hq0 : ∀ e, 0 ≤ q e := fun e => by have := hq1 e; omega
  have hqM : ∀ e, q e ≤ M := fun e => (hqp e).trans (hpM e)
  obtain ⟨B1, hB1, hsp1⟩ := kruskal ends (by omega) hconn p hp0 (M + 1)
    (fun e => by have := hpM e; push_cast; omega)
  obtain ⟨B2, hB2, hsp2⟩ := kruskal ends (by omega) hconn q hq0 (M + 1)
    (fun e => by have := hqM e; push_cast; omega)
  refine ⟨B1, B2, hB1, hB2, ?_⟩
  have hW := weight_eq_sum p M hp0 hpM Finset.univ
  have hW1 := weight_eq_sum p M hp0 hpM B1
  have hW2 := weight_eq_sum q M hq0 hqM B2
  set a : ℕ → ℝ := fun t => Psi ends k R (Gt p (t : ℤ)) with ha
  -- pointwise bound
  have hpt : ∀ i ∈ Finset.range M,
      ((((Finset.univ : Finset (Fin m)).filter fun e => ((i + 1 : ℕ) : ℤ) ≤ p e).card : ℤ) : ℝ)
        - ((k : ℝ) - 1) * (((B1.filter fun e => ((i + 1 : ℕ) : ℤ) ≤ p e).card : ℤ) : ℝ)
        - (((B2.filter fun e => ((i + 1 : ℕ) : ℤ) ≤ q e).card : ℤ) : ℝ)
      ≤ (Tset ends L p ((i + 1 : ℕ) : ℤ)).card + (a (i + 3) - a (i + 1)) := by
    intro i _
    set j : ℤ := ((i + 1 : ℕ) : ℤ) with hj
    have hth := threshold h hk L hout p j
    have hr1 := rank_le ends (B := B1.filter fun e => j ≤ p e) (F := Gt p j)
      (fun e he => by
        simp only [Gt, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢; exact he.2)
      (hsp1 (i + 1))
    have hr2 := rank_le ends (B := B2.filter fun e => j ≤ q e) (F := Gt q j)
      (fun e he => by
        simp only [Gt, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢; exact he.2)
      (hsp2 (i + 1))
    have hr1' : (n : ℝ) - (comps ends (Gt p j)).card ≤ (B1.filter fun e => j ≤ p e).card := by
      have : (n : ℝ) ≤ (B1.filter fun e => j ≤ p e).card + (comps ends (Gt p j)).card := by
        exact_mod_cast hr1
      linarith
    have hr2' : (n : ℝ) - (comps ends (Gt q j)).card ≤ (B2.filter fun e => j ≤ q e).card := by
      have : (n : ℝ) ≤ (B2.filter fun e => j ≤ q e).card + (comps ends (Gt q j)).card := by
        exact_mod_cast hr2
      linarith
    have hanti : Psi ends k R (Gt q j) ≤ a (i + 3) := by
      have hsub := G2_sub_H ends L p j
      have : j + 2 = ((i + 3 : ℕ) : ℤ) := by rw [hj]; push_cast; ring
      rw [this] at hsub
      exact Psi_anti ends hk0 R hsub
    have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (8 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hmul := mul_le_mul_of_nonneg_left hr1' hk1
    have haj : a (i + 1) = Psi ends k R (Gt p j) := rfl
    push_cast
    have hG : ((Finset.univ : Finset (Fin m)).filter fun e => j ≤ p e) = Gt p j := rfl
    rw [hG, haj]
    linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, telescope a M] at hsum
  have hT := Tset_sum ends L p M
  have hB : ∀ t, 0 ≤ a t ∧ a t ≤ 8 * (n : ℝ) / k + R.card := fun t =>
    ⟨Psi_nonneg ends k R _, Psi_le ends hk0 R _⟩
  have hlhs : (((weight p Finset.univ - ((k : ℤ) - 1) * weight p B1 - weight q B2 : ℤ)) : ℝ)
      = ∑ i ∈ Finset.range M,
      (((((Finset.univ : Finset (Fin m)).filter fun e => ((i + 1 : ℕ) : ℤ) ≤ p e).card : ℤ) : ℝ)
        - ((k : ℝ) - 1) * (((B1.filter fun e => ((i + 1 : ℕ) : ℤ) ≤ p e).card : ℤ) : ℝ)
        - (((B2.filter fun e => ((i + 1 : ℕ) : ℤ) ≤ q e).card : ℤ) : ℝ)) := by
    rw [hW, hW1, hW2]
    push_cast
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hlhs]
  have := hB (M + 2)
  have := hB (M + 1)
  have := hB 2
  have := hB 1
  linarith

end LowDiameterNashWilliams.Main.Dev.L33

namespace LowDiameterNashWilliams.Main
open LowDiameterNashWilliams.Main.Dev.L33 in
theorem chk_lemma_3_3 :
  ∃ C : ℝ, 0 < C ∧ ∀ n m k : ℕ, 2 ≤ n → 8 ≤ k →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Trees k m)
    (D : Fin k → Direction n m) (r : Fin n) (L : Finset (Fin n)),
  Simple ends → TreePartition ends T → (∀ i, Toward ends (T i) (D i) r) →
  (∀ v, (outgoingTo T D v L : ℝ) ≤ (k : ℝ) / 8) → ∀ p : Fin m → ℤ,
    ((weight p Finset.univ - ((k : ℤ) - 1) * maxTreeWeight ends p -
      maxTreeWeight ends (fun e => p e - incidenceWeight ends L e) : ℤ) : ℝ) ≤
        L.card + C * ((n : ℝ) / k) := by
  obtain ⟨C0, hC0, h32⟩ := lemma_3_2
  refine ⟨16 + 2 * C0, by positivity, ?_⟩
  intro n m k hn hk ends T D r L hs hpart htow hout p
  have h : LowDiameterNashWilliams.Dev.L32.Hyp ends T D r := ⟨hs, hpart, htow⟩
  have hR := h32 n m k hn (by omega) ends T D r hs hpart htow
  set c : ℤ := 3 + ∑ e, |p e| with hc
  have hpe : ∀ e, |p e| ≤ ∑ e, |p e| := fun e =>
    Finset.single_le_sum (f := fun e => |p e|) (fun _ _ => abs_nonneg _) (Finset.mem_univ e)
  set p' : Fin m → ℤ := fun e => p e + c with hp'
  have hq1 : ∀ e, 1 ≤ qf ends L p' e := by
    intro e
    have h1 := hpe e
    have h2 := neg_abs_le (p e)
    have h3 := iw_le_two ends L e
    simp only [qf, hp', hc]
    linarith
  have hpM : ∀ e, p' e ≤ ((2 * c).toNat : ℕ) := by
    intro e
    have h1 := hpe e
    have h2 := le_abs_self (p e)
    have h0 : 0 ≤ ∑ e, |p e| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    simp only [hp']
    rw [Int.toNat_of_nonneg (by linarith)]
    linarith
  obtain ⟨B1, B2, hB1, hB2, hbound⟩ := core h hk hn L hout p' _ hq1 hpM
  have hmu1 := le_maxTreeWeight ends p hB1
  have hmu2 := le_maxTreeWeight ends (fun e => p e - incidenceWeight ends L e) hB2
  have hm := m_eq h
  have hb1 : (B1.card : ℤ) = (n : ℤ) - 1 := by have := tree_card ends hB1; omega
  have hb2 : (B2.card : ℤ) = (n : ℤ) - 1 := by have := tree_card ends hB2; omega
  have hq' : qf ends L p' = fun e => (p e - incidenceWeight ends L e) + c := by
    funext e; simp only [qf, hp']; ring
  have hequal : weight p' Finset.univ - ((k : ℤ) - 1) * weight p' B1 - weight (qf ends L p') B2
      = weight p Finset.univ - ((k : ℤ) - 1) * weight p B1
        - weight (fun e => p e - incidenceWeight ends L e) B2 := by
    rw [hq', hp', weight_add_const, weight_add_const, weight_add_const, hb1, hb2,
      Finset.card_univ, Fintype.card_fin, hm]
    ring
  have hk1 : (0 : ℤ) ≤ (k : ℤ) - 1 := by omega
  have hint : weight p Finset.univ - ((k : ℤ) - 1) * maxTreeWeight ends p -
      maxTreeWeight ends (fun e => p e - incidenceWeight ends L e)
      ≤ weight p' Finset.univ - ((k : ℤ) - 1) * weight p' B1 - weight (qf ends L p') B2 := by
    rw [hequal]
    have := mul_le_mul_of_nonneg_left hmu1 hk1
    linarith
  have hreal : ((weight p Finset.univ - ((k : ℤ) - 1) * maxTreeWeight ends p -
      maxTreeWeight ends (fun e => p e - incidenceWeight ends L e) : ℤ) : ℝ)
      ≤ ((weight p' Finset.univ - ((k : ℤ) - 1) * weight p' B1
          - weight (qf ends L p') B2 : ℤ) : ℝ) := by
    exact_mod_cast hint
  have h8 : 8 * (n : ℝ) / k = 8 * ((n : ℝ) / k) := by ring
  rw [h8] at hbound
  have hnk : 0 ≤ (n : ℝ) / k := by positivity
  nlinarith

end LowDiameterNashWilliams.Main
end

theorem solution : type_of% @LowDiameterNashWilliams.Main.chk_lemma_3_3 := @LowDiameterNashWilliams.Main.chk_lemma_3_3
