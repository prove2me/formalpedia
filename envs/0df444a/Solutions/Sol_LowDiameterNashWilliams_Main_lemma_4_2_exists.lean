-- Prove2me | solution 1 for LowDiameterNashWilliams.Main.lemma_4_2_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:35:15.900027+00:00
-- url     : https://prove2.me/submissions/76b7344f-f100-4c9f-ab53-7ab927f9700b

import Mathlib
import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Definitions.Def_LowDiameterNashWilliams_Main_Geometry
import Definitions.Def_LowDiameterNashWilliams_Main_Reserves

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

/-! ### Forests -/

/-! ### Thresholds and the Kruskal tree -/

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

end LowDiameterNashWilliams.Main.Dev.L33
end

section
/-! Lemma 4.1, part A: spanning trees of a simple multigraph on `Fin n` as Mathlib trees,
"forest with `n - 1` edges" and "connected with `n - 1` edges" characterisations, walks
avoiding a vertex, and the single tree exchange at a vertex. -/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L41
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33

variable {n m : ℕ}

theorem adjS (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (F : Finset (Fin m))
    (u v : Fin n) : (edgeGraph ends F).Adj u v ↔ ∃ e ∈ F, ends e = s(u, v) := by
  unfold edgeGraph
  rw [SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨e, he, h⟩, -⟩
    exact ⟨e, he, h⟩
  · rintro ⟨e, he, h⟩
    refine ⟨⟨e, he, h⟩, ?_⟩
    rintro rfl
    exact hs.2 e (by rw [h]; simp)

theorem graph_erase (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (F : Finset (Fin m))
    (e : Fin m) (u v : Fin n) (huv : ends e = s(u, v)) :
    edgeGraph ends (F.erase e) = (edgeGraph ends F).deleteEdges {s(u, v)} := by
  ext a b
  rw [SimpleGraph.deleteEdges_adj, adjS ends hs, adjS ends hs]
  constructor
  · rintro ⟨f, hf, hfab⟩
    rw [Finset.mem_erase] at hf
    refine ⟨⟨f, hf.2, hfab⟩, ?_⟩
    rw [Set.mem_singleton_iff, ← hfab, ← huv]
    exact fun h => hf.1 (hs.1 h)
  · rintro ⟨⟨f, hf, hfab⟩, hne⟩
    refine ⟨f, Finset.mem_erase.2 ⟨fun hfe => hne ?_, hf⟩, hfab⟩
    rw [Set.mem_singleton_iff, ← hfab, ← huv, hfe]

theorem forest_iff (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends)
    (F : Finset (Fin m)) : IsForest ends F ↔ (edgeGraph ends F).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  constructor
  · intro hF u v huv
    obtain ⟨e, he, heq⟩ := (adjS ends hs F u v).1 huv
    rw [SimpleGraph.isBridge_iff, ← graph_erase ends hs F e u v heq]
    exact hF e he u v heq
  · intro h e he u v heq
    have hadj : (edgeGraph ends F).Adj u v := (adjS ends hs F u v).2 ⟨e, he, heq⟩
    have := h hadj
    rw [SimpleGraph.isBridge_iff] at this
    rw [graph_erase ends hs F e u v heq]
    exact this

theorem edgeSet_eq (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (F : Finset (Fin m)) :
    (edgeGraph ends F).edgeSet = ends '' (F : Set (Fin m)) := by
  rw [edgeGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext x
  simp only [Set.mem_sdiff, Set.mem_image, Finset.mem_coe]
  constructor
  · exact fun h => h.1
  · rintro ⟨e, he, rfl⟩; exact ⟨⟨e, he, rfl⟩, hs.2 e⟩

theorem ncard_edgeSet (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (F : Finset (Fin m)) :
    Nat.card (edgeGraph ends F).edgeSet = F.card := by
  rw [Nat.card_coe_set_eq, edgeSet_eq ends hs, Set.ncard_image_of_injective _ hs.1,
    Set.ncard_coe_finset]

theorem tree_iff (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (hn : 0 < n)
    (F : Finset (Fin m)) : IsSpanningTree ends F ↔ (edgeGraph ends F).IsTree := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  constructor
  · intro hT
    exact ⟨⟨fun a b => connected_of_tree ends hT a b⟩, (forest_iff ends hs F).1 hT.2.2.2.1⟩
  · intro hT
    exact ⟨Finset.subset_univ _, ⟨⟨0, hn⟩, Finset.mem_univ _⟩, fun _ _ _ _ => Finset.mem_univ _,
      (forest_iff ends hs F).2 hT.isAcyclic, fun a _ b _ => hT.connected.preconnected a b⟩

/-- a connected edge set with `n - 1` edges is a spanning tree -/
theorem tree_of_conn (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (hn : 0 < n)
    (F : Finset (Fin m)) (hc : ∀ a b, Rch ends F a b) (hcard : F.card + 1 = n) :
    IsSpanningTree ends F := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [tree_iff ends hs hn, SimpleGraph.isTree_iff_connected_and_card, ncard_edgeSet ends hs,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  exact ⟨⟨fun a b => hc a b⟩, hcard⟩

end LowDiameterNashWilliams.Main.Dev.L41
end

section
/-! Lemma 4.2 (existence), part A: a spanning tree rooted at a vertex `x` as a parent map
`par` (with `par x = x`, every vertex reaching `x` by iterating `par`) and a parent-edge map
`pe`; subtrees as the relation `Desc`; existence of such a representation for every spanning
tree and every root; the edges of a represented tree form a spanning tree; the two sides of
the parent edge of `v` are the subtree of `v` and its complement; and the redirection of a set
`U` of vertices directly to the root `x`, with its effect on subtrees. -/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L42
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33
open LowDiameterNashWilliams.Main.Dev.L41

variable {n m : ℕ}

/-- `y` lies in the subtree of `v`: some iterate of `par` sends `y` to `v` -/
def Desc (par : Fin n → Fin n) (v y : Fin n) : Prop := ∃ k, par^[k] y = v

theorem desc_refl (par : Fin n → Fin n) (v : Fin n) : Desc par v v := ⟨0, rfl⟩

theorem desc_par_iff (par : Fin n → Fin n) (v y : Fin n) :
    Desc par v y ↔ v = y ∨ Desc par v (par y) := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => exact Or.inl hk.symm
    | succ k =>
      rw [Function.iterate_succ_apply] at hk
      exact Or.inr ⟨k, hk⟩
  · rintro (rfl | ⟨k, hk⟩)
    · exact desc_refl par v
    · exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

theorem desc_trans (par : Fin n → Fin n) {a b c : Fin n} (h1 : Desc par a b)
    (h2 : Desc par b c) : Desc par a c := by
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := h2
  exact ⟨i + j, by rw [Function.iterate_add_apply, hj, hi]⟩

theorem desc_of_par (par : Fin n → Fin n) {v y : Fin n} (h : Desc par v (par y)) :
    Desc par v y := ((desc_par_iff par v y).2 (Or.inr h))

theorem desc_par_self (par : Fin n → Fin n) (y : Fin n) : Desc par (par y) y := ⟨1, rfl⟩

theorem desc_chain (par : Fin n → Fin n) {a b y : Fin n} (ha : Desc par a y)
    (hb : Desc par b y) : Desc par a b ∨ Desc par b a := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  rcases le_total i j with h | h
  · right
    refine ⟨j - i, ?_⟩
    rw [← hi, ← Function.iterate_add_apply, Nat.sub_add_cancel h, hj]
  · left
    refine ⟨i - j, ?_⟩
    rw [← hj, ← Function.iterate_add_apply, Nat.sub_add_cancel h, hi]

section Rooted

variable {par : Fin n → Fin n} {x : Fin n}

/-- a rooted parent map -/
structure Rooted (par : Fin n → Fin n) (x : Fin n) : Prop where
  root : par x = x
  reach : ∀ y, Desc par x y

theorem iterate_root (h : Rooted par x) (k : ℕ) : par^[k] x = x :=
  Function.iterate_fixed h.root k

theorem desc_root_eq (h : Rooted par x) {v : Fin n} (hv : Desc par v x) : v = x := by
  obtain ⟨k, hk⟩ := hv
  rw [iterate_root h] at hk
  exact hk.symm

/-- depth: the number of `par` steps to the root -/
noncomputable def ht (h : Rooted par x) (y : Fin n) : ℕ := Nat.find (h.reach y)

theorem ht_spec (h : Rooted par x) (y : Fin n) : par^[ht h y] y = x := Nat.find_spec (h.reach y)

theorem ht_le_of (h : Rooted par x) {y : Fin n} {k : ℕ} (hk : par^[k] y = x) : ht h y ≤ k :=
  Nat.find_min' (h.reach y) hk

theorem ht_root (h : Rooted par x) : ht h x = 0 :=
  Nat.le_zero.1 (ht_le_of h (k := 0) rfl)

theorem ht_eq_zero (h : Rooted par x) {y : Fin n} (hy : ht h y = 0) : y = x := by
  have := ht_spec h y
  rw [hy] at this
  exact this

theorem ht_par (h : Rooted par x) {y : Fin n} (hy : y ≠ x) : ht h (par y) + 1 = ht h y := by
  have hpos : 0 < ht h y := Nat.pos_of_ne_zero fun h0 => hy (ht_eq_zero h h0)
  have h1 : ht h (par y) ≤ ht h y - 1 := by
    apply ht_le_of h
    have := ht_spec h y
    rw [← Nat.sub_add_cancel hpos, Function.iterate_succ_apply] at this
    exact this
  have h2 : ht h y ≤ ht h (par y) + 1 := by
    apply ht_le_of h
    rw [Function.iterate_succ_apply]
    exact ht_spec h (par y)
  omega

theorem ht_par_le (h : Rooted par x) (y : Fin n) : ht h (par y) ≤ ht h y := by
  by_cases hy : y = x
  · subst hy; rw [h.root]
  · have := ht_par h hy; omega

theorem ht_iter_le (h : Rooted par x) (k : ℕ) (y : Fin n) : ht h (par^[k] y) ≤ ht h y := by
  induction k generalizing y with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact (ih (par y)).trans (ht_par_le h y)

theorem ht_le_of_desc (h : Rooted par x) {v y : Fin n} (hd : Desc par v y) : ht h v ≤ ht h y := by
  obtain ⟨k, rfl⟩ := hd
  exact ht_iter_le h k y

theorem ht_lt_of_desc (h : Rooted par x) {v y : Fin n} (hd : Desc par v y) (hne : v ≠ y) :
    ht h v < ht h y := by
  rcases (desc_par_iff par v y).1 hd with rfl | hd'
  · exact absurd rfl hne
  · have hy : y ≠ x := by
      rintro rfl
      rw [h.root] at hd'
      exact hne (desc_root_eq h hd')
    have := ht_le_of_desc h hd'
    have := ht_par h hy
    omega

theorem desc_antisymm (h : Rooted par x) {a b : Fin n} (h1 : Desc par a b) (h2 : Desc par b a) :
    a = b := by
  by_contra hne
  have := ht_lt_of_desc h h1 hne
  have := ht_le_of_desc h h2
  omega

theorem not_desc_par (h : Rooted par x) {v : Fin n} (hv : v ≠ x) : ¬ Desc par v (par v) := by
  intro hd
  have := ht_le_of_desc h hd
  have := ht_par h hv
  omega

theorem par_ne (h : Rooted par x) {v : Fin n} (hv : v ≠ x) : par v ≠ v := by
  intro he
  apply not_desc_par h hv
  rw [he]; exact desc_refl par v

theorem not_desc_root (h : Rooted par x) {v : Fin n} (hv : v ≠ x) : ¬ Desc par v x :=
  fun hd => hv (desc_root_eq h hd)

end Rooted

/-- a representation of the spanning tree `Q` rooted at `x` -/
structure Rep (ends : Fin m → Sym2 (Fin n)) (Q : Finset (Fin m)) (x : Fin n)
    (par : Fin n → Fin n) (pe : Fin n → Fin m) : Prop where
  rooted : Rooted par x
  mem : ∀ v, v ≠ x → pe v ∈ Q
  ends_eq : ∀ v, v ≠ x → ends (pe v) = s(v, par v)
  surj : ∀ e ∈ Q, ∃ v, v ≠ x ∧ pe v = e

section RepLemmas

variable {ends : Fin m → Sym2 (Fin n)} {Q : Finset (Fin m)} {x : Fin n}
  {par : Fin n → Fin n} {pe : Fin n → Fin m}

theorem pe_inj (h : Rep ends Q x par pe) {v w : Fin n} (hv : v ≠ x) (hw : w ≠ x)
    (he : pe v = pe w) : v = w := by
  have h1 := h.ends_eq v hv
  have h2 := h.ends_eq w hw
  rw [he, h2, Sym2.eq_iff] at h1
  rcases h1 with ⟨h1, -⟩ | ⟨h1, h1'⟩
  · exact h1.symm
  · -- `w = par v` and `par w = v`
    have hd1 : Desc par w v := by rw [h1]; exact desc_par_self par v
    have hd2 : Desc par v w := by rw [← h1']; exact desc_par_self par w
    exact desc_antisymm h.rooted hd2 hd1

theorem Q_eq (h : Rep ends Q x par pe) : Q = (Finset.univ.erase x).image pe := by
  ext e
  rw [Finset.mem_image]
  constructor
  · intro he
    obtain ⟨v, hv, rfl⟩ := h.surj e he
    exact ⟨v, Finset.mem_erase.2 ⟨hv, Finset.mem_univ _⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact h.mem v (Finset.mem_erase.1 hv).1

theorem card_Q (h : Rep ends Q x par pe) : Q.card + 1 = n := by
  rw [Q_eq h, Finset.card_image_of_injOn]
  · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have : 0 < n := Fin.pos x
    omega
  · intro v hv w hw he
    exact pe_inj h (Finset.mem_erase.1 hv).1 (Finset.mem_erase.1 hw).1 he

theorem rch_par (h : Rep ends Q x par pe) (v : Fin n) : Rch ends Q v (par v) := by
  by_cases hv : v = x
  · subst hv; rw [h.rooted.root]
  · exact rch_of_edge ends (h.mem v hv) (h.ends_eq v hv)

theorem rch_desc (h : Rep ends Q x par pe) {v y : Fin n} (hd : Desc par v y) :
    Rch ends Q y v := by
  obtain ⟨k, rfl⟩ := hd
  induction k generalizing y with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact (rch_par h y).trans (ih (y := par y))

theorem tree_of_rep (hs : Simple ends) (h : Rep ends Q x par pe) : IsSpanningTree ends Q := by
  apply tree_of_conn ends hs (Fin.pos x) Q _ (card_Q h)
  intro a b
  exact (rch_desc h (h.rooted.reach a)).trans (rch_desc h (h.rooted.reach b)).symm

/-- the two sides of the parent edge of `v`: reachability in `Q - pe v` is "same side of
the subtree of `v`" -/
theorem cut_iff (h : Rep ends Q x par pe) {v : Fin n} (hv : v ≠ x) (y z : Fin n) :
    Rch ends (Q.erase (pe v)) y z ↔ (Desc par v y ↔ Desc par v z) := by
  constructor
  · intro hr
    rw [Rch, SimpleGraph.reachable_iff_reflTransGen] at hr
    induction hr with
    | refl => exact Iff.rfl
    | @tail b c _ hbc ih =>
      refine ih.trans ?_
      obtain ⟨⟨e, he, hee⟩, -⟩ := (adj_iff ends _ _ _).1 hbc
      rw [Finset.mem_erase] at he
      obtain ⟨w, hw, rfl⟩ := h.surj e he.2
      have hwv : w ≠ v := fun hwv => he.1 (by rw [hwv])
      have key : Desc par v w ↔ Desc par v (par w) := by
        rw [desc_par_iff par v w]
        constructor
        · rintro (h' | h')
          · exact absurd h'.symm hwv
          · exact h'
        · exact fun h' => Or.inr h'
      rw [h.ends_eq w hw, Sym2.eq_iff] at hee
      rcases hee with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact key
      · exact key.symm
  · intro hiff
    -- every vertex reaches `v` (inside) or `x` (outside) avoiding `pe v`
    have hin : ∀ k (y : Fin n), par^[k] y = v → Rch ends (Q.erase (pe v)) y v := by
      intro k
      induction k with
      | zero => intro y hy; rw [← hy]; exact SimpleGraph.Reachable.refl _
      | succ k ih =>
        intro y hy
        rw [Function.iterate_succ_apply] at hy
        have hyx : y ≠ x := by
          rintro rfl
          rw [h.rooted.root, iterate_root h.rooted] at hy
          exact hv hy.symm
        have hyv : y ≠ v := by
          rintro rfl
          exact not_desc_par h.rooted hyx ⟨k, hy⟩
        have hne : pe y ≠ pe v := fun he => hyv (pe_inj h hyx hv he)
        exact (rch_of_edge ends (Finset.mem_erase.2 ⟨hne, h.mem y hyx⟩) (h.ends_eq y hyx)).trans
          (ih (par y) hy)
    have hout : ∀ k (y : Fin n), par^[k] y = x → ¬ Desc par v y →
        Rch ends (Q.erase (pe v)) y x := by
      intro k
      induction k with
      | zero => intro y hy _; rw [← hy]; exact SimpleGraph.Reachable.refl _
      | succ k ih =>
        intro y hy hnd
        rw [Function.iterate_succ_apply] at hy
        by_cases hyx : y = x
        · rw [hyx]
        have hyv : y ≠ v := by rintro rfl; exact hnd (desc_refl par y)
        have hne : pe y ≠ pe v := fun he => hyv (pe_inj h hyx hv he)
        exact (rch_of_edge ends (Finset.mem_erase.2 ⟨hne, h.mem y hyx⟩) (h.ends_eq y hyx)).trans
          (ih (par y) hy fun hd => hnd (desc_of_par par hd))
    by_cases hy : Desc par v y
    · obtain ⟨k, hk⟩ := hy
      obtain ⟨j, hj⟩ := hiff.1 ⟨k, hk⟩
      exact (hin k y hk).trans (hin j z hj).symm
    · obtain ⟨k, hk⟩ := h.rooted.reach y
      obtain ⟨j, hj⟩ := h.rooted.reach z
      exact (hout k y hk hy).trans (hout j z hj fun hz => hy (hiff.2 hz)).symm

theorem ends_mem_left (h : Rep ends Q x par pe) {v : Fin n} (hv : v ≠ x) : v ∈ ends (pe v) := by
  rw [h.ends_eq v hv]; exact Sym2.mem_mk_left _ _

theorem ends_mem_right (h : Rep ends Q x par pe) {v : Fin n} (hv : v ≠ x) :
    par v ∈ ends (pe v) := by
  rw [h.ends_eq v hv]; exact Sym2.mem_mk_right _ _

/-- an end of `pe v` inside the subtree of `v` is `v` -/
theorem end_in_sub (h : Rep ends Q x par pe) {v w : Fin n} (hv : v ≠ x) (hw : w ∈ ends (pe v))
    (hd : Desc par v w) : w = v := by
  rw [h.ends_eq v hv, Sym2.mem_iff] at hw
  rcases hw with rfl | rfl
  · rfl
  · exact absurd hd (not_desc_par h.rooted hv)

end RepLemmas

/-! ### Existence of a representation -/

theorem exists_rep (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) {Q : Finset (Fin m)}
    (hQ : IsSpanningTree ends Q) (hm : 0 < m) (x : Fin n) :
    ∃ par pe, Rep ends Q x par pe := by
  have hstep : ∀ v, v ≠ x → ∃ w, (edgeGraph ends Q).Adj v w ∧ (edgeGraph ends Q).dist w x < (edgeGraph ends Q).dist v x := by
    intro v hv
    obtain ⟨p, hp⟩ := (connected_of_tree ends hQ v x).exists_walk_length_eq_dist
    cases p with
    | nil => exact absurd rfl hv
    | @cons _ w _ hadj q =>
      refine ⟨w, hadj, ?_⟩
      have := SimpleGraph.dist_le q
      rw [SimpleGraph.Walk.length_cons] at hp
      omega
  let par : Fin n → Fin n := fun v => if hv : v = x then x else Classical.choose (hstep v hv)
  have hpar : ∀ v, v ≠ x → (edgeGraph ends Q).Adj v (par v) ∧ (edgeGraph ends Q).dist (par v) x < (edgeGraph ends Q).dist v x := by
    intro v hv
    simp only [par, dif_neg hv]
    exact Classical.choose_spec (hstep v hv)
  have hedge : ∀ v, ∃ e, v ≠ x → e ∈ Q ∧ ends e = s(v, par v) := by
    intro v
    by_cases hv : v = x
    · exact ⟨⟨0, hm⟩, fun h => absurd hv h⟩
    · obtain ⟨e, he, hee⟩ := (adjS ends hs Q v (par v)).1 (hpar v hv).1
      exact ⟨e, fun _ => ⟨he, hee⟩⟩
  let pe : Fin n → Fin m := fun v => Classical.choose (hedge v)
  have hpe : ∀ v, v ≠ x → pe v ∈ Q ∧ ends (pe v) = s(v, par v) :=
    fun v hv => Classical.choose_spec (hedge v) hv
  have hroot : par x = x := by simp [par]
  have hreach : ∀ y, Desc par x y := by
    intro y
    induction hk : (edgeGraph ends Q).dist y x using Nat.strong_induction_on generalizing y with
    | _ k ih =>
      by_cases hy : y = x
      · rw [hy]; exact desc_refl par x
      · exact desc_of_par par (ih _ (hk ▸ (hpar y hy).2) (par y) rfl)
  have hrt : Rooted par x := ⟨hroot, hreach⟩
  have hinj : ∀ v w, v ≠ x → w ≠ x → pe v = pe w → v = w := by
    intro v w hv hw he
    have h1 := (hpe v hv).2
    rw [he, (hpe w hw).2, Sym2.eq_iff] at h1
    rcases h1 with ⟨h1, -⟩ | ⟨h1, h1'⟩
    · exact h1.symm
    · have hd1 : Desc par w v := by rw [h1]; exact desc_par_self par v
      have hd2 : Desc par v w := by rw [← h1']; exact desc_par_self par w
      exact desc_antisymm hrt hd2 hd1
  refine ⟨par, pe, hrt, fun v hv => (hpe v hv).1, fun v hv => (hpe v hv).2, ?_⟩
  -- surjectivity by counting
  have hsub : (Finset.univ.erase x).image pe ⊆ Q := by
    intro e he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
    exact (hpe v (Finset.mem_erase.1 hv).1).1
  have hcard : ((Finset.univ.erase x).image pe).card = Q.card := by
    rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    · have := tree_card ends hQ; omega
    · intro v hv w hw he
      exact hinj v w (Finset.mem_erase.1 hv).1 (Finset.mem_erase.1 hw).1 he
  have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
  intro e he
  rw [← heq] at he
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
  exact ⟨v, (Finset.mem_erase.1 hv).1, rfl⟩

/-! ### Redirecting a set `U` to the root -/

section Redirect

variable {par : Fin n → Fin n} {x : Fin n}

/-- the redirected parent map: every vertex of `U` points directly to `x` -/
def redir (par : Fin n → Fin n) (x : Fin n) (U : Finset (Fin n)) : Fin n → Fin n :=
  fun v => if v ∈ U then x else par v

theorem redir_rooted (h : Rooted par x) {U : Finset (Fin n)} (hxU : x ∉ U) :
    Rooted (redir par x U) x := by
  have hroot : redir par x U x = x := by simp [redir, hxU, h.root]
  refine ⟨hroot, ?_⟩
  intro y
  induction hk : ht h y using Nat.strong_induction_on generalizing y with
  | _ k ih =>
    by_cases hy : y = x
    · rw [hy]; exact desc_refl _ x
    · by_cases hyU : y ∈ U
      · exact ⟨1, by simp [redir, hyU]⟩
      · have hp : redir par x U y = par y := by simp [redir, hyU]
        have := ht_par h hy
        apply desc_of_par
        rw [hp]
        exact ih (ht h (par y)) (by omega) (par y) rfl

/-- (i) new subtrees are contained in old subtrees -/
theorem redir_desc (h : Rooted par x) {U : Finset (Fin n)} (hxU : x ∉ U) {v y : Fin n}
    (hv : v ≠ x) (hd : Desc (redir par x U) v y) : Desc par v y := by
  obtain ⟨k, hk⟩ := hd
  induction k generalizing y with
  | zero => exact ⟨0, hk⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply] at hk
    by_cases hyU : y ∈ U
    · have hp : redir par x U y = x := by simp [redir, hyU]
      rw [hp, iterate_root (redir_rooted h hxU)] at hk
      exact absurd hk.symm hv
    · have hp : redir par x U y = par y := by simp [redir, hyU]
      rw [hp] at hk
      exact desc_of_par par (ih hk)

/-- (iii) the subtree of a redirected proper descendant leaves the subtree of `v` -/
theorem redir_excl (h : Rooted par x) {U : Finset (Fin n)} (hxU : x ∉ U) {u v y : Fin n}
    (hu : u ∈ U) (huy : Desc par u y) (hvu : Desc par v u) (huv : u ≠ v) (hv : v ≠ x) :
    ¬ Desc (redir par x U) v y := by
  rintro ⟨k, hk⟩
  induction k generalizing y with
  | zero =>
    simp only [Function.iterate_zero, id] at hk
    subst hk
    exact huv (desc_antisymm h hvu huy).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply] at hk
    by_cases hyU : y ∈ U
    · have hp : redir par x U y = x := by simp [redir, hyU]
      rw [hp, iterate_root (redir_rooted h hxU)] at hk
      exact hv hk.symm
    · have hp : redir par x U y = par y := by simp [redir, hyU]
      rw [hp] at hk
      have hyu : y ≠ u := fun e => hyU (e ▸ hu)
      have huy' : Desc par u (par y) := by
        rcases (desc_par_iff par u y).1 huy with e | h'
        · exact absurd e.symm hyu
        · exact h'
      exact ih huy' hk

/-- (ii) a vertex of the old subtree of `v` that lies below no redirected proper
descendant of `v` stays in the subtree of `v` -/
theorem redir_incl (_h : Rooted par x) {U : Finset (Fin n)} {v y : Fin n}
    (hd : Desc par v y)
    (hU : ∀ u ∈ U, Desc par u y → Desc par v u → u = v) : Desc (redir par x U) v y := by
  obtain ⟨k, hk⟩ := hd
  induction k generalizing y with
  | zero => exact ⟨0, hk⟩
  | succ k ih =>
    by_cases hyv : y = v
    · rw [hyv]; exact desc_refl _ v
    have hyU : y ∉ U := by
      intro hyU
      exact hyv (hU y hyU (desc_refl par y) ⟨k + 1, hk⟩)
    rw [Function.iterate_succ_apply] at hk
    have hp : redir par x U y = par y := by simp [redir, hyU]
    apply desc_of_par
    rw [hp]
    exact ih (fun u hu hd1 hd2 => hU u hu (desc_trans par hd1 (desc_par_self par y)) hd2) hk

end Redirect

end LowDiameterNashWilliams.Main.Dev.L42
end

section
/-! Lemma 4.2 (existence), part B: vertex weights, the cut charge `gch`, the potential `pot`
of a spanning tree (sum of the charges of the cuts of its edges), its expression through any
rooted representation, and the redirection move `x, U` (every `u ∈ U` with a complementary
arc `(u, x)` takes `{u, x}` as its new parent edge, and its old parent edge becomes the
complementary arc from `u` to its old parent): the result is a spanning tree with a
complementary orientation of the same outdegrees, and its potential is the sum of the charges
of the redirected subtrees. -/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L42
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33
open LowDiameterNashWilliams.Main.Dev.L41

variable {n m : ℕ}

/-- total weight of a vertex set -/
def wsum (wt : Fin n → ℕ) (A : Finset (Fin n)) : ℕ := ∑ y ∈ A, wt y

/-- the charge of a cut with side `A` -/
def gch (d : ℕ) (wt : Fin n → ℕ) (A : Finset (Fin n)) : ℕ :=
  min d (min (wsum wt A) (wsum wt (Finset.univ \ A)))

theorem gch_compl (d : ℕ) (wt : Fin n → ℕ) (A : Finset (Fin n)) :
    gch d wt (Finset.univ \ A) = gch d wt A := by
  unfold gch
  rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ A), min_comm (wsum wt (Finset.univ \ A))]

theorem gch_le (d : ℕ) (wt : Fin n → ℕ) (A : Finset (Fin n)) : gch d wt A ≤ d := min_le_left _ _

theorem gch_le_w (d : ℕ) (wt : Fin n → ℕ) (A : Finset (Fin n)) : gch d wt A ≤ wsum wt A :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem gch_le_wc (d : ℕ) (wt : Fin n → ℕ) (A : Finset (Fin n)) :
    gch d wt A ≤ wsum wt (Finset.univ \ A) :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- the potential of an edge set: the charges of the cuts `Q - e` (seen from `c0`) -/
noncomputable def pot (ends : Fin m → Sym2 (Fin n)) (d : ℕ) (wt : Fin n → ℕ) (c0 : Fin n)
    (S : Finset (Fin m)) : ℕ :=
  ∑ e ∈ S, gch d wt (cc ends (S.erase e) c0)

/-- the subtree of `v` -/
noncomputable def sub (par : Fin n → Fin n) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (Desc par v)

theorem mem_sub (par : Fin n → Fin n) (v y : Fin n) : y ∈ sub par v ↔ Desc par v y := by
  simp [sub]

section Pot

variable {ends : Fin m → Sym2 (Fin n)} {S : Finset (Fin m)} {x : Fin n}
  {par : Fin n → Fin n} {pe : Fin n → Fin m}

theorem cc_rep (h : Rep ends S x par pe) {v : Fin n} (hv : v ≠ x) (c : Fin n) :
    cc ends (S.erase (pe v)) c = if Desc par v c then sub par v else Finset.univ \ sub par v := by
  ext y
  rw [mem_cc, cut_iff h hv]
  split_ifs with hc
  · rw [mem_sub]; tauto
  · rw [Finset.mem_sdiff, mem_sub]; simp only [Finset.mem_univ, true_and]; tauto

theorem gch_cc (h : Rep ends S x par pe) (d : ℕ) (wt : Fin n → ℕ) {v : Fin n} (hv : v ≠ x)
    (c : Fin n) : gch d wt (cc ends (S.erase (pe v)) c) = gch d wt (sub par v) := by
  rw [cc_rep h hv]
  split_ifs
  · rfl
  · exact gch_compl d wt _

theorem pot_rep (h : Rep ends S x par pe) (d : ℕ) (wt : Fin n → ℕ) (c0 : Fin n) :
    pot ends d wt c0 S = ∑ v ∈ Finset.univ.erase x, gch d wt (sub par v) := by
  unfold pot
  conv_lhs => rw [Q_eq h]
  rw [Finset.sum_image]
  · refine Finset.sum_congr ?_ fun v hv => ?_
    · rfl
    · rw [← Q_eq h]
      exact gch_cc h d wt (Finset.mem_erase.1 hv).1 c0
  · intro v hv w hw he
    exact pe_inj h (Finset.mem_erase.1 hv).1 (Finset.mem_erase.1 hw).1 he

end Pot

/-! ### The redirection move -/

/-- `u` has a complementary arc to `x` -/
def InArc (Q : Finset (Fin m)) (D : Direction n m) (u x : Fin n) : Prop :=
  ∃ e, e ∉ Q ∧ D e = (u, x)

theorem outdegree_eq_sum (F : Finset (Fin m)) (D : Direction n m) (v : Fin n) :
    outdegree F D v = ∑ e ∈ F, if (D e).1 = v then 1 else 0 := by
  unfold outdegree
  rw [Finset.card_filter]

theorem move (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) {Q : Finset (Fin m)}
    {D : Direction n m} (hD : Orients ends (Finset.univ \ Q) D) {x : Fin n}
    {par : Fin n → Fin n} {pe : Fin n → Fin m} (h : Rep ends Q x par pe)
    (U : Finset (Fin n)) (hU : ∀ u ∈ U, InArc Q D u x) (d : ℕ) (wt : Fin n → ℕ) (c0 : Fin n) :
    ∃ (S : Finset (Fin m)) (D' : Direction n m), IsSpanningTree ends S ∧
      Orients ends (Finset.univ \ S) D' ∧
      (∀ v, outdegree (Finset.univ \ S) D' v = outdegree (Finset.univ \ Q) D v) ∧
      pot ends d wt c0 S = ∑ v ∈ Finset.univ.erase x, gch d wt (sub (redir par x U) v) := by
  -- the arcs into `x`
  let ae : Fin n → Fin m := fun u => if hu : InArc Q D u x then Classical.choose hu else pe u
  have hae : ∀ u ∈ U, ae u ∉ Q ∧ D (ae u) = (u, x) := by
    intro u hu
    simp only [ae, dif_pos (hU u hu)]
    exact Classical.choose_spec (hU u hu)
  have hxU : x ∉ U := by
    intro hx
    have h1 := hae x hx
    have h2 := hD (ae x) (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h1.1⟩)
    rw [h1.2] at h2
    exact hs.2 _ (by rw [h2]; exact Sym2.mk_isDiag_iff.2 rfl)
  have hae_ends : ∀ u ∈ U, ends (ae u) = s(u, x) := by
    intro u hu
    have h2 := hD (ae u) (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (hae u hu).1⟩)
    rw [(hae u hu).2] at h2
    exact h2
  let pe' : Fin n → Fin m := fun v => if v ∈ U then ae v else pe v
  let S : Finset (Fin m) := (Finset.univ.erase x).image pe'
  have hrep : Rep ends S x (redir par x U) pe' := by
    refine ⟨redir_rooted h.rooted hxU, ?_, ?_, ?_⟩
    · intro v hv
      exact Finset.mem_image.2 ⟨v, Finset.mem_erase.2 ⟨hv, Finset.mem_univ _⟩, rfl⟩
    · intro v hv
      by_cases hvU : v ∈ U
      · simp only [pe', redir, if_pos hvU]; exact hae_ends v hvU
      · simp only [pe', redir, if_neg hvU]; exact h.ends_eq v hv
    · intro e he
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
      exact ⟨v, (Finset.mem_erase.1 hv).1, rfl⟩
  -- the new complementary orientation
  let D' : Direction n m := fun e =>
    if hh : ∃ u ∈ U, pe u = e then (Classical.choose hh, par (Classical.choose hh)) else D e
  have hpeU : ∀ u ∈ U, u ≠ x := fun u hu hux => hxU (hux ▸ hu)
  have hD'pe : ∀ u ∈ U, D' (pe u) = (u, par u) := by
    intro u hu
    have hh : ∃ u' ∈ U, pe u' = pe u := ⟨u, hu, rfl⟩
    simp only [D', dif_pos hh]
    have hc := Classical.choose_spec hh
    have : Classical.choose hh = u := pe_inj h (hpeU _ hc.1) (hpeU u hu) hc.2
    rw [this]
  have hD'ne : ∀ e, e ∉ U.image pe → D' e = D e := by
    intro e he
    have hh : ¬ ∃ u ∈ U, pe u = e := fun ⟨u, hu, hue⟩ => he (Finset.mem_image.2 ⟨u, hu, hue⟩)
    simp only [D', dif_neg hh]
  have hpeQ : U.image pe ⊆ Q := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 he
    exact h.mem u (hpeU u hu)
  have haeQ : U.image ae ⊆ Finset.univ \ Q := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 he
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (hae u hu).1⟩
  -- the complement of the new tree
  have hcompl : Finset.univ \ S = ((Finset.univ \ Q) \ U.image ae) ∪ U.image pe := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, S,
      Finset.mem_image, Finset.mem_erase, pe']
    constructor
    · intro hnot
      by_cases heQ : e ∈ Q
      · obtain ⟨w, hw, rfl⟩ := h.surj e heQ
        by_cases hwU : w ∈ U
        · exact Or.inr ⟨w, hwU, rfl⟩
        · exact absurd ⟨w, ⟨hw, trivial⟩, by simp [hwU]⟩ hnot
      · refine Or.inl ⟨heQ, ?_⟩
        rintro ⟨u, hu, rfl⟩
        exact hnot ⟨u, ⟨hpeU u hu, trivial⟩, by simp [hu]⟩
    · rintro (⟨heQ, hae'⟩ | ⟨u, hu, rfl⟩)
      · rintro ⟨v, ⟨hv, -⟩, rfl⟩
        by_cases hvU : v ∈ U
        · simp only [if_pos hvU] at hae'
          exact hae' ⟨v, hvU, rfl⟩
        · simp only [if_neg hvU] at heQ
          exact heQ (h.mem v hv)
      · rintro ⟨v, ⟨hv, -⟩, hve⟩
        by_cases hvU : v ∈ U
        · simp only [if_pos hvU] at hve
          exact (hae v hvU).1 (hve ▸ h.mem u (hpeU u hu))
        · simp only [if_neg hvU] at hve
          exact hvU ((pe_inj h hv (hpeU u hu) hve) ▸ hu)
  have hdisj : Disjoint ((Finset.univ \ Q) \ U.image ae) (U.image pe) := by
    rw [Finset.disjoint_left]
    intro e he he'
    exact (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 he).1).2 (hpeQ he')
  refine ⟨S, D', tree_of_rep hs hrep, ?_, ?_, pot_rep hrep d wt c0⟩
  · intro e he
    rw [hcompl, Finset.mem_union] at he
    rcases he with he | he
    · have he' : e ∉ U.image pe := fun h' => (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 he).1).2
        (hpeQ h')
      rw [hD'ne e he']
      exact hD e (Finset.mem_sdiff.1 he).1
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 he
      rw [hD'pe u hu]
      exact h.ends_eq u (hpeU u hu)
  · intro v
    rw [outdegree_eq_sum, outdegree_eq_sum, hcompl, Finset.sum_union hdisj]
    have hsplit : Finset.univ \ Q = ((Finset.univ \ Q) \ U.image ae) ∪ U.image ae :=
      (Finset.sdiff_union_of_subset haeQ).symm
    conv_rhs => rw [hsplit]
    rw [Finset.sum_union Finset.sdiff_disjoint]
    congr 1
    · refine Finset.sum_congr rfl fun e he => ?_
      have he' : e ∉ U.image pe := fun h' => (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 he).1).2
        (hpeQ h')
      rw [hD'ne e he']
    · rw [Finset.sum_image, Finset.sum_image]
      · refine Finset.sum_congr rfl fun u hu => ?_
        rw [hD'pe u hu, (hae u hu).2]
      · intro u hu w hw he
        have h1 := (hae u hu).2
        rw [he, (hae w hw).2] at h1
        exact (Prod.mk.inj h1).1.symm
      · intro u hu w hw he
        exact pe_inj h (hpeU u hu) (hpeU w hw) he

end LowDiameterNashWilliams.Main.Dev.L42
end

section
/-! Lemma 4.2 (existence), part C: the setting of a potential-minimal feasible pair, the
stopping inequality for every redirection move, the reindexing of the per-root sums by tree
edges, the two sides of a tree edge, the small sides, and the first and third estimates of
the paper (Section 5): the total size of the small sides is at most `2 (n - 1)`, and a leaf
`a` with an outneighbour `x` satisfies `r(a) ≤ r(x) + 1`, hence `d r(a) ≤ s + d`. -/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L42
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33
open LowDiameterNashWilliams.Main.Dev.L41

variable {n m : ℕ}

/-- weight `d` on `X`, two elsewhere -/
def wt (X : Finset (Fin n)) (d : ℕ) (v : Fin n) : ℕ := if v ∈ X then d else 2

/-- the setting: `(Q, D)` is feasible and minimizes the potential among all feasible pairs -/
structure Setup (ends : Fin m → Sym2 (Fin n)) (Q : Finset (Fin m)) (D : Direction n m)
    (X : Finset (Fin n)) (d : ℕ) (c0 : Fin n) : Prop where
  hs : Simple ends
  hQ : IsSpanningTree ends Q
  hD : Orients ends (Finset.univ \ Q) D
  hm : 0 < m
  hc0 : c0 ∈ X
  hd : 1 ≤ d
  hdeg : ∀ v, v ∉ X → d ≤ outdegree (Finset.univ \ Q) D v
  hmin : ∀ (S : Finset (Fin m)) (D' : Direction n m), IsSpanningTree ends S →
    Orients ends (Finset.univ \ S) D' →
    (∀ v, outdegree (Finset.univ \ S) D' v = outdegree (Finset.univ \ Q) D v) →
    pot ends d (wt X d) c0 Q ≤ pot ends d (wt X d) c0 S

section Weights

variable {X : Finset (Fin n)} {d : ℕ}

theorem wsum_ge_of_mem {A : Finset (Fin n)} {y : Fin n} (hy : y ∈ A) :
    wt X d y ≤ wsum (wt X d) A :=
  Finset.single_le_sum (f := wt X d) (fun _ _ => Nat.zero_le _) hy

theorem not_mem_X_of_light {A : Finset (Fin n)} (hA : wsum (wt X d) A < d) {y : Fin n}
    (hy : y ∈ A) : y ∉ X := by
  intro hyX
  have := wsum_ge_of_mem (X := X) (d := d) hy
  simp [wt, hyX] at this
  omega

theorem wsum_light {A : Finset (Fin n)} (hA : wsum (wt X d) A < d) :
    wsum (wt X d) A = 2 * A.card := by
  unfold wsum
  rw [Finset.sum_congr rfl fun y hy => (show wt X d y = 2 by simp [wt, not_mem_X_of_light hA hy]),
    Finset.sum_const, smul_eq_mul, mul_comm]

theorem wsum_le_two_mul {A : Finset (Fin n)} (hA : ∀ y ∈ A, y ∉ X) :
    wsum (wt X d) A = 2 * A.card := by
  unfold wsum
  rw [Finset.sum_congr rfl fun y hy => (show wt X d y = 2 by simp [wt, hA y hy]),
    Finset.sum_const, smul_eq_mul, mul_comm]

theorem wsum_mono {A B : Finset (Fin n)} (h : A ⊆ B) :
    wsum (wt X d) A ≤ wsum (wt X d) B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => Nat.zero_le _

theorem wsum_erase {A : Finset (Fin n)} {a : Fin n} (ha : a ∈ A) (haX : a ∉ X) :
    wsum (wt X d) (A.erase a) + 2 = wsum (wt X d) A := by
  unfold wsum
  rw [← Finset.sum_erase_add A _ ha]
  simp [wt, haX]

theorem compl_erase {A : Finset (Fin n)} {a : Fin n} (ha : a ∈ A) :
    Finset.univ \ A.erase a = insert a (Finset.univ \ A) := by
  ext y
  by_cases hya : y = a
  · subst hya; simp
  · simp [hya]

theorem wsum_compl_erase {A : Finset (Fin n)} {a : Fin n} (ha : a ∈ A) (haX : a ∉ X) :
    wsum (wt X d) (Finset.univ \ A.erase a) = wsum (wt X d) (Finset.univ \ A) + 2 := by
  unfold wsum
  rw [compl_erase ha, Finset.sum_insert (by simp [ha])]
  simp [wt, haX, add_comm]

/-- a light set (weight `< d`) misses `X`; its complement then has weight `≥ d` when `c0 ∈ X` -/
theorem compl_heavy {A : Finset (Fin n)} (hA : wsum (wt X d) A < d) {c0 : Fin n} (hc0 : c0 ∈ X) :
    d ≤ wsum (wt X d) (Finset.univ \ A) := by
  have hc0A : c0 ∉ A := fun h => not_mem_X_of_light hA h hc0
  have := wsum_ge_of_mem (X := X) (d := d) (A := Finset.univ \ A) (y := c0) (by simp [hc0A])
  simp [wt, hc0] at this
  exact this

theorem gch_light {A : Finset (Fin n)} (hA : wsum (wt X d) A < d) {c0 : Fin n} (hc0 : c0 ∈ X) :
    gch d (wt X d) A = 2 * A.card := by
  have h1 := compl_heavy hA hc0
  unfold gch
  rw [← wsum_light hA]
  omega

theorem gch_heavy {A : Finset (Fin n)} (h1 : d ≤ wsum (wt X d) A)
    (h2 : d ≤ wsum (wt X d) (Finset.univ \ A)) : gch d (wt X d) A = d := by
  unfold gch; omega

end Weights

/-- in-neighbours of `x` in the complementary orientation -/
noncomputable def InSet (Q : Finset (Fin m)) (D : Direction n m) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun u => InArc Q D u x

/-- out-neighbours of `u` in the complementary orientation -/
noncomputable def OutSet (Q : Finset (Fin m)) (D : Direction n m) (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x => InArc Q D u x

theorem mem_InSet {Q : Finset (Fin m)} {D : Direction n m} (x u : Fin n) :
    u ∈ InSet Q D x ↔ InArc Q D u x := by simp [InSet]

theorem mem_OutSet {Q : Finset (Fin m)} {D : Direction n m} (u x : Fin n) :
    x ∈ OutSet Q D u ↔ InArc Q D u x := by simp [OutSet]

/-- the side of `Q - e` containing `y` -/
noncomputable def side (ends : Fin m → Sym2 (Fin n)) (Q : Finset (Fin m)) (e : Fin m)
    (y : Fin n) : Finset (Fin n) := cc ends (Q.erase e) y

/-- the small side of `e` (empty when `e` is saturated) -/
noncomputable def small (ends : Fin m → Sym2 (Fin n)) (Q : Finset (Fin m)) (X : Finset (Fin n))
    (d : ℕ) (e : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun y => wsum (wt X d) (side ends Q e y) < d

/-- the number of small sides containing `y` -/
noncomputable def rr (ends : Fin m → Sym2 (Fin n)) (Q : Finset (Fin m)) (X : Finset (Fin n))
    (d : ℕ) (y : Fin n) : ℕ :=
  (Q.filter fun e => wsum (wt X d) (side ends Q e y) < d).card

section Setting

variable {ends : Fin m → Sym2 (Fin n)} {Q : Finset (Fin m)} {D : Direction n m}
  {X : Finset (Fin n)} {d : ℕ} {c0 : Fin n} (st : Setup ends Q D X d c0)

include st

/-- the chosen representation of `Q` rooted at `x` -/
noncomputable def PR (x : Fin n) : Fin n → Fin n :=
  Classical.choose (exists_rep ends st.hs st.hQ st.hm x)

noncomputable def PE (x : Fin n) : Fin n → Fin m :=
  Classical.choose (Classical.choose_spec (exists_rep ends st.hs st.hQ st.hm x))

theorem rep (x : Fin n) : Rep ends Q x (PR st x) (PE st x) :=
  Classical.choose_spec (Classical.choose_spec (exists_rep ends st.hs st.hQ st.hm x))

theorem inArc_ne {u x : Fin n} (h : InArc Q D u x) : u ≠ x := by
  rintro rfl
  obtain ⟨e, he, hDe⟩ := h
  have := st.hD e (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, he⟩)
  rw [hDe] at this
  exact st.hs.2 e (by rw [this]; exact Sym2.mk_isDiag_iff.2 rfl)

/-- the change of the charge of the parent edge of `v` under the move `x, U` -/
noncomputable def dl (x : Fin n) (U : Finset (Fin n)) (v : Fin n) : ℤ :=
  (gch d (wt X d) (sub (redir (PR st x) x U) v) : ℤ) - gch d (wt X d) (sub (PR st x) v)

/-- the stopping inequality -/
theorem key (x : Fin n) (U : Finset (Fin n)) (hU : ∀ u ∈ U, InArc Q D u x) :
    0 ≤ ∑ v ∈ Finset.univ.erase x, dl st x U v := by
  obtain ⟨S, D', hS, hO, hdeg, hpot⟩ := move ends st.hs st.hD (rep st x) U hU d (wt X d) c0
  have h := st.hmin S D' hS hO hdeg
  rw [hpot, pot_rep (rep st x)] at h
  unfold dl
  rw [Finset.sum_sub_distrib, sub_nonneg]
  exact_mod_cast h

theorem xnotU (x : Fin n) {U : Finset (Fin n)} (hU : ∀ u ∈ U, InArc Q D u x) : x ∉ U :=
  fun hx => inArc_ne st (hU x hx) rfl

/-! ### In- and out-neighbours -/

theorem card_OutSet (u : Fin n) : (OutSet Q D u).card = outdegree (Finset.univ \ Q) D u := by
  unfold outdegree
  have himg : OutSet Q D u =
      ((Finset.univ \ Q).filter fun e => (D e).1 = u).image fun e => (D e).2 := by
    ext x
    rw [mem_OutSet, Finset.mem_image]
    constructor
    · rintro ⟨e, he, hDe⟩
      exact ⟨e, Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _, he⟩, by rw [hDe]⟩,
        by rw [hDe]⟩
    · rintro ⟨e, he, rfl⟩
      rw [Finset.mem_filter, Finset.mem_sdiff] at he
      refine ⟨e, he.1.2, ?_⟩
      rw [← he.2]
  rw [himg, Finset.card_image_of_injOn]
  intro e he e' he' hh
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_sdiff] at he he'
  apply st.hs.1
  rw [st.hD e (Finset.mem_sdiff.2 he.1), st.hD e' (Finset.mem_sdiff.2 he'.1), he.2, he'.2]
  simp only at hh
  rw [hh]

theorem card_OutSet_ge {u : Fin n} (hu : u ∉ X) : d ≤ (OutSet Q D u).card := by
  rw [card_OutSet st]; exact st.hdeg u hu

theorem not_mem_OutSet_self (u : Fin n) : u ∉ OutSet Q D u := by
  rw [mem_OutSet]; exact fun h => inArc_ne st h rfl

theorem InSet_ok (x : Fin n) : ∀ u ∈ InSet Q D x, InArc Q D u x := fun u hu =>
  (mem_InSet x u).1 hu

/-! ### Reindexing by edges -/

/-- the child end of the tree edge `e` for the root `x` -/
noncomputable def child (x : Fin n) (e : Fin m) : Fin n :=
  if h : ∃ v, v ≠ x ∧ PE st x v = e then Classical.choose h else x

theorem child_spec (x : Fin n) {e : Fin m} (he : e ∈ Q) :
    child st x e ≠ x ∧ PE st x (child st x e) = e := by
  have h : ∃ v, v ≠ x ∧ PE st x v = e := (rep st x).surj e he
  simp only [child, dif_pos h]
  exact Classical.choose_spec h

theorem child_pe (x : Fin n) {v : Fin n} (hv : v ≠ x) : child st x (PE st x v) = v := by
  have hm : PE st x v ∈ Q := (rep st x).mem v hv
  have h := child_spec st x hm
  exact pe_inj (rep st x) h.1 hv h.2

theorem sum_child (x : Fin n) (f : Fin n → ℤ) :
    ∑ e ∈ Q, f (child st x e) = ∑ v ∈ Finset.univ.erase x, f v := by
  refine Finset.sum_bij' (fun e _ => child st x e) (fun v _ => PE st x v) ?_ ?_ ?_ ?_ ?_
  · intro e he; exact Finset.mem_erase.2 ⟨(child_spec st x he).1, Finset.mem_univ _⟩
  · intro v hv; exact (rep st x).mem v (Finset.mem_erase.1 hv).1
  · intro e he; exact (child_spec st x he).2
  · intro v hv; exact child_pe st x (Finset.mem_erase.1 hv).1
  · intro e _; rfl

/-! ### Sides of a tree edge -/

/-- the side of `e` away from the root `x` -/
noncomputable def Kx (x : Fin n) (e : Fin m) : Finset (Fin n) := sub (PR st x) (child st x e)

theorem side_eq (x : Fin n) {e : Fin m} (he : e ∈ Q) (y : Fin n) :
    side ends Q e y = if y ∈ Kx st x e then Kx st x e else Finset.univ \ Kx st x e := by
  have h := child_spec st x he
  unfold side Kx
  conv_lhs => rw [← h.2]
  rw [cc_rep (rep st x) h.1 y]
  by_cases hy : Desc (PR st x) (child st x e) y
  · rw [if_pos hy, if_pos ((mem_sub _ _ _).2 hy)]
  · rw [if_neg hy, if_neg (fun h' => hy ((mem_sub _ _ _).1 h'))]

theorem x_not_mem_Kx (x : Fin n) {e : Fin m} (he : e ∈ Q) : x ∉ Kx st x e := by
  unfold Kx
  rw [mem_sub]
  exact not_desc_root (rep st x).rooted (child_spec st x he).1

theorem side_x (x : Fin n) {e : Fin m} (he : e ∈ Q) : side ends Q e x = Finset.univ \ Kx st x e := by
  rw [side_eq st x he, if_neg (x_not_mem_Kx st x he)]

theorem mem_side_self (e : Fin m) (y : Fin n) : y ∈ side ends Q e y := self_mem_cc ends _ y

theorem side_of_mem {e : Fin m} {y z : Fin n} (hz : z ∈ side ends Q e y) :
    side ends Q e z = side ends Q e y := cc_eq_of_mem ends _ hz

theorem side_of_not_mem {e : Fin m} (he : e ∈ Q) {y z : Fin n} (hz : z ∉ side ends Q e y) :
    side ends Q e z = Finset.univ \ side ends Q e y := by
  rw [side_eq st c0 he y, side_eq st c0 he z] at *
  by_cases hy : y ∈ Kx st c0 e <;> by_cases hz' : z ∈ Kx st c0 e <;> simp_all

/-! ### Small sides -/

theorem sum_rr : ∑ y, rr ends Q X d y = ∑ e ∈ Q, (small ends Q X d e).card := by
  unfold rr small
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

theorem small_eq {e : Fin m} (he : e ∈ Q) {y0 : Fin n} (hy0 : y0 ∈ small ends Q X d e) :
    small ends Q X d e = side ends Q e y0 := by
  have hl : wsum (wt X d) (side ends Q e y0) < d := (Finset.mem_filter.1 hy0).2
  ext z
  simp only [small, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hz : z ∈ side ends Q e y0
  · rw [side_of_mem st hz]; exact iff_of_true hl hz
  · rw [side_of_not_mem st he hz]
    exact iff_of_false (not_lt.2 (compl_heavy hl st.hc0)) hz

theorem small_light {e : Fin m} (he : e ∈ Q) (hne : (small ends Q X d e).Nonempty) :
    wsum (wt X d) (small ends Q X d e) < d := by
  obtain ⟨y0, hy0⟩ := hne
  rw [small_eq st he hy0]
  exact (Finset.mem_filter.1 hy0).2

theorem Kx_small {e : Fin m} (he : e ∈ Q) (hne : (small ends Q X d e).Nonempty) (x : Fin n) :
    Kx st x e = if x ∈ small ends Q X d e then Finset.univ \ small ends Q X d e else small ends Q X d e := by
  obtain ⟨y0, hy0⟩ := hne
  have hK : Kx st x e = Finset.univ \ side ends Q e x := by
    rw [side_x st x he, Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
  rw [hK, small_eq st he hy0]
  split_ifs with hx
  · rw [side_of_mem st hx]
  · rw [side_of_not_mem st he hx, Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]

theorem c0_not_small (e : Fin m) : c0 ∉ small ends Q X d e := by
  intro h
  have hl := (Finset.mem_filter.1 h).2
  exact not_mem_X_of_light hl (mem_side_self st e c0) st.hc0

theorem small_not_X {e : Fin m} {y : Fin n} (hy : y ∈ small ends Q X d e) : y ∉ X :=
  not_mem_X_of_light (Finset.mem_filter.1 hy).2 (mem_side_self st e y)

/-- a saturated edge cannot gain charge -/
theorem dl_sat {e : Fin m} (he : e ∈ Q) (hsat : small ends Q X d e = ∅) (x : Fin n) (U : Finset (Fin n)) :
    dl st x U (child st x e) ≤ 0 := by
  have hK1 : d ≤ wsum (wt X d) (Kx st x e) := by
    have hc : child st x e ∈ Kx st x e := by
      unfold Kx; rw [mem_sub]; exact desc_refl _ _
    have : child st x e ∉ small ends Q X d e := by rw [hsat]; exact Finset.notMem_empty _
    simp only [small, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at this
    rwa [side_eq st x he, if_pos hc] at this
  have hK2 : d ≤ wsum (wt X d) (Finset.univ \ Kx st x e) := by
    have : x ∉ small ends Q X d e := by rw [hsat]; exact Finset.notMem_empty _
    simp only [small, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at this
    rwa [side_x st x he] at this
  unfold dl
  have h1 := gch_heavy hK1 hK2
  unfold Kx at h1
  rw [h1]
  have := gch_le d (wt X d) (sub (redir (PR st x) x U) (child st x e))
  omega

/-! ### First estimate: the small sides -/

/-- the child end of a light edge on the small side does not depend on the root outside it -/
theorem child_light {e : Fin m} (he : e ∈ Q) (hne : (small ends Q X d e).Nonempty) {x : Fin n}
    (hx : x ∉ small ends Q X d e) : child st x e = child st c0 e := by
  have hK := Kx_small st he hne x
  have hK0 := Kx_small st he hne c0
  rw [if_neg hx] at hK
  rw [if_neg (c0_not_small st e)] at hK0
  have h0 := child_spec st c0 he
  have hx' := child_spec st x he
  -- `child x e` is an end of `e` inside the small side, hence `child c0 e`
  have hmem : child st x e ∈ ends e := by
    have := ends_mem_left (rep st x) hx'.1
    rwa [hx'.2] at this
  have hin : child st x e ∈ Kx st c0 e := by
    rw [hK0, ← hK]; unfold Kx; rw [mem_sub]; exact desc_refl _ _
  have hmem' : child st x e ∈ ends (PE st c0 (child st c0 e)) := by rw [h0.2]; exact hmem
  exact end_in_sub (rep st c0) h0.1 hmem' (by unfold Kx at hin; rwa [mem_sub] at hin)

theorem dl_light_in {e : Fin m} (he : e ∈ Q) (hne : (small ends Q X d e).Nonempty) {x : Fin n}
    (hx : x ∈ small ends Q X d e) (U : Finset (Fin n)) :
    dl st x U (child st x e) ≤ (d : ℤ) - 2 * (small ends Q X d e).card := by
  have hK := Kx_small st he hne x
  rw [if_pos hx] at hK
  unfold dl
  have h1 : gch d (wt X d) (sub (PR st x) (child st x e)) = 2 * (small ends Q X d e).card := by
    have : sub (PR st x) (child st x e) = Kx st x e := rfl
    rw [this, hK, gch_compl, gch_light (small_light st he hne) st.hc0]
  rw [h1]
  have := gch_le d (wt X d) (sub (redir (PR st x) x U) (child st x e))
  push_cast
  omega

theorem dl_light_out {e : Fin m} (he : e ∈ Q) (hne : (small ends Q X d e).Nonempty) {x : Fin n}
    (hx : x ∉ small ends Q X d e) :
    dl st x (InSet Q D x) (child st x e) ≤
      -2 * ((InSet Q D x ∩ (small ends Q X d e).erase (child st c0 e)).card : ℤ) := by
  have hK := Kx_small st he hne x
  rw [if_neg hx] at hK
  set A := small ends Q X d e with hA
  set c := child st c0 e with hc
  have hcx : child st x e = c := child_light st he hne hx
  have hxU : x ∉ InSet Q D x := xnotU st x (InSet_ok st x)
  have hcne : c ≠ x := by rw [← hcx]; exact (child_spec st x he).1
  have hsubA : sub (PR st x) c = A := by rw [← hK]; unfold Kx; rw [hcx]
  set N := sub (redir (PR st x) x (InSet Q D x)) c with hN
  have hNsub : N ⊆ A \ (InSet Q D x ∩ A.erase c) := by
    intro y hy
    rw [hN, mem_sub] at hy
    have hyA : y ∈ A := by
      rw [← hsubA, mem_sub]; exact redir_desc (rep st x).rooted hxU hcne hy
    refine Finset.mem_sdiff.2 ⟨hyA, ?_⟩
    rintro hy'
    rw [Finset.mem_inter, Finset.mem_erase] at hy'
    have hdesc : Desc (PR st x) c y := by rw [← mem_sub, hsubA]; exact hy'.2.2
    exact redir_excl (rep st x).rooted hxU hy'.1 (desc_refl _ y) hdesc hy'.2.1 hcne hy
  have hcard : N.card + (InSet Q D x ∩ A.erase c).card ≤ A.card := by
    have h1 := Finset.card_le_card hNsub
    have h2 : InSet Q D x ∩ A.erase c ⊆ A := fun y hy =>
      Finset.mem_of_mem_erase (Finset.mem_inter.1 hy).2
    rw [Finset.card_sdiff_of_subset h2] at h1
    have := Finset.card_le_card h2
    omega
  have hgN : gch d (wt X d) N ≤ 2 * N.card := by
    have hNA : ∀ y ∈ N, y ∉ X := fun y hy =>
      small_not_X st (Finset.mem_sdiff.1 (hNsub hy)).1
    rw [← wsum_le_two_mul hNA]; exact gch_le_w d (wt X d) N
  unfold dl
  rw [hcx, ← hN, hsubA, gch_light (small_light st he hne) st.hc0]
  have hj : (small ends Q X d e).card = A.card := by rw [hA]
  rw [hj]
  push_cast
  omega

/-- the double count of the arcs leaving a small side -/
theorem arcs_out (A B : Finset (Fin n)) :
    ∑ x ∈ Finset.univ \ A, ((InSet Q D x ∩ B).card : ℤ) =
      ∑ u ∈ B, ((OutSet Q D u \ A).card : ℤ) := by
  have h1 : ∀ x, ((InSet Q D x ∩ B).card : ℤ) = ∑ u ∈ B, if InArc Q D u x then 1 else 0 := by
    intro x
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter]
    simp [Finset.sum_boole, mem_InSet]
  have h2 : ∀ u, ((OutSet Q D u \ A).card : ℤ) =
      ∑ x ∈ Finset.univ \ A, if InArc Q D u x then 1 else 0 := by
    intro u
    rw [Finset.sum_boole]
    congr 2
    ext x
    simp [mem_OutSet, and_comm]
  simp only [h1, h2]
  exact Finset.sum_comm

theorem light_sum {e : Fin m} (he : e ∈ Q) (hne : (small ends Q X d e).Nonempty) :
    ∑ x, dl st x (InSet Q D x) (child st x e) ≤ 2 * (d : ℤ) - d * (small ends Q X d e).card := by
  set A := small ends Q X d e with hA
  set c := child st c0 e with hc
  have hsplit := Finset.sum_add_sum_compl A (fun x => dl st x (InSet Q D x) (child st x e))
  rw [← hsplit]
  have hin : ∑ x ∈ A, dl st x (InSet Q D x) (child st x e) ≤ A.card * ((d : ℤ) - 2 * A.card) := by
    have := Finset.sum_le_sum fun x hx => dl_light_in st he hne (x := x) hx (InSet Q D x)
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hout : ∑ x ∈ Aᶜ, dl st x (InSet Q D x) (child st x e) ≤
      -2 * ∑ u ∈ A.erase c, ((OutSet Q D u \ A).card : ℤ) := by
    have := Finset.sum_le_sum fun x (hx : x ∈ Aᶜ) =>
      dl_light_out st he hne (x := x) (Finset.mem_compl.1 hx)
    rw [← Finset.mul_sum] at this
    rw [← arcs_out st A (A.erase c), ← Finset.compl_eq_univ_sdiff]
    exact this
  have hper : ∀ u ∈ A.erase c, (d : ℤ) - (A.card - 1) ≤ ((OutSet Q D u \ A).card : ℤ) := by
    intro u hu
    have huA := Finset.mem_of_mem_erase hu
    have h1 := card_OutSet_ge st (small_not_X st huA)
    have h2 : OutSet Q D u ∩ A ⊆ A.erase u := by
      intro y hy
      rw [Finset.mem_inter] at hy
      refine Finset.mem_erase.2 ⟨?_, hy.2⟩
      rintro rfl; exact not_mem_OutSet_self st y hy.1
    have h3 := Finset.card_le_card h2
    rw [Finset.card_erase_of_mem huA] at h3
    have h4 := Finset.card_sdiff_add_card_inter (OutSet Q D u) A
    have hApos : 1 ≤ A.card := Finset.card_pos.2 ⟨u, huA⟩
    push_cast
    omega
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcA : c ∈ A := by
    have hc' : c ∈ Kx st c0 e := by unfold Kx; rw [mem_sub]; exact desc_refl _ _
    rwa [Kx_small st he hne c0, if_neg (c0_not_small st e)] at hc'
  rw [Finset.card_erase_of_mem hcA] at hsum
  have hApos : 1 ≤ A.card := Finset.card_pos.2 hne
  have hcast : ((A.card - 1 : ℕ) : ℤ) = (A.card : ℤ) - 1 := by push_cast [hApos]; ring
  rw [hcast] at hsum
  have hA1 : (1 : ℤ) ≤ A.card := by exact_mod_cast hApos
  nlinarith

/-- the total stopping inequality, summed over all roots, split into light and saturated
edges -/
theorem total_split :
    0 ≤ ∑ e ∈ Q.filter (fun e => (small ends Q X d e).Nonempty),
          (2 * (d : ℤ) - d * (small ends Q X d e).card) +
        ∑ x, ∑ e ∈ Q.filter (fun e => ¬ (small ends Q X d e).Nonempty), dl st x (InSet Q D x) (child st x e) := by
  have h0 : 0 ≤ ∑ x, ∑ e ∈ Q, dl st x (InSet Q D x) (child st x e) := by
    apply Finset.sum_nonneg
    intro x _
    rw [sum_child st x (dl st x (InSet Q D x))]
    exact key st x (InSet Q D x) (InSet_ok st x)
  have hsplit : ∀ x, ∑ e ∈ Q, dl st x (InSet Q D x) (child st x e) =
      ∑ e ∈ Q.filter (fun e => (small ends Q X d e).Nonempty), dl st x (InSet Q D x) (child st x e) +
      ∑ e ∈ Q.filter (fun e => ¬ (small ends Q X d e).Nonempty), dl st x (InSet Q D x) (child st x e) :=
    fun x => (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  simp only [hsplit, Finset.sum_add_distrib] at h0
  rw [Finset.sum_comm] at h0
  have hl : ∑ e ∈ Q.filter (fun e => (small ends Q X d e).Nonempty), ∑ x, dl st x (InSet Q D x) (child st x e)
      ≤ ∑ e ∈ Q.filter (fun e => (small ends Q X d e).Nonempty), (2 * (d : ℤ) - d * (small ends Q X d e).card) :=
    Finset.sum_le_sum fun e he =>
      light_sum st (Finset.mem_filter.1 he).1 (Finset.mem_filter.1 he).2
  linarith

theorem light_total_le :
    ∑ e ∈ Q.filter (fun e => (small ends Q X d e).Nonempty), (2 * (d : ℤ) - d * (small ends Q X d e).card) ≤
      2 * d * Q.card - d * ∑ y, rr ends Q X d y := by
  rw [sum_rr st]
  have h1 : ∑ e ∈ Q.filter (fun e => (small ends Q X d e).Nonempty), (2 * (d : ℤ) - d * (small ends Q X d e).card)
      ≤ ∑ e ∈ Q, (2 * (d : ℤ) - d * (small ends Q X d e).card) := by
    rw [← Finset.sum_filter_add_sum_filter_not Q (fun e => (small ends Q X d e).Nonempty)]
    have : 0 ≤ ∑ e ∈ Q.filter (fun e => ¬ (small ends Q X d e).Nonempty),
        (2 * (d : ℤ) - d * (small ends Q X d e).card) := by
      apply Finset.sum_nonneg
      intro e he
      have : small ends Q X d e = ∅ := Finset.not_nonempty_iff_eq_empty.1 (Finset.mem_filter.1 he).2
      rw [this]; simp
    linarith
  have h2 : ∑ e ∈ Q, (2 * (d : ℤ) - d * (small ends Q X d e).card) =
      2 * d * Q.card - d * ∑ e ∈ Q, ((small ends Q X d e).card : ℤ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]; ring
  push_cast
  linarith

/-- first estimate: `s ≤ 2 (n - 1)` -/
theorem s_le : ∑ y, rr ends Q X d y ≤ 2 * Q.card := by
  have h0 := total_split st
  have h1 := light_total_le st
  have h2 : ∑ x, ∑ e ∈ Q.filter (fun e => ¬ (small ends Q X d e).Nonempty),
      dl st x (InSet Q D x) (child st x e) ≤ 0 := by
    apply Finset.sum_nonpos
    intro x _
    apply Finset.sum_nonpos
    intro e he
    rw [Finset.mem_filter] at he
    exact dl_sat st he.1 (Finset.not_nonempty_iff_eq_empty.1 he.2) x _
  have hd : (1 : ℤ) ≤ d := by exact_mod_cast st.hd
  have : (d : ℤ) * ∑ y, (rr ends Q X d y : ℤ) ≤ (d : ℤ) * (2 * Q.card) := by push_cast at h1; nlinarith
  have := le_of_mul_le_mul_left this (by omega)
  exact_mod_cast this

end Setting

end LowDiameterNashWilliams.Main.Dev.L42
end

section
/-! Lemma 4.2 (existence), part D: the third estimate of the paper (Section 5, "bounding the
light ends"): reattaching a leaf `a` to an out-neighbour `x` shows `r(a) ≤ r(x) + 1`, hence
`d r(a) ≤ s + d`. -/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L42
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33
open LowDiameterNashWilliams.Main.Dev.L41

variable {n m : ℕ}

section Setting

variable {ends : Fin m → Sym2 (Fin n)} {Q : Finset (Fin m)} {D : Direction n m}
  {X : Finset (Fin n)} {d : ℕ} {c0 : Fin n} (st : Setup ends Q D X d c0)

include st

theorem side_pe (x : Fin n) {v : Fin n} (hv : v ≠ x) (y : Fin n) :
    side ends Q (PE st x v) y = if Desc (PR st x) v y then sub (PR st x) v
      else Finset.univ \ sub (PR st x) v := by
  have hm : PE st x v ∈ Q := (rep st x).mem v hv
  rw [side_eq st x hm y]
  have hK : Kx st x (PE st x v) = sub (PR st x) v := by unfold Kx; rw [child_pe st x hv]
  rw [hK]
  by_cases hy : Desc (PR st x) v y
  · rw [if_pos hy, if_pos ((mem_sub _ _ _).2 hy)]
  · rw [if_neg hy, if_neg (fun h' => hy ((mem_sub _ _ _).1 h'))]

/-- `r(y)` counted through the representation rooted at `x` -/
theorem rr_root (x y : Fin n) :
    (rr ends Q X d y : ℤ) = ∑ v ∈ Finset.univ.erase x,
      if wsum (wt X d) (side ends Q (PE st x v) y) < d then (1 : ℤ) else 0 := by
  unfold rr
  rw [Finset.card_filter]
  push_cast
  have := sum_child st x (fun v => if wsum (wt X d) (side ends Q (PE st x v) y) < d then (1 : ℤ) else 0)
  rw [← this]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [(child_spec st x he).2]

/-- a leaf has no children for any other root -/
theorem sub_leaf {a x : Fin n} (hax : a ≠ x) (hleaf : degIn ends Q a = 1) :
    sub (PR st x) a = {a} := by
  ext y
  rw [mem_sub, Finset.mem_singleton]
  constructor
  · rintro ⟨k, hk⟩
    by_contra hya
    cases k with
    | zero => exact hya hk
    | succ j =>
      rw [Function.iterate_succ_apply'] at hk
      set c := (PR st x)^[j] y with hc
      have hrt := (rep st x).rooted
      have hcx : c ≠ x := by
        intro h; rw [h, hrt.root] at hk; exact hax hk.symm
      have hca : c ≠ a := by
        intro h; rw [h] at hk; exact par_ne hrt (h ▸ hcx) (h ▸ hk)
      have h1 : PE st x c ∈ Q.filter (fun e => a ∈ ends e) := by
        rw [Finset.mem_filter]
        refine ⟨(rep st x).mem c hcx, ?_⟩
        rw [(rep st x).ends_eq c hcx, hk]; exact Sym2.mem_mk_right _ _
      have h2 : PE st x a ∈ Q.filter (fun e => a ∈ ends e) := by
        rw [Finset.mem_filter]
        exact ⟨(rep st x).mem a hax, ends_mem_left (rep st x) hax⟩
      have hle : (Q.filter (fun e => a ∈ ends e)).card ≤ 1 := by
        unfold degIn at hleaf; omega
      have := Finset.card_le_one.1 hle _ h1 _ h2
      exact hca (pe_inj (rep st x) hcx hax this)
  · rintro rfl; exact desc_refl _ _

theorem redir_leaf {a x : Fin n} (hax : a ≠ x) (hleaf : degIn ends Q a = 1) (v : Fin n)
    (hv : v ≠ x) :
    sub (redir (PR st x) x {a}) v =
      if Desc (PR st x) v a ∧ v ≠ a then (sub (PR st x) v).erase a else sub (PR st x) v := by
  have hrt := (rep st x).rooted
  have hxU : x ∉ ({a} : Finset (Fin n)) := by simp [hax.symm]
  have hsa := sub_leaf st hax hleaf
  ext y
  rw [mem_sub]
  split_ifs with hva
  · rw [Finset.mem_erase, mem_sub]
    constructor
    · intro hy
      refine ⟨?_, redir_desc hrt hxU hv hy⟩
      rintro rfl
      exact redir_excl hrt hxU (Finset.mem_singleton_self y) (desc_refl _ y) hva.1 hva.2.symm hv hy
    · rintro ⟨hya, hy⟩
      apply redir_incl hrt hy
      intro u hu hdu _
      rw [Finset.mem_singleton] at hu
      subst hu
      have : y ∈ sub (PR st x) u := by rw [mem_sub]; exact hdu
      rw [hsa, Finset.mem_singleton] at this
      exact absurd this hya
  · rw [mem_sub]
    constructor
    · exact redir_desc hrt hxU hv
    · intro hy
      apply redir_incl hrt hy
      intro u hu _ hvu
      rw [Finset.mem_singleton] at hu
      subst hu
      by_contra hne
      exact hva ⟨hvu, fun h => hne h.symm⟩

/-- the per-edge bound for the leaf move -/
theorem dl_leaf {a x : Fin n} (hax : a ≠ x) (hleaf : degIn ends Q a = 1) (haX : a ∉ X)
    (v : Fin n) (hv : v ≠ x) :
    dl st x {a} v ≤
      (if Desc (PR st x) v a ∧ v ≠ a ∧ wsum (wt X d) (sub (PR st x) v) < d then (-2 : ℤ) else 0) +
      (if Desc (PR st x) v a ∧ wsum (wt X d) (Finset.univ \ sub (PR st x) v) < d then (2 : ℤ)
        else 0) := by
  unfold dl
  rw [redir_leaf st hax hleaf v hv]
  set A := sub (PR st x) v with hA
  by_cases hva : Desc (PR st x) v a ∧ v ≠ a
  · rw [if_pos hva]
    have haA : a ∈ A := by rw [hA, mem_sub]; exact hva.1
    have he1 := wsum_erase (X := X) (d := d) haA haX
    have he2 := wsum_compl_erase (X := X) (d := d) haA haX
    have hg1 := gch_le_w d (wt X d) (A.erase a)
    have hg2 := gch_le_wc d (wt X d) (A.erase a)
    have hg3 := gch_le d (wt X d) (A.erase a)
    by_cases hl : wsum (wt X d) A < d
    · have hc := compl_heavy hl st.hc0
      have hgA : gch d (wt X d) A = wsum (wt X d) A := by unfold gch; omega
      rw [if_pos ⟨hva.1, hva.2, hl⟩, hgA]
      split_ifs <;> push_cast <;> omega
    · rw [if_neg (fun h => hl h.2.2)]
      by_cases hl2 : wsum (wt X d) (Finset.univ \ A) < d
      · have hgA : gch d (wt X d) A = wsum (wt X d) (Finset.univ \ A) := by unfold gch; omega
        rw [if_pos ⟨hva.1, hl2⟩, hgA]
        push_cast; omega
      · have hgA : gch d (wt X d) A = d := gch_heavy (by omega) (by omega)
        rw [hgA]
        split_ifs <;> push_cast <;> omega
  · rw [if_neg hva, if_neg (fun h => hva ⟨h.1, h.2.1⟩)]
    split_ifs <;> simp

theorem pt_leaf (x a v : Fin n) (hvx : v ≠ x) :
    (if wsum (wt X d) (side ends Q (PE st x v) a) < d then (1 : ℤ) else 0) +
        (if Desc (PR st x) v a ∧ wsum (wt X d) (Finset.univ \ sub (PR st x) v) < d then (1 : ℤ)
          else 0) ≤
      (if Desc (PR st x) v a ∧ v ≠ a ∧ wsum (wt X d) (sub (PR st x) v) < d then (1 : ℤ) else 0) +
        (if wsum (wt X d) (side ends Q (PE st x v) x) < d then (1 : ℤ) else 0) +
        (if v = a then 1 else 0) := by
  rw [side_pe st x hvx a, side_pe st x hvx x,
    if_neg (not_desc_root (rep st x).rooted hvx)]
  by_cases hd : Desc (PR st x) v a
  · rw [if_pos hd]
    by_cases hva : v = a
    · simp only [hd, hva, ne_eq, not_true_eq_false, false_and, and_false, if_false, if_true,
        true_and]
      split_ifs <;> omega
    · simp only [hd, hva, ne_eq, not_false_eq_true, true_and, if_false]
      split_ifs <;> omega
  · rw [if_neg hd]
    simp only [hd, false_and, if_false]
    split_ifs <;> omega

/-- third estimate, local form: `r(a) ≤ r(x) + 1` for every out-neighbour `x` of a leaf `a` -/
theorem rr_leaf {a x : Fin n} (hax : InArc Q D a x) (hleaf : degIn ends Q a = 1) (haX : a ∉ X) :
    rr ends Q X d a ≤ rr ends Q X d x + 1 := by
  have hax' : a ≠ x := inArc_ne st hax
  have hU : ∀ u ∈ ({a} : Finset (Fin n)), InArc Q D u x := by
    intro u hu; rw [Finset.mem_singleton] at hu; rw [hu]; exact hax
  have h0 := key st x {a} hU
  have h1 := Finset.sum_le_sum fun v (hv : v ∈ Finset.univ.erase x) =>
    dl_leaf st hax' hleaf haX v (Finset.mem_erase.1 hv).1
  have hra := rr_root st x a
  have hrx := rr_root st x x
  have hpt := fun v (hv : v ∈ Finset.univ.erase x) => pt_leaf st x a v (Finset.mem_erase.1 hv).1
  set E := Finset.univ.erase x with hE
  set par := PR st x
  have hsum := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib] at hsum
  rw [← hra, ← hrx] at hsum
  have hP : ∑ v ∈ E, (if v = a then (1 : ℤ) else 0) ≤ 1 := by
    rw [Finset.sum_ite_eq']; split_ifs <;> simp
  -- the stopping inequality: `2 P' ≤ 2 Q`
  have hstop : ∑ v ∈ E,
      (if Desc par v a ∧ v ≠ a ∧ wsum (wt X d) (sub par v) < d then (1 : ℤ) else 0) ≤
      ∑ v ∈ E, (if Desc par v a ∧ wsum (wt X d) (Finset.univ \ sub par v) < d then (1 : ℤ)
        else 0) := by
    have h2 : ∀ v ∈ E,
        ((if Desc par v a ∧ v ≠ a ∧ wsum (wt X d) (sub par v) < d then (-2 : ℤ) else 0) +
        (if Desc par v a ∧ wsum (wt X d) (Finset.univ \ sub par v) < d then (2 : ℤ) else 0)) =
        2 * ((if Desc par v a ∧ wsum (wt X d) (Finset.univ \ sub par v) < d then (1 : ℤ) else 0) -
          (if Desc par v a ∧ v ≠ a ∧ wsum (wt X d) (sub par v) < d then (1 : ℤ) else 0)) := by
      intro v _; split_ifs <;> norm_num
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, Finset.sum_sub_distrib] at h1
    linarith
  have : (rr ends Q X d a : ℤ) ≤ rr ends Q X d x + 1 := by linarith
  exact_mod_cast this

/-- third estimate: `d r(a) ≤ s + d` for every leaf `a` -/
theorem leaf_bound {a : Fin n} (hleaf : degIn ends Q a = 1) :
    d * rr ends Q X d a ≤ ∑ y, rr ends Q X d y + d := by
  by_cases h0 : rr ends Q X d a = 0
  · rw [h0]; omega
  have haX : a ∉ X := by
    obtain ⟨e, he⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h0)
    exact not_mem_X_of_light (Finset.mem_filter.1 he).2 (mem_side_self st e a)
  have hout := card_OutSet_ge st haX
  have h1 : ∀ x ∈ OutSet Q D a, rr ends Q X d a - 1 ≤ rr ends Q X d x := by
    intro x hx
    have := rr_leaf st ((mem_OutSet a x).1 hx) hleaf haX
    omega
  have h2 := Finset.sum_le_sum h1
  rw [Finset.sum_const, smul_eq_mul] at h2
  have h3 : ∑ x ∈ OutSet Q D a, rr ends Q X d x ≤ ∑ y, rr ends Q X d y :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.zero_le _
  have h4 : d * (rr ends Q X d a - 1) ≤ (OutSet Q D a).card * (rr ends Q X d a - 1) :=
    Nat.mul_le_mul_right _ hout
  have h5 : d * rr ends Q X d a = d * (rr ends Q X d a - 1) + d := by
    rw [Nat.mul_sub_one]; have : d ≤ d * rr ends Q X d a := Nat.le_mul_of_pos_right d (by omega)
    omega
  omega

end Setting

end LowDiameterNashWilliams.Main.Dev.L42
end

section
/-! Lemma 4.2 (existence), part E: the second estimate of the paper (Section 5, "bounding the
saturated middle"). For the root `c0 ∈ X` and a vertex `h` all of whose proper ancestors `v`
(and `h` itself) have subtrees of weight at least `d`, the path `H` from `h` to `c0` has
`d (depth h + 1) ≤ 4 d |X| + 11 n` vertices (the paper's constant is `3 |X| + 9 N / d`; the
cruder count of the sets `F_v` used below costs the difference). -/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L42
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33
open LowDiameterNashWilliams.Main.Dev.L41

variable {n m : ℕ}

/-! ### Depth along iterates -/

theorem ht_iter {par : Fin n → Fin n} {x : Fin n} (hr : Rooted par x) (y : Fin n) :
    ∀ i, i ≤ ht hr y → ht hr (par^[i] y) + i = ht hr y := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have hne : par^[i] y ≠ x := by
      intro he; rw [he, ht_root hr] at h1; omega
    rw [Function.iterate_succ_apply']
    have := ht_par hr hne
    omega

theorem iter_ne_root {par : Fin n → Fin n} {x : Fin n} (hr : Rooted par x) (y : Fin n) {i : ℕ}
    (hi : i < ht hr y) : par^[i] y ≠ x := by
  intro he
  have := ht_iter hr y i hi.le
  rw [he, ht_root hr] at this
  omega

/-- the proper ancestors of `y` (excluding the root) are `ht y` many -/
theorem card_anc {par : Fin n → Fin n} {x : Fin n} (hr : Rooted par x) (y : Fin n) :
    ((Finset.univ.erase x).filter fun v => Desc par v y).card = ht hr y := by
  have heq : ((Finset.univ.erase x).filter fun v => Desc par v y) =
      (Finset.range (ht hr y)).image fun i => par^[i] y := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_image,
      Finset.mem_range]
    constructor
    · rintro ⟨hvx, k, hk⟩
      refine ⟨k, ?_, hk⟩
      by_contra hk'
      apply hvx
      rw [← hk, ← Nat.sub_add_cancel (not_lt.1 hk'), Function.iterate_add_apply, ht_spec hr y,
        iterate_root hr]
    · rintro ⟨i, hi, rfl⟩
      exact ⟨iter_ne_root hr y hi, i, rfl⟩
  rw [heq, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj he
  have h1 := ht_iter hr y i (Finset.mem_range.1 hi).le
  have h2 := ht_iter hr y j (Finset.mem_range.1 hj).le
  simp only at he
  rw [he] at h1
  omega

/-- a walk to the root of length `ht y` -/
theorem walk_root {ends : Fin m → Sym2 (Fin n)} (hs : Simple ends) {Q : Finset (Fin m)}
    {x : Fin n} {par : Fin n → Fin n} {pe : Fin n → Fin m} (h : Rep ends Q x par pe) (y : Fin n) :
    ∃ p : (edgeGraph ends Q).Walk y x, p.length = ht h.rooted y := by
  induction hk : ht h.rooted y using Nat.strong_induction_on generalizing y with
  | _ k ih =>
    by_cases hy : y = x
    · subst hy
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      rw [ht_root h.rooted] at hk; simp [hk]
    · have hp := ht_par h.rooted hy
      obtain ⟨q, hq⟩ := ih (ht h.rooted (par y)) (by omega) (par y) rfl
      have hadj : (edgeGraph ends Q).Adj y (par y) :=
        (adjS ends hs Q y (par y)).2 ⟨pe y, h.mem y hy, h.ends_eq y hy⟩
      exact ⟨SimpleGraph.Walk.cons hadj q, by rw [SimpleGraph.Walk.length_cons]; omega⟩

section Setting

variable {ends : Fin m → Sym2 (Fin n)} {Q : Finset (Fin m)} {D : Direction n m}
  {X : Finset (Fin n)} {d : ℕ} {c0 : Fin n} (st : Setup ends Q D X d c0)

include st

/-! ### General facts for a root `x` -/

theorem child_of_end (x : Fin n) {e : Fin m} (he : e ∈ Q) {w : Fin n} (hw : w ∈ ends e)
    (hwK : w ∈ Kx st x e) : child st x e = w := by
  have h := child_spec st x he
  rw [← h.2] at hw
  unfold Kx at hwK
  rw [mem_sub] at hwK
  exact (end_in_sub (rep st x) h.1 hw hwK).symm

theorem excl_edge (x : Fin n) {U : Finset (Fin n)} (hU : ∀ u ∈ U, InArc Q D u x)
    {e e' : Fin m} (he : e ∈ Q) (he' : e' ∈ Q) (hne : e ≠ e')
    (hsub : Kx st x e' ⊆ Kx st x e) (hcU : child st x e' ∈ U) :
    sub (redir (PR st x) x U) (child st x e) ⊆ Kx st x e \ Kx st x e' := by
  have hxU := xnotU st x hU
  have hrt := (rep st x).rooted
  have h1 := child_spec st x he
  have h2 := child_spec st x he'
  have huv : child st x e' ≠ child st x e := by
    intro heq; apply hne; rw [← h1.2, ← h2.2, heq]
  have hvu : Desc (PR st x) (child st x e) (child st x e') := by
    have : child st x e' ∈ Kx st x e := hsub (by unfold Kx; rw [mem_sub]; exact desc_refl _ _)
    unfold Kx at this; rwa [mem_sub] at this
  intro y hy
  rw [mem_sub] at hy
  refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
  · unfold Kx; rw [mem_sub]; exact redir_desc hrt hxU h1.1 hy
  · intro hy'
    unfold Kx at hy'
    rw [mem_sub] at hy'
    exact redir_excl hrt hxU hcU hy' hvu huv h1.1 hy

theorem dl_le_of_sub (x : Fin n) (U : Finset (Fin n)) {e : Fin m} {B : Finset (Fin n)}
    (hB : sub (redir (PR st x) x U) (child st x e) ⊆ B) (hK : gch d (wt X d) (Kx st x e) = d) :
    dl st x U (child st x e) ≤ (wsum (wt X d) B : ℤ) - d := by
  unfold dl
  have h1 := gch_le_w d (wt X d) (sub (redir (PR st x) x U) (child st x e))
  have h2 := wsum_mono (X := X) (d := d) hB
  unfold Kx at hK
  rw [hK]
  push_cast
  omega

/-! ### Marks: `d` chosen out-neighbours of each vertex outside `X` -/

noncomputable def MK (u : Fin n) : Finset (Fin n) :=
  if hu : u ∉ X then Classical.choose (Finset.exists_subset_card_eq (card_OutSet_ge st hu))
  else ∅

theorem MK_sub (u : Fin n) : MK st u ⊆ OutSet Q D u := by
  unfold MK
  by_cases hu : u ∉ X
  · rw [dif_pos hu]
    exact (Classical.choose_spec (Finset.exists_subset_card_eq (card_OutSet_ge st hu))).1
  · rw [dif_neg hu]; exact Finset.empty_subset _

theorem MK_card {u : Fin n} (hu : u ∉ X) : (MK st u).card = d := by
  unfold MK
  rw [dif_pos hu]
  exact (Classical.choose_spec (Finset.exists_subset_card_eq (card_OutSet_ge st hu))).2

theorem MK_card_le (u : Fin n) : (MK st u).card ≤ d := by
  by_cases hu : u ∉ X
  · rw [MK_card st hu]
  · unfold MK; rw [dif_neg hu]; simp

/-! ### The path from `h` to the root `c0` -/

/-- the `i`-th ancestor of `h` -/
noncomputable def gg (h : Fin n) (i : ℕ) : Fin n := (PR st c0)^[i] h

/-- its subtree -/
noncomputable def GG (h : Fin n) (i : ℕ) : Finset (Fin n) := sub (PR st c0) (gg st h i)

/-- its parent edge -/
noncomputable def ff (h : Fin n) (i : ℕ) : Fin m := PE st c0 (gg st h i)

theorem GG_mono (h : Fin n) {i j : ℕ} (hij : i ≤ j) : GG st h i ⊆ GG st h j := by
  intro y hy
  unfold GG at hy ⊢
  rw [mem_sub] at hy ⊢
  refine desc_trans _ ⟨j - i, ?_⟩ hy
  unfold gg
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij]

theorem GG_top (h : Fin n) (y : Fin n) : y ∈ GG st h (ht (rep st c0).rooted h) := by
  unfold GG gg
  rw [ht_spec, mem_sub]
  exact (rep st c0).rooted.reach y

theorem exists_GG (h y : Fin n) : ∃ i, y ∈ GG st h i := ⟨_, GG_top st h y⟩

/-- the index of the component `F_i` of `Q - E(H)` containing `y` -/
noncomputable def pii (h y : Fin n) : ℕ := Nat.find (exists_GG st h y)

theorem mem_GG_iff (h y : Fin n) (i : ℕ) : y ∈ GG st h i ↔ pii st h y ≤ i := by
  constructor
  · intro hy; exact Nat.find_min' (exists_GG st h y) hy
  · intro hi; exact GG_mono st h hi (Nat.find_spec (exists_GG st h y))

theorem pii_le (h y : Fin n) : pii st h y ≤ ht (rep st c0).rooted h :=
  Nat.find_min' (exists_GG st h y) (GG_top st h y)

/-- the component `F_i` -/
noncomputable def FF (h : Fin n) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun y => pii st h y = i

theorem gg_ne (h : Fin n) {i : ℕ} (hi : i < ht (rep st c0).rooted h) : gg st h i ≠ c0 :=
  iter_ne_root (rep st c0).rooted h hi

theorem gg_succ (h : Fin n) (i : ℕ) : gg st h (i + 1) = PR st c0 (gg st h i) := by
  unfold gg; rw [Function.iterate_succ_apply']

theorem ht_gg (h : Fin n) {i : ℕ} (hi : i ≤ ht (rep st c0).rooted h) :
    ht (rep st c0).rooted (gg st h i) + i = ht (rep st c0).rooted h :=
  ht_iter (rep st c0).rooted h i hi

theorem gg_inj (h : Fin n) {i j : ℕ} (hi : i ≤ ht (rep st c0).rooted h)
    (hj : j ≤ ht (rep st c0).rooted h) (he : gg st h i = gg st h j) : i = j := by
  have h1 := ht_gg st h hi
  have h2 := ht_gg st h hj
  rw [he] at h1
  omega

theorem ff_mem (h : Fin n) {i : ℕ} (hi : i < ht (rep st c0).rooted h) : ff st h i ∈ Q :=
  (rep st c0).mem _ (gg_ne st h hi)

theorem ff_inj (h : Fin n) {i j : ℕ} (hi : i < ht (rep st c0).rooted h)
    (hj : j < ht (rep st c0).rooted h) (he : ff st h i = ff st h j) : i = j :=
  gg_inj st h hi.le hj.le (pe_inj (rep st c0) (gg_ne st h hi) (gg_ne st h hj) he)

theorem gg_mem_ends (h : Fin n) {i : ℕ} (hi : i < ht (rep st c0).rooted h) :
    gg st h i ∈ ends (ff st h i) := ends_mem_left (rep st c0) (gg_ne st h hi)

theorem gg_succ_mem_ends (h : Fin n) {i : ℕ} (hi : i < ht (rep st c0).rooted h) :
    gg st h (i + 1) ∈ ends (ff st h i) := by
  rw [gg_succ]; exact ends_mem_right (rep st c0) (gg_ne st h hi)

theorem gg_mem_GG (h : Fin n) (i : ℕ) : gg st h i ∈ GG st h i := by
  unfold GG; rw [mem_sub]; exact desc_refl _ _

theorem gg_succ_not_mem_GG (h : Fin n) {i : ℕ} (hi : i < ht (rep st c0).rooted h) :
    gg st h (i + 1) ∉ GG st h i := by
  unfold GG; rw [mem_sub, gg_succ]
  exact not_desc_par (rep st c0).rooted (gg_ne st h hi)

theorem side_ff (h : Fin n) {i : ℕ} (hi : i < ht (rep st c0).rooted h) (y : Fin n) :
    side ends Q (ff st h i) y = if y ∈ GG st h i then GG st h i else Finset.univ \ GG st h i := by
  unfold ff GG
  rw [side_pe st c0 (gg_ne st h hi) y]
  by_cases hy : Desc (PR st c0) (gg st h i) y
  · rw [if_pos hy, if_pos ((mem_sub _ _ _).2 hy)]
  · rw [if_neg hy, if_neg (fun h' => hy ((mem_sub _ _ _).1 h'))]

theorem Kx_ff (h : Fin n) {i : ℕ} (hi : i < ht (rep st c0).rooted h) (x : Fin n) :
    Kx st x (ff st h i) = if x ∈ GG st h i then Finset.univ \ GG st h i else GG st h i := by
  have hK : Kx st x (ff st h i) = Finset.univ \ side ends Q (ff st h i) x := by
    rw [side_x st x (ff_mem st h hi), Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
  rw [hK, side_ff st h hi x]
  split_ifs
  · rfl
  · exact Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)

section Heavy

variable {h : Fin n}
  (hheavy : ∀ v, v ≠ c0 → Desc (PR st c0) v h → d ≤ wsum (wt X d) (sub (PR st c0) v))

include hheavy

theorem GG_heavy {i : ℕ} (hi : i < ht (rep st c0).rooted h) :
    d ≤ wsum (wt X d) (GG st h i) ∧ d ≤ wsum (wt X d) (Finset.univ \ GG st h i) := by
  refine ⟨hheavy _ (gg_ne st h hi) ⟨i, rfl⟩, ?_⟩
  have hc0 : c0 ∈ Finset.univ \ GG st h i := by
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold GG; rw [mem_sub]
    exact not_desc_root (rep st c0).rooted (gg_ne st h hi)
  have := wsum_ge_of_mem (X := X) (d := d) hc0
  simp [wt, st.hc0] at this
  exact this

theorem gch_Kx_ff {i : ℕ} (hi : i < ht (rep st c0).rooted h) (x : Fin n) :
    gch d (wt X d) (Kx st x (ff st h i)) = d := by
  have hh := GG_heavy st hheavy hi
  rw [Kx_ff st h hi x]
  split_ifs
  · rw [gch_compl]; exact gch_heavy hh.1 hh.2
  · exact gch_heavy hh.1 hh.2

theorem small_ff {i : ℕ} (hi : i < ht (rep st c0).rooted h) : small ends Q X d (ff st h i) = ∅ := by
  have hh := GG_heavy st hheavy hi
  rw [Finset.eq_empty_iff_forall_notMem]
  intro y hy
  rw [small, Finset.mem_filter, side_ff st h hi y] at hy
  split_ifs at hy <;> omega

/-! ### The edge charged by a far marked arc -/

/-- the saturated edge whose cut loses the subtree of `g_t` when `g_t` is redirected to `x` -/
noncomputable def eps (x : Fin n) (t : ℕ) : Fin m :=
  if t + 2 ≤ pii st h x then ff st h (t + 1) else ff st h (t - 2)

/-- the index of the component that then contains the new cut side -/
noncomputable def phi (x : Fin n) (t : ℕ) : ℕ :=
  if t + 2 ≤ pii st h x then t + 1 else t - 1

omit hheavy in
theorem phi_le (x : Fin n) (t : ℕ) : phi st (h := h) x t = t + 1 ∨ phi st (h := h) x t = t - 1 := by
  unfold phi; split_ifs <;> simp

theorem eps_spec (x : Fin n) {t : ℕ} (ht' : t ≤ ht (rep st c0).rooted h)
    (hin : gg st h t ∈ InSet Q D x)
    (hcase : t + 2 ≤ pii st h x ∨ pii st h x + 2 ≤ t) :
    eps st (h := h) x t ∈ Q ∧ small ends Q X d (eps st (h := h) x t) = ∅ ∧
      dl st x (InSet Q D x) (child st x (eps st (h := h) x t)) ≤
        (wsum (wt X d) (FF st h (phi st (h := h) x t)) : ℤ) - d := by
  have hU := InSet_ok st x
  have hpl := pii_le st h x
  set L := ht (rep st c0).rooted h with hL
  by_cases hA : t + 2 ≤ pii st h x
  · simp only [eps, phi, if_pos hA]
    have hi1 : t + 1 < L := by omega
    have hi0 : t < L := by omega
    have hx1 : x ∉ GG st h (t + 1) := by rw [mem_GG_iff]; omega
    have hx0 : x ∉ GG st h t := by rw [mem_GG_iff]; omega
    have hK1 : Kx st x (ff st h (t + 1)) = GG st h (t + 1) := by
      rw [Kx_ff st h hi1, if_neg hx1]
    have hK0 : Kx st x (ff st h t) = GG st h t := by rw [Kx_ff st h hi0, if_neg hx0]
    have hch : child st x (ff st h t) = gg st h t :=
      child_of_end st x (ff_mem st h hi0) (gg_mem_ends st h hi0) (by rw [hK0]; exact gg_mem_GG st h t)
    have hne : ff st h (t + 1) ≠ ff st h t := fun he => by
      have := ff_inj st h hi1 hi0 he; omega
    have hex := excl_edge st x hU (ff_mem st h hi1) (ff_mem st h hi0) hne
      (by rw [hK0, hK1]; exact GG_mono st h (by omega)) (by rw [hch]; exact hin)
    refine ⟨ff_mem st h hi1, small_ff st hheavy hi1, dl_le_of_sub st x _ (hex.trans ?_)
      (gch_Kx_ff st hheavy hi1 x)⟩
    intro y hy
    rw [hK0, hK1, Finset.mem_sdiff, mem_GG_iff, mem_GG_iff] at hy
    simp only [FF, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · have hB : pii st h x + 2 ≤ t := hcase.resolve_left hA
    simp only [eps, phi, if_neg hA]
    have hi2 : t - 2 < L := by omega
    have hi1 : t - 1 < L := by omega
    have hx2 : x ∈ GG st h (t - 2) := by rw [mem_GG_iff]; omega
    have hx1 : x ∈ GG st h (t - 1) := by rw [mem_GG_iff]; omega
    have hK2 : Kx st x (ff st h (t - 2)) = Finset.univ \ GG st h (t - 2) := by
      rw [Kx_ff st h hi2, if_pos hx2]
    have hK1 : Kx st x (ff st h (t - 1)) = Finset.univ \ GG st h (t - 1) := by
      rw [Kx_ff st h hi1, if_pos hx1]
    have ht1 : t - 1 + 1 = t := by omega
    have hch : child st x (ff st h (t - 1)) = gg st h t := by
      have hm := gg_succ_mem_ends st h hi1
      have hn := gg_succ_not_mem_GG st h hi1
      rw [ht1] at hm hn
      exact child_of_end st x (ff_mem st h hi1) hm
        (by rw [hK1, Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hn⟩)
    have hne : ff st h (t - 2) ≠ ff st h (t - 1) := fun he => by
      have := ff_inj st h hi2 hi1 he; omega
    have hex := excl_edge st x hU (ff_mem st h hi2) (ff_mem st h hi1) hne
      (by
        rw [hK1, hK2]
        exact Finset.sdiff_subset_sdiff (subset_refl _) (GG_mono st h (by omega)))
      (by rw [hch]; exact hin)
    refine ⟨ff_mem st h hi2, small_ff st hheavy hi2, dl_le_of_sub st x _ (hex.trans ?_)
      (gch_Kx_ff st hheavy hi2 x)⟩
    intro y hy
    rw [hK1, hK2, Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_sdiff, mem_GG_iff,
      mem_GG_iff] at hy
    simp only [FF, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.mem_univ, true_and, not_le, not_not] at hy
    omega

/-- the far marked arcs at `x` -/
noncomputable def Valid (x : Fin n) : Finset ℕ :=
  (Finset.range (ht (rep st c0).rooted h + 1)).filter fun t =>
    gg st h t ∉ X ∧ x ∈ MK st (gg st h t) ∧ (t + 2 ≤ pii st h x ∨ pii st h x + 2 ≤ t)

/-- all marked arcs at `x` from the path -/
noncomputable def Pre (x : Fin n) : Finset ℕ :=
  (Finset.range (ht (rep st c0).rooted h + 1)).filter fun t =>
    gg st h t ∉ X ∧ x ∈ MK st (gg st h t)

theorem eps_inj (x : Fin n) : Set.InjOn (eps st (h := h) x) (Valid st (h := h) x) := by
  intro t ht' t' ht'' he
  simp only [Valid, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ht' ht''
  set L := ht (rep st c0).rooted h
  have hpl := pii_le st h x
  unfold eps at he
  split_ifs at he with h1 h2 h2
  · have := ff_inj st h (by omega) (by omega) he; omega
  · have := ff_inj st h (by omega) (by omega) he; omega
  · have := ff_inj st h (by omega) (by omega) he; omega
  · have := ff_inj st h (by omega) (by omega) he; omega

/-- per root: the saturated edges change by at most the far-marked-arc terms -/
theorem sat_sum_le (x : Fin n) :
    ∑ e ∈ Q.filter (fun e => ¬ (small ends Q X d e).Nonempty),
        dl st x (InSet Q D x) (child st x e) ≤
      ∑ t ∈ Valid st (h := h) x, ((wsum (wt X d) (FF st h (phi st (h := h) x t)) : ℤ) - d) := by
  have hvalid : ∀ t ∈ Valid st (h := h) x, gg st h t ∈ InSet Q D x ∧
      t ≤ ht (rep st c0).rooted h ∧ (t + 2 ≤ pii st h x ∨ pii st h x + 2 ≤ t) := by
    intro t ht'
    simp only [Valid, Finset.mem_filter, Finset.mem_range] at ht'
    exact ⟨MK_sub st _ ht'.2.2.1 |> (mem_OutSet _ _).1 |> (mem_InSet _ _).2, by omega, ht'.2.2.2⟩
  have hsub : (Valid st (h := h) x).image (eps st (h := h) x) ⊆
      Q.filter (fun e => ¬ (small ends Q X d e).Nonempty) := by
    intro e he
    obtain ⟨t, ht', rfl⟩ := Finset.mem_image.1 he
    obtain ⟨h1, h2, h3⟩ := hvalid t ht'
    obtain ⟨hm, hs, -⟩ := eps_spec st hheavy x h2 h1 h3
    rw [Finset.mem_filter, hs]
    exact ⟨hm, Finset.not_nonempty_empty⟩
  rw [← Finset.sum_sdiff hsub, Finset.sum_image (eps_inj st hheavy x)]
  have hrest : ∑ e ∈ Q.filter (fun e => ¬ (small ends Q X d e).Nonempty) \
      (Valid st (h := h) x).image (eps st (h := h) x), dl st x (InSet Q D x) (child st x e) ≤ 0 := by
    apply Finset.sum_nonpos
    intro e he
    rw [Finset.mem_sdiff, Finset.mem_filter] at he
    exact dl_sat st he.1.1 (Finset.not_nonempty_iff_eq_empty.1 he.1.2) x _
  have hmain := Finset.sum_le_sum fun t (ht' : t ∈ Valid st (h := h) x) =>
    (eps_spec st hheavy x (hvalid t ht').2.1 (hvalid t ht').1 (hvalid t ht').2.2).2.2
  linarith

end Heavy

end Setting

end LowDiameterNashWilliams.Main.Dev.L42
end

section
/-! Lemma 4.2 (existence), part F: the counting that turns the per-root bounds of part E into
the bound on the saturated middle, `d (depth h + 1) ≤ 4 d |X| + 11 n`, and then the depth
bound `d · depth y ≤ 4 d |X| + 13 n + d` for every vertex `y` (root `c0`). -/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L42
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33
open LowDiameterNashWilliams.Main.Dev.L41

variable {n m : ℕ}

theorem wsum_univ_le (X : Finset (Fin n)) (d : ℕ) :
    wsum (wt X d) Finset.univ ≤ d * X.card + 2 * n := by
  unfold wsum wt
  have : ∀ y : Fin n, (if y ∈ X then d else 2) ≤ (if y ∈ X then d else 0) + 2 := by
    intro y; split_ifs <;> omega
  refine (Finset.sum_le_sum fun y _ => this y).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, smul_eq_mul]
  simp [mul_comm]

section Setting

variable {ends : Fin m → Sym2 (Fin n)} {Q : Finset (Fin m)} {D : Direction n m}
  {X : Finset (Fin n)} {d : ℕ} {c0 : Fin n} (st : Setup ends Q D X d c0)

include st

theorem sum_FF (h : Fin n) :
    ∑ i ∈ Finset.range (ht (rep st c0).rooted h + 2), wsum (wt X d) (FF st h i) =
      wsum (wt X d) Finset.univ := by
  unfold wsum FF
  exact Finset.sum_fiberwise_of_maps_to (g := pii st h)
    (fun y _ => Finset.mem_range.2 (by have := pii_le st h y; omega)) _

theorem sum_FF_shift (h : Fin n) :
    ∑ t ∈ Finset.range (ht (rep st c0).rooted h + 1),
        (wsum (wt X d) (FF st h (t + 1)) + wsum (wt X d) (FF st h (t - 1))) ≤
      3 * wsum (wt X d) Finset.univ := by
  have hS := sum_FF st h
  set L := ht (rep st c0).rooted h
  rw [Finset.sum_add_distrib]
  have h1 : ∑ t ∈ Finset.range (L + 1), wsum (wt X d) (FF st h (t + 1)) ≤
      wsum (wt X d) Finset.univ := by
    rw [← hS, Finset.sum_range_succ' (fun i => wsum (wt X d) (FF st h i)) (L + 1)]
    exact Nat.le_add_right _ _
  have h2 : ∑ t ∈ Finset.range (L + 1), wsum (wt X d) (FF st h (t - 1)) ≤
      2 * wsum (wt X d) Finset.univ := by
    rw [Finset.sum_range_succ' (fun t => wsum (wt X d) (FF st h (t - 1)))]
    simp only [Nat.add_sub_cancel, Nat.zero_sub]
    have h3 : ∑ i ∈ Finset.range L, wsum (wt X d) (FF st h i) ≤
        ∑ i ∈ Finset.range (L + 2), wsum (wt X d) (FF st h i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun _ _ _ =>
        Nat.zero_le _
    have h4 : wsum (wt X d) (FF st h 0) ≤ ∑ i ∈ Finset.range (L + 2), wsum (wt X d) (FF st h i) :=
      Finset.single_le_sum (f := fun i => wsum (wt X d) (FF st h i)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (by omega))
    rw [hS] at h3 h4
    omega
  exact (add_le_add h1 h2).trans (by omega)

section Heavy

variable {h : Fin n}
  (hheavy : ∀ v, v ≠ c0 → Desc (PR st c0) v h → d ≤ wsum (wt X d) (sub (PR st c0) v))

include hheavy

omit hheavy in
theorem Valid_sub_Pre (x : Fin n) : Valid st (h := h) x ⊆ Pre st (h := h) x := by
  intro t ht'
  simp only [Valid, Pre, Finset.mem_filter] at ht' ⊢
  exact ⟨ht'.1, ht'.2.1, ht'.2.2.1⟩

omit hheavy in
theorem sum_Pre_swap (f : ℕ → ℕ) :
    ∑ x, ∑ t ∈ Pre st (h := h) x, f t ≤
      d * ∑ t ∈ Finset.range (ht (rep st c0).rooted h + 1), f t := by
  unfold Pre
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have : ∀ x, (if gg st h t ∉ X ∧ x ∈ MK st (gg st h t) then f t else 0) ≤
      (if x ∈ MK st (gg st h t) then f t else 0) := by
    intro x; split_ifs <;> simp_all
  refine (Finset.sum_le_sum fun x _ => this x).trans ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (MK_card_le st _)

omit hheavy in
theorem sum_Pre_card :
    d * (ht (rep st c0).rooted h + 1) ≤ ∑ x, (Pre st (h := h) x).card + d * X.card := by
  set L := ht (rep st c0).rooted h
  have hswap : ∑ x, (Pre st (h := h) x).card =
      ∑ t ∈ Finset.range (L + 1), if gg st h t ∉ X then d else 0 := by
    unfold Pre
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht' : gg st h t ∉ X
    · rw [if_pos ht', ← Finset.card_filter]
      have : (Finset.univ.filter fun x => gg st h t ∉ X ∧ x ∈ MK st (gg st h t)) =
          MK st (gg st h t) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨fun h' => h'.2,
          fun h' => ⟨ht', h'⟩⟩
      rw [this, MK_card st ht']
    · rw [if_neg ht']
      exact Finset.sum_eq_zero fun x _ => if_neg fun h' => ht' h'.1
  rw [hswap, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  have hX : ((Finset.range (L + 1)).filter fun t => ¬ gg st h t ∉ X).card ≤ X.card := by
    apply Finset.card_le_card_of_injOn (gg st h)
    · intro t ht'
      simp only [Finset.coe_filter, Finset.mem_range, not_not, Set.mem_setOf_eq] at ht'
      exact ht'.2
    · intro t ht' t' ht'' he
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ht' ht''
      exact gg_inj st h (by omega) (by omega) he
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range (L + 1))
    (fun t => gg st h t ∉ X)
  rw [Finset.card_range] at hsplit
  have : d * (L + 1) = d * ((Finset.range (L + 1)).filter fun t => gg st h t ∉ X).card +
      d * ((Finset.range (L + 1)).filter fun t => ¬ gg st h t ∉ X).card := by
    rw [← mul_add, hsplit]
  rw [this, mul_comm _ d]
  have := Nat.mul_le_mul_left d hX
  omega

omit hheavy in
theorem Pre_le_Valid (x : Fin n) :
    (Pre st (h := h) x).card ≤ (Valid st (h := h) x).card + 3 := by
  have hV : Valid st (h := h) x = (Pre st (h := h) x).filter
      (fun t => t + 2 ≤ pii st h x ∨ pii st h x + 2 ≤ t) := by
    unfold Valid Pre; rw [Finset.filter_filter]; simp only [and_assoc]
  have hsplit := Finset.card_filter_add_card_filter_not (s := Pre st (h := h) x)
    (fun t => t + 2 ≤ pii st h x ∨ pii st h x + 2 ≤ t)
  have hbad : ((Pre st (h := h) x).filter
      (fun t => ¬ (t + 2 ≤ pii st h x ∨ pii st h x + 2 ≤ t))).card ≤ 3 := by
    have hsub : ((Pre st (h := h) x).filter
        (fun t => ¬ (t + 2 ≤ pii st h x ∨ pii st h x + 2 ≤ t))) ⊆
        {pii st h x - 1, pii st h x, pii st h x + 1} := by
      intro t ht'
      rw [Finset.mem_filter] at ht'
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact (Finset.card_le_card hsub).trans Finset.card_le_three
  rw [hV]
  omega

/-- second estimate: the saturated middle -/
theorem mid_bound : d * (ht (rep st c0).rooted h + 1) ≤ 4 * d * X.card + 11 * n := by
  set L := ht (rep st c0).rooted h
  set W := wsum (wt X d) Finset.univ with hW
  have h0 := total_split st
  have h1 := light_total_le st
  have hs0 : (0 : ℤ) ≤ ∑ y, (rr ends Q X d y : ℤ) := Finset.sum_nonneg fun _ _ => by positivity
  -- saturated part
  have h2 : ∑ x, ∑ e ∈ Q.filter (fun e => ¬ (small ends Q X d e).Nonempty),
      dl st x (InSet Q D x) (child st x e) ≤
      ∑ x, ∑ t ∈ Valid st (h := h) x,
        ((wsum (wt X d) (FF st h (phi st (h := h) x t)) : ℤ) - d) :=
    Finset.sum_le_sum fun x _ => sat_sum_le st hheavy x
  have h3 : ∑ x, ∑ t ∈ Valid st (h := h) x,
      ((wsum (wt X d) (FF st h (phi st (h := h) x t)) : ℤ) - d) =
      (∑ x, ∑ t ∈ Valid st (h := h) x, wsum (wt X d) (FF st h (phi st (h := h) x t)) : ℕ) -
        (d : ℤ) * ∑ x, ((Valid st (h := h) x).card : ℤ) := by
    push_cast
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- (A): the weights of the components
  have hA : ∑ x, ∑ t ∈ Valid st (h := h) x, wsum (wt X d) (FF st h (phi st (h := h) x t)) ≤
      d * (3 * W) := by
    have hpt : ∀ x, ∑ t ∈ Valid st (h := h) x, wsum (wt X d) (FF st h (phi st (h := h) x t)) ≤
        ∑ t ∈ Pre st (h := h) x,
          (wsum (wt X d) (FF st h (t + 1)) + wsum (wt X d) (FF st h (t - 1))) := by
      intro x
      refine (Finset.sum_le_sum fun t _ => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Valid_sub_Pre st x) fun _ _ _ => Nat.zero_le _)
      rcases phi_le st (h := h) x t with he | he <;> rw [he] <;> omega
    refine (Finset.sum_le_sum fun x _ => hpt x).trans ((sum_Pre_swap st _).trans ?_)
    exact Nat.mul_le_mul_left d (sum_FF_shift st h)
  -- (B): the number of far marked arcs
  have hB : d * (L + 1) ≤ ∑ x, (Valid st (h := h) x).card + 3 * n + d * X.card := by
    have h4 : d * (L + 1) ≤ ∑ x, (Pre st (h := h) x).card + d * X.card := sum_Pre_card st
    have h5 : ∑ x, (Pre st (h := h) x).card ≤ ∑ x, ((Valid st (h := h) x).card + 3) :=
      Finset.sum_le_sum fun x _ => Pre_le_Valid st x
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h5
    omega
  have hWle := wsum_univ_le X d
  have hQ := tree_card ends st.hQ
  have hd : (1 : ℤ) ≤ d := by exact_mod_cast st.hd
  -- combine
  have hBz : (d : ℤ) * (L + 1) ≤ ∑ x, ((Valid st (h := h) x).card : ℤ) + 3 * n + d * X.card := by
    exact_mod_cast hB
  have hAz : ((∑ x, ∑ t ∈ Valid st (h := h) x,
      wsum (wt X d) (FF st h (phi st (h := h) x t)) : ℕ) : ℤ) ≤ d * (3 * W) := by
    exact_mod_cast hA
  have hWz : (W : ℤ) ≤ d * X.card + 2 * n := by exact_mod_cast hWle
  have hQz : (Q.card : ℤ) + 1 = n := by exact_mod_cast hQ
  have key : (d : ℤ) * (d * (L + 1)) ≤ (d : ℤ) * (4 * d * X.card + 11 * n) := by
    nlinarith
  have := le_of_mul_le_mul_left key (by omega)
  exact_mod_cast this

end Heavy

/-! ### Depth bound -/

theorem rr_c0 (y : Fin n) :
    rr ends Q X d y = ((Finset.univ.erase c0).filter fun v =>
      Desc (PR st c0) v y ∧ wsum (wt X d) (sub (PR st c0) v) < d).card := by
  have h := rr_root st c0 y
  rw [Finset.card_filter]
  have : ∀ v ∈ Finset.univ.erase c0,
      (if wsum (wt X d) (side ends Q (PE st c0 v) y) < d then (1 : ℤ) else 0) =
      ((if Desc (PR st c0) v y ∧ wsum (wt X d) (sub (PR st c0) v) < d then 1 else 0 : ℕ) : ℤ) := by
    intro v hv
    have hvc := (Finset.mem_erase.1 hv).1
    rw [side_pe st c0 hvc y]
    by_cases hd : Desc (PR st c0) v y
    · simp only [hd, if_true, true_and]; split_ifs <;> simp
    · simp only [hd, if_false, false_and]
      have hc0 : c0 ∈ Finset.univ \ sub (PR st c0) v := by
        rw [Finset.mem_sdiff, mem_sub]
        exact ⟨Finset.mem_univ _, not_desc_root (rep st c0).rooted hvc⟩
      have := wsum_ge_of_mem (X := X) (d := d) hc0
      simp only [wt, st.hc0, if_true] at this
      rw [if_neg (not_lt.2 this)]; simp
  rw [Finset.sum_congr rfl this] at h
  exact_mod_cast h

/-- a deepest vertex below `y` is a leaf, and has at least as many small sides as `y` -/
theorem rr_le_leaf (y : Fin n) : ∃ a, degIn ends Q a = 1 ∧ rr ends Q X d y ≤ rr ends Q X d a ∨
    rr ends Q X d y = 0 := by
  by_cases hy : y = c0
  · refine ⟨y, Or.inr ?_⟩
    rw [rr_c0 st, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv hd
    exact (Finset.mem_erase.1 hv).1 (desc_root_eq (rep st c0).rooted (hy ▸ hd.1))
  have hrt := (rep st c0).rooted
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (sub (PR st c0) y) (ht hrt)
    ⟨y, (mem_sub _ _ _).2 (desc_refl _ _)⟩
  rw [mem_sub] at ha
  have hac : a ≠ c0 := fun h' => hy (desc_root_eq hrt (h' ▸ ha))
  -- no child
  have hnochild : ∀ c, c ≠ c0 → PR st c0 c ≠ a := by
    intro c hc hpc
    have hcy : c ∈ sub (PR st c0) y := by
      rw [mem_sub]; exact desc_trans _ ha (by rw [← hpc]; exact desc_par_self _ c)
    have := hmax c hcy
    have := ht_par hrt hc
    rw [hpc] at this
    omega
  refine ⟨a, Or.inl ⟨?_, ?_⟩⟩
  · unfold degIn
    rw [Finset.card_eq_one]
    refine ⟨PE st c0 a, ?_⟩
    ext e
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨he, hae⟩
      obtain ⟨v, hv, rfl⟩ := (rep st c0).surj e he
      rw [(rep st c0).ends_eq v hv, Sym2.mem_iff] at hae
      rcases hae with rfl | hae
      · rfl
      · exact absurd hae.symm (hnochild v hv)
    · rintro rfl
      exact ⟨(rep st c0).mem a hac, ends_mem_left (rep st c0) hac⟩
  · rw [rr_c0 st, rr_c0 st]
    apply Finset.card_le_card
    intro v hv
    simp only [Finset.mem_filter] at hv ⊢
    exact ⟨hv.1, desc_trans _ hv.2.1 ha, hv.2.2⟩

theorem depth_bound (y : Fin n) :
    d * ht (rep st c0).rooted y ≤ 4 * d * X.card + 13 * n + d := by
  have hrt := (rep st c0).rooted
  have hs := s_le st
  have hQ := tree_card ends st.hQ
  -- `r(y)` bound
  have hry : d * rr ends Q X d y ≤ 2 * n + d := by
    obtain ⟨a, ha⟩ := rr_le_leaf st y
    rcases ha with ⟨hleaf, hle⟩ | h0
    · have := leaf_bound st hleaf
      have := Nat.mul_le_mul_left d hle
      omega
    · rw [h0]; omega
  -- split the ancestors into light and heavy
  set A := (Finset.univ.erase c0).filter fun v => Desc (PR st c0) v y with hA
  have hcard : A.card = ht hrt y := card_anc hrt y
  set S := A.filter fun v => d ≤ wsum (wt X d) (sub (PR st c0) v) with hS
  have hsplit : A.card = rr ends Q X d y + S.card := by
    rw [rr_c0 st, hS, ← Finset.card_filter_add_card_filter_not
      (s := A) (fun v => d ≤ wsum (wt X d) (sub (PR st c0) v)), add_comm]
    congr 2
    rw [hA, Finset.filter_filter]
    simp only [not_le]
  by_cases hSe : S.Nonempty
  · obtain ⟨h, hh, hmax⟩ := Finset.exists_max_image S (ht hrt) hSe
    simp only [hS, hA, Finset.mem_filter, Finset.mem_erase] at hh
    -- every heavy ancestor of `y` is an ancestor of `h`
    have hSsub : S ⊆ (Finset.univ.erase c0).filter fun v => Desc (PR st c0) v h := by
      intro v hv
      have hv' := hv
      simp only [hS, hA, Finset.mem_filter, Finset.mem_erase] at hv'
      refine Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hv'.1.1.1, Finset.mem_univ _⟩, ?_⟩
      rcases desc_chain _ hv'.1.2 hh.1.2 with h1 | h1
      · exact h1
      · by_cases hvh : h = v
        · rw [hvh]; exact desc_refl _ _
        · have := ht_lt_of_desc hrt h1 hvh
          have := hmax v hv
          omega
    have hSle : S.card ≤ ht hrt h := by
      have := Finset.card_le_card hSsub
      rwa [card_anc hrt h] at this
    have hheavy : ∀ v, v ≠ c0 → Desc (PR st c0) v h → d ≤ wsum (wt X d) (sub (PR st c0) v) := by
      intro v _ hvh
      refine hh.2.trans (wsum_mono ?_)
      intro z hz
      rw [mem_sub] at hz ⊢
      exact desc_trans _ hvh hz
    have hmid := mid_bound st hheavy
    have : d * ht hrt y ≤ d * rr ends Q X d y + d * ht hrt h := by
      rw [← mul_add]; exact Nat.mul_le_mul_left d (by omega)
    have : d * ht hrt h + d ≤ 4 * d * X.card + 11 * n := by
      rw [mul_add, mul_one] at hmid; exact hmid
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hSe
    rw [hSe, Finset.card_empty] at hsplit
    have : ht hrt y = rr ends Q X d y := by omega
    rw [this]
    omega

end Setting

end LowDiameterNashWilliams.Main.Dev.L42
end

section
/-!
# Lemma 4.2, existential half (outdegree-preserving shortening), with `C_D = 40`

Notation: `N = n`, `X' = X ∪ {c0}` with `c0 = 0`; `X'` still satisfies the hypothesis
(`d ≤ outdeg v` for `v ∉ X'`) and `|X'| ≤ |X| + 1`.

**Trivial case `X' = V`.** Keep `(T, D)`. Rooting `T` at `c0`, every vertex has depth
`≤ n - 1 ≤ |X|`, so every distance is `≤ 2 |X| ≤ 40 (|X| + n/d)`.

**Otherwise.** Some `v ∉ X'` has `d ≤ outdeg v ≤ n` (heads of distinct complementary arcs at
`v` are distinct, `card_OutSet`), so `d ≤ n`. Weights: `wt = d` on `X'`, `2` elsewhere;
`w(A) = Σ_{y ∈ A} wt y`. Charge of a cut side `A`: `g(A) = min(d, w(A), w(V∖A))`
(`g(A) = g(V∖A)`). Potential of a spanning tree `S`: `ϕ(S) = Σ_{e ∈ S} g(side of S - e)`.
A *feasible pair* `(S, D_S)`: `S` a spanning tree, `D_S` orients `E ∖ S`, same outdegrees as
`(T, D)`. These form a finite nonempty set; take `(Q, D_Q)` minimizing `ϕ` (`Setup`).

*Rooted form (L42A/B).* For a root `x`, `Q` is a parent map `par` (`par x = x`, iterates reach
`x`) with parent edges `pe`; the side of `pe v` away from `x` is the subtree `sub v`
(`cut_iff`), so `ϕ(Q) = Σ_{v ≠ x} g(sub v)` (`pot_rep`).

*Move `(x, U)`* (`U` ⊆ in-neighbours of `x` in `D_Q`): redirect every `u ∈ U` to `x` (new
parent edge = the arc `(u,x)`; the old parent edge becomes the arc `u → par u`). This is
again a feasible pair (`move`), with `ϕ = Σ_{v ≠ x} g(sub' v)`, where (`redir_*`)
`sub' v ⊆ sub v`, and `sub' v` misses `sub u` for every `u ∈ U` strictly below `v`, and
contains every other vertex of `sub v`. Minimality: `Σ_{v≠x} (g(sub' v) - g(sub v)) ≥ 0`
(`key`). Write `δ_x(e)` for the term of the tree edge `e`.

*Small sides.* Since `c0 ∈ X'` has weight `d`, a side of weight `< d` (a *small side*) misses
`X'` (so has weight `2 |A|`), and the other side has weight `≥ d`. An edge with a small
side is *light* (`g = 2|A|`), otherwise *saturated* (`g = d`, so `δ_x(e) ≤ 0`, `dl_sat`).
`r(y)` = number of small sides containing `y`; `s = Σ_y r(y) = Σ_e |A_e|`.

**Estimate 1 (`light_sum`, `s_le`).** Use `U = In(x)` for every `x`. Fix a light edge `e`
with small side `A`, `a = |A| ≥ 1`, and `c` its end in `A`. For `x ∈ A`: `δ_x(e) ≤ d - 2a`.
For `x ∉ A`: the new side is inside `A` and misses `In(x) ∩ (A ∖ c)`, so
`δ_x(e) ≤ -2 |In(x) ∩ (A ∖ c)|`. Every `u ∈ A ∖ c` has `≥ d` out-neighbours, at most
`a - 1` of them in `A`. Summing:
`Σ_x δ_x(e) ≤ a(d - 2a) - 2(a - 1)(d - a + 1) = 2d - da - 4a + 2 ≤ 2d - da`.
So `0 ≤ Σ_x Σ_e δ_x(e) ≤ Σ_{e light} (2d - d a_e) ≤ 2d|Q| - d s`, i.e. `s ≤ 2|Q| < 2n`.

**Estimate 3 (`rr_leaf`, `leaf_bound`).** For a leaf `a` with `r(a) > 0` (so `a ∉ X'`) and
an out-neighbour `x`, the move `(x, {a})` changes only the cuts between `a` and `x`: each
small side containing `a` but not `x` (except the leaf cut itself) loses `2`, each small side
containing `x` but not `a` gains `≤ 2`, the rest cannot gain. Hence
`0 ≤ 2 (r(x) - r(a) + 1)`. Over the `≥ d` out-neighbours: `d (r(a) - 1) ≤ s`, so
`d r(a) ≤ s + d ≤ 2n + d`.

**Estimate 2 (`mid_bound`).** Root at `c0`. Let `h` be a vertex such that every ancestor
`v ≠ c0` of `h` (including `h`) has `w(sub v) ≥ d`; let `g_0 = h, …, g_L = c0` be the path
(`L = depth h`), `G_i = sub g_i` (increasing, `G_L = V`), `F_i = G_i ∖ G_{i-1}`, `π(y)` the
index with `y ∈ F_{π(y)}`, and `f_i` the parent edge of `g_i` (`i < L`, saturated: both
sides weigh `≥ d`). Mark exactly `d` out-neighbours `M(u)` of each `u ∉ X'`. Fix a root `x`,
`j = π(x)`, and a *far* marked arc `(g_t, x)`: `g_t ∉ X'`, `x ∈ M(g_t)`, `|t - j| ≥ 2`.
 - `t + 2 ≤ j`: the side of `f_{t+1}` away from `x` is `G_{t+1}`, that of `f_t` is `G_t`,
   whose child end is `g_t ∈ In(x)`; so the new side of `f_{t+1}` is inside `F_{t+1}` and
   `δ_x(f_{t+1}) ≤ w(F_{t+1}) - d`.
 - `j + 2 ≤ t`: the sides away from `x` are `V ∖ G_{t-2} ⊇ V ∖ G_{t-1}`, the latter with
   child end `g_t`; so `δ_x(f_{t-2}) ≤ w(F_{t-1}) - d`.
Distinct far arcs at `x` charge distinct saturated edges; other saturated edges have
`δ ≤ 0` (`sat_sum_le`). Summing over `x` (`W = w(V) ≤ d|X'| + 2n`):
 - `Σ_x Σ_far w(F) ≤ Σ_t d (w(F_{t+1}) + w(F_{t-1})) ≤ 3 d W` (`sum_FF_shift`);
 - `#far ≥ d (L + 1 - |X'|) - 3n` (at most three `t` are near `j`, `Pre_le_Valid`).
With Estimate 1's light part `≤ 2d|Q|`:
`0 ≤ 2d|Q| + 3dW - d (d (L+1) - d|X'| - 3n)`, so
`d (L + 1) ≤ 2|Q| + 3W + d|X'| + 3n ≤ 4 d |X'| + 11 n`.

**Depth (`depth_bound`).** For any `y`, its ancestors `v ≠ c0` number `depth y`; those with
`w(sub v) < d` are exactly the small sides containing `y` (`c0` lies in no small side), so
they number `r(y) ≤ r(a)` for a deepest vertex `a` below `y`, a leaf; the heavy ones are
ancestors of the deepest heavy one `h`, which satisfies the hypothesis of Estimate 2. So
`d depth(y) ≤ (2n + d) + (4 d |X'| + 11 n - d) = 4 d |X'| + 13 n` (or `≤ 2n + d` if there is
no heavy ancestor); in all cases `d depth(y) ≤ 4 d |X'| + 13 n + d`.

**Diameter.** `dist(y, z) ≤ depth y + depth z`, so with `|X'| ≤ |X| + 1` and `d ≤ n`:
`d dist ≤ 8 d |X| + 8d + 26 n + 2d ≤ 8 d |X| + 36 n`, i.e.
`dist ≤ 8 |X| + 36 n/d ≤ 40 (|X| + n/d)`. The pair `(Q, D_Q)` is feasible, so it keeps every
outdegree.
-/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L42
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33
open LowDiameterNashWilliams.Main.Dev.L41

variable {n m : ℕ}

theorem diam_le_of_walks (ends : Fin m → Sym2 (Fin n)) (Q : Finset (Fin m)) (B : ℝ)
    (h : ∀ y z, ∃ p : (edgeGraph ends Q).Walk y z, (p.length : ℝ) ≤ B) :
    diameter ends Q ≤ ENNReal.ofReal B := by
  unfold diameter
  refine iSup_le fun y => iSup_le fun z => ?_
  obtain ⟨p, hp⟩ := h y z
  unfold distance
  refine (iInf_le _ p).trans ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hp

/-- walks through the root of a represented tree -/
theorem walks_via_root (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) {Q : Finset (Fin m)}
    {x : Fin n} {par : Fin n → Fin n} {pe : Fin n → Fin m} (h : Rep ends Q x par pe)
    (y z : Fin n) : ∃ p : (edgeGraph ends Q).Walk y z,
      p.length = ht h.rooted y + ht h.rooted z := by
  obtain ⟨p, hp⟩ := walk_root hs h y
  obtain ⟨q, hq⟩ := walk_root hs h z
  exact ⟨p.append q.reverse, by rw [SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_reverse, hp, hq]⟩

theorem ht_le_card {par : Fin n → Fin n} {x : Fin n} (hr : Rooted par x) (y : Fin n) :
    ht hr y + 1 ≤ n := by
  rw [← card_anc hr y]
  have := Finset.card_le_card (Finset.filter_subset (fun v => Desc par v y) (Finset.univ.erase x))
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
  have : 0 < n := Fin.pos x
  omega

end LowDiameterNashWilliams.Main.Dev.L42

namespace LowDiameterNashWilliams.Main
open LowDiameterNashWilliams.Main.Dev.L42 LowDiameterNashWilliams.Main.Dev.L33
  LowDiameterNashWilliams.Main.Dev.L41 in
theorem chk_lemma_4_2_exists :
  ∃ C_D : ℝ, 0 < C_D ∧
  ∀ n m d : ℕ, 1 ≤ n → 1 ≤ d →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Edges m) (X : Finset (Fin n)) (D : Direction n m),
  Simple ends → IsSpanningTree ends T → Orients ends (Finset.univ \ T) D →
  (∀ v, v ∉ X → d ≤ outdegree (Finset.univ \ T) D v) →
  ∃ (Q : Edges m) (D' : Direction n m), IsSpanningTree ends Q ∧
    Orients ends (Finset.univ \ Q) D' ∧
    diameter ends Q ≤ ENNReal.ofReal (C_D * (X.card + (n : ℝ) / d)) ∧
    ∀ v, outdegree (Finset.univ \ Q) D' v = outdegree (Finset.univ \ T) D v := by
  refine ⟨40, by norm_num, ?_⟩
  intro n m d hn hd ends T X D hs hT hD hdeg
  set c0 : Fin n := ⟨0, hn⟩ with hc0
  set X' := insert c0 X with hX'
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnd : (0 : ℝ) ≤ (n : ℝ) / d := by positivity
  have hXr : (0 : ℝ) ≤ X.card := by positivity
  by_cases htriv : X' = Finset.univ
  · -- trivial case: keep `T`
    refine ⟨T, D, hT, hD, ?_, fun v => rfl⟩
    have hXc : n ≤ X.card + 1 := by
      have := Finset.card_insert_le c0 X
      rw [← hX', htriv, Finset.card_univ, Fintype.card_fin] at this
      exact this
    apply diam_le_of_walks
    intro y z
    by_cases hm : 0 < m
    · obtain ⟨par, pe, hrep⟩ := exists_rep ends hs hT hm c0
      obtain ⟨p, hp⟩ := walks_via_root ends hs hrep y z
      refine ⟨p, ?_⟩
      have h1 := ht_le_card hrep.rooted y
      have h2 := ht_le_card hrep.rooted z
      have : p.length ≤ 2 * X.card := by omega
      have : (p.length : ℝ) ≤ 2 * X.card := by exact_mod_cast this
      linarith
    · have hm0 : m = 0 := by omega
      have hn1 : n = 1 := by
        have h1 := tree_card ends hT
        have h2 := Finset.card_le_univ T
        rw [Fintype.card_fin] at h2
        omega
      have hyz : y = z := by
        apply Fin.ext; have := y.isLt; have := z.isLt; omega
      subst hyz
      exact ⟨SimpleGraph.Walk.nil, by simp; positivity⟩
  · -- the main case
    obtain ⟨v0, hv0⟩ : ∃ v, v ∉ X' := by
      by_contra h'
      simp only [not_exists, not_not] at h'
      exact htriv (Finset.eq_univ_of_forall h')
    have hv0X : v0 ∉ X := fun h' => hv0 (Finset.mem_insert_of_mem h')
    have hv0c : v0 ≠ c0 := fun h' => hv0 (h' ▸ Finset.mem_insert_self c0 X)
    have hm : 0 < m := by
      have := tree_card ends hT
      have h2 : 2 ≤ n := by
        have := v0.isLt
        have : v0.val ≠ 0 := fun h' => hv0c (Fin.ext h')
        omega
      have h3 := Finset.card_le_univ T
      rw [Fintype.card_fin] at h3
      omega
    -- feasible pairs and a minimizer
    set F : Finset (Finset (Fin m) × Direction n m) := Finset.univ.filter fun p =>
      IsSpanningTree ends p.1 ∧ Orients ends (Finset.univ \ p.1) p.2 ∧
        ∀ v, outdegree (Finset.univ \ p.1) p.2 v = outdegree (Finset.univ \ T) D v with hF
    have hTF : (T, D) ∈ F := by
      rw [hF, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hT, hD, fun v => rfl⟩
    obtain ⟨⟨Q, DQ⟩, hQF, hQmin⟩ := Finset.exists_min_image F
      (fun p => pot ends d (wt X' d) c0 p.1) ⟨_, hTF⟩
    rw [hF, Finset.mem_filter] at hQF
    obtain ⟨-, hQ, hDQ, hout⟩ := hQF
    have st : Setup ends Q DQ X' d c0 := by
      refine ⟨hs, hQ, hDQ, hm, Finset.mem_insert_self c0 X, hd, ?_, ?_⟩
      · intro v hv
        rw [hout v]
        exact hdeg v (fun h' => hv (Finset.mem_insert_of_mem h'))
      · intro S D' hS hO hdS
        have hmem : (S, D') ∈ F := by
          rw [hF, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hS, hO, fun v => (hdS v).trans (hout v)⟩
        exact hQmin (S, D') hmem
    refine ⟨Q, DQ, hQ, hDQ, ?_, hout⟩
    -- `d ≤ n`
    have hdn : d ≤ n := by
      have h1 := card_OutSet_ge st hv0
      have h2 := Finset.card_le_univ (OutSet Q DQ v0)
      rw [Fintype.card_fin] at h2
      omega
    have hX'c : X'.card ≤ X.card + 1 := Finset.card_insert_le c0 X
    apply diam_le_of_walks
    intro y z
    obtain ⟨p, hp⟩ := walks_via_root ends hs (rep st c0) y z
    refine ⟨p, ?_⟩
    have hy := depth_bound st y
    have hz := depth_bound st z
    have hnat : d * p.length ≤ 8 * d * X.card + 36 * n := by
      rw [hp, mul_add]
      have : 4 * d * X'.card ≤ 4 * d * X.card + 4 * d := by
        have := Nat.mul_le_mul_left (4 * d) hX'c
        linarith
      have h8 : 8 * d * X.card = 2 * (4 * d * X.card) := by ring
      omega
    have hreal : (d : ℝ) * p.length ≤ 8 * d * X.card + 36 * n := by exact_mod_cast hnat
    have hdiv : (p.length : ℝ) ≤ 8 * X.card + 36 * ((n : ℝ) / d) := by
      have heq : (8 * (X.card : ℝ) + 36 * ((n : ℝ) / d)) = (8 * d * X.card + 36 * n) / d := by
        field_simp
      rw [heq, le_div_iff₀ hdpos]; linarith
    linarith

end LowDiameterNashWilliams.Main
end

theorem solution : type_of% @LowDiameterNashWilliams.Main.chk_lemma_4_2_exists := @LowDiameterNashWilliams.Main.chk_lemma_4_2_exists
