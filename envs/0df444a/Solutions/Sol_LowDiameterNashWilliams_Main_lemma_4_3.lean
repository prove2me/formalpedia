-- Prove2me | solution 1 for LowDiameterNashWilliams.Main.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T20:37:39.866521+00:00
-- url     : https://prove2.me/submissions/24d1b823-8d55-45a5-895c-8f3b1728e453

import Mathlib
import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Definitions.Def_LowDiameterNashWilliams_Main_Geometry
import Definitions.Def_LowDiameterNashWilliams_Main_Reserves
import Definitions.Def_LowDiameterNashWilliams_Main_Sampling
import Theorems.Thm_LowDiameterNashWilliams_Main_lemma_4_4
import Definitions.Def_LowDiameterNashWilliams_Main_Computation

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
/-! Lemma 4.1, part B: inserting an owned forest into a spanning tree by exchanges.

`F` is a set of reserve edges in which every vertex owns at most one edge, together with a
height function that strictly decreases from the owner of an edge to its other end (so the
owned edges are parent edges of a rooted forest). Inserting the parent edge of a deepest
owner `v` (whose only `F`-edge is its parent edge) into the tree and returning to `R v` the
first edge at `v` of the tree path keeps a spanning tree, keeps `|R v|`, and never removes an
edge of `F`. -/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L41
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33

variable {n m : ℕ}

end LowDiameterNashWilliams.Main.Dev.L41
end

section
/-! Lemma 4.1, part C: the merging forest and the prepared tree.

`F` is a maximum-size set of reserve edges, each joining its owner to a vertex of `A`, with at
most one edge per owner and a height function decreasing from owner to other end
(`Insertable`). Maximality: a vertex `r` owning no edge of `F` reaches through `F` every
`A`-neighbour it has in `R r`. Two vertices owning no edge of `F` are never joined by `F`
(`path_owner`), so the reserve neighbourhoods in `A` of the non-owners outside `B` are
disjoint and each has at least `d` elements: the number `c` of non-owners satisfies
`d c ≤ d |B| + |A|`, and `|F| = n - c`. Inserting `F` into `T` (part B) gives the tree `U`;
the core is `W = A ∪ B ∪ D` with `D` the ends of the `c - 1` edges of `U ∖ F`. -/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L41
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33

variable {n m : ℕ}

end LowDiameterNashWilliams.Main.Dev.L41
end

section
/-! Lemma 4.1, part D: transport of a sub-multigraph (vertex set `W ≅ Fin N`, edge set
`Ecore ≅ Fin m'`) and the core step.

The transport lemmas push adjacency, reachability and distances forward along injective
vertex and edge maps `ι`, `κ` with `Sym2.map ι (endsW i) = ends (κ i)`, and pull simplicity and
forests back. `core_step` takes the prepared tree `U` (every vertex outside `W` is a leaf of
`U` hanging on `W`), applies the shortening lemma (given as hypothesis `H42`) to the core
multigraph induced on `W`, and re-attaches the pendant edges. -/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L41
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33

variable {n m : ℕ}

/-! ### Distances -/

theorem dist_adj (ends : Fin m → Sym2 (Fin n)) (Q : Finset (Fin m)) {u u' : Fin n}
    (h : (edgeGraph ends Q).Adj u u') (v : Fin n) :
    distance ends Q u v ≤ distance ends Q u' v + 1 := by
  unfold distance
  rw [ENNReal.iInf_add]
  refine le_iInf fun p => ?_
  refine iInf_le_of_le (SimpleGraph.Walk.cons h p) ?_
  rw [SimpleGraph.Walk.length_cons]
  push_cast
  exact le_refl _

theorem dist_symm (ends : Fin m → Sym2 (Fin n)) (Q : Finset (Fin m)) (u v : Fin n) :
    distance ends Q u v = distance ends Q v u := by
  unfold distance
  apply le_antisymm
  · exact le_iInf fun p => iInf_le_of_le p.reverse (by rw [SimpleGraph.Walk.length_reverse])
  · exact le_iInf fun p => iInf_le_of_le p.reverse (by rw [SimpleGraph.Walk.length_reverse])

/-! ### Transport along `ι : Fin N → Fin n`, `κ : Fin m' → Fin m` -/

section Transport

variable {N m' : ℕ} (ends : Fin m → Sym2 (Fin n)) (endsW : Fin m' → Sym2 (Fin N))
  (ι : Fin N → Fin n) (κ : Fin m' → Fin m)

end Transport

/-! ### The core step -/

end LowDiameterNashWilliams.Main.Dev.L41
end

section
/-! Lemma 4.3, part P: counting on finite product spaces and uniform subsets.

* `card_pi_filter_le`: coordinatewise predicates on `piFinset A` multiply.
* `card_cond_le`: fixing one coordinate and constraining others.
* `card_contain_le`: `#{a ∈ (s-subsets of L) : Q ⊆ a} ≤ (s/|L|)^|Q| C(|L|, s)`.
* `card_avoid_le`: `#{c ∈ (b-subsets of W) : c ∩ X = ∅} ≤ exp(-b|X|/|W|) C(|W|, b)`.
* `choose_le_exp`: `C(N, h) ≤ (N e / h)^h`. -/

set_option autoImplicit false
open Classical
open scoped BigOperators

namespace LowDiameterNashWilliams.Main.Dev.L43

theorem pi_filter_eq {ι β : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Finset β)
    (P : ι → β → Prop) :
    (Fintype.piFinset A).filter (fun ω => ∀ a, P a (ω a)) =
      Fintype.piFinset (fun a => (A a).filter (P a)) := by
  ext ω
  simp only [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩ a; exact ⟨h1 a, h2 a⟩
  · intro h; exact ⟨fun a => (h a).1, fun a => (h a).2⟩

theorem card_pi_filter_le {ι β : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Finset β)
    (P : ι → β → Prop) (c : ι → ℝ) (hc : ∀ a, 0 ≤ c a)
    (h : ∀ a, (((A a).filter (P a)).card : ℝ) ≤ c a * (A a).card) :
    ((((Fintype.piFinset A).filter (fun ω => ∀ a, P a (ω a))).card : ℕ) : ℝ) ≤
      (∏ a, c a) * (Fintype.piFinset A).card := by
  rw [pi_filter_eq, Fintype.card_piFinset, Fintype.card_piFinset]
  push_cast
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun a _ => by positivity) (fun a _ => h a)

/-- fix the coordinate `v` to `a` and constrain the coordinates in `Y ∌ v` -/
theorem card_cond_le' {ι β : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Finset β) {v : ι}
    {a : β} (Y : Finset ι) (hvY : v ∉ Y) (p : ι → β → Prop)
    (c : ι → ℝ) (hc : ∀ y, 0 ≤ c y)
    (h : ∀ y ∈ Y, (((A y).filter (p y)).card : ℝ) ≤ c y * (A y).card) :
    ((((Fintype.piFinset A).filter (fun ω => ω v = a ∧ ∀ y ∈ Y, p y (ω y))).card : ℕ) : ℝ) *
      (A v).card ≤ (∏ y ∈ Y, c y) * (Fintype.piFinset A).card := by
  by_cases hAv : (A v).card = 0
  · rw [hAv]; simp only [Nat.cast_zero, mul_zero]
    exact mul_nonneg (Finset.prod_nonneg fun y _ => hc y) (Nat.cast_nonneg _)
  have hAv' : (0 : ℝ) < (A v).card := by exact_mod_cast Nat.pos_of_ne_zero hAv
  let P : ι → β → Prop := fun w b => (w = v → b = a) ∧ (w ∈ Y → p w b)
  let c' : ι → ℝ := fun w => if w = v then 1 / (A v).card else if w ∈ Y then c w else 1
  have hfil : (Fintype.piFinset A).filter (fun ω => ω v = a ∧ ∀ y ∈ Y, p y (ω y)) =
      (Fintype.piFinset A).filter (fun ω => ∀ w, P w (ω w)) := by
    apply Finset.filter_congr
    intro ω _
    constructor
    · rintro ⟨h1, h2⟩ w
      refine ⟨fun hw => hw ▸ h1, fun hw => h2 w hw⟩
    · intro h
      exact ⟨(h v).1 rfl, fun y hy => (h y).2 hy⟩
  have hc' : ∀ w, 0 ≤ c' w := by
    intro w; simp only [c']; split_ifs
    · positivity
    · exact hc w
    · norm_num
  have hbound : ∀ w, (((A w).filter (P w)).card : ℝ) ≤ c' w * (A w).card := by
    intro w
    by_cases hw : w = v
    · subst hw
      simp only [c', if_pos rfl]
      rw [div_mul_cancel₀ _ hAv'.ne']
      have : (A w).filter (P w) ⊆ {a} := by
        intro b hb
        exact Finset.mem_singleton.2 ((Finset.mem_filter.1 hb).2.1 rfl)
      have := Finset.card_le_card this
      simp at this
      exact_mod_cast this
    · by_cases hwY : w ∈ Y
      · simp only [c', if_neg hw, if_pos hwY]
        refine le_trans (le_of_eq ?_) (h w hwY)
        congr 2
        apply Finset.filter_congr
        intro b _
        simp [P, hw, hwY]
      · simp only [c', if_neg hw, if_neg hwY, one_mul]
        exact_mod_cast Finset.card_filter_le _ _
  have := card_pi_filter_le A P c' hc' (fun w => by convert hbound w)
  rw [hfil]
  have hprod : (∏ w, c' w) = 1 / (A v).card * ∏ y ∈ Y, c y := by
    rw [← Finset.mul_prod_erase Finset.univ c' (Finset.mem_univ v)]
    simp only [c', if_pos rfl]
    congr 1
    have : ∀ w ∈ Finset.univ.erase v, (if w = v then 1 / ((A v).card : ℝ) else
        if w ∈ Y then c w else 1) = if w ∈ Y then c w else 1 := by
      intro w hw
      rw [if_neg (Finset.ne_of_mem_erase hw)]
    rw [Finset.prod_congr rfl this, Finset.prod_ite_mem]
    congr 1
    ext y
    simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · exact fun h => h.2
    · intro hy; exact ⟨fun h => hvY (h ▸ hy), hy⟩
  rw [hprod] at this
  have hle : ((((Fintype.piFinset A).filter (fun ω => ∀ w, P w (ω w))).card : ℕ) : ℝ) ≤
      (1 / (A v).card * ∏ y ∈ Y, c y) * (Fintype.piFinset A).card := by convert this using 4
  calc _ ≤ 1 / ((A v).card : ℝ) * (∏ y ∈ Y, c y) * (Fintype.piFinset A).card * (A v).card := by
        gcongr
    _ = _ := by field_simp

theorem card_cond_le {ι β : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Finset β) {v : ι}
    {a : β} (Y : Finset ι) (hvY : v ∉ Y) (p : ι → β → Prop) [∀ y, DecidablePred (p y)]
    [DecidablePred (fun ω : ι → β => ω v = a ∧ ∀ y ∈ Y, p y (ω y))]
    (c : ι → ℝ) (hc : ∀ y, 0 ≤ c y)
    (h : ∀ y ∈ Y, (((A y).filter (p y)).card : ℝ) ≤ c y * (A y).card) :
    ((((Fintype.piFinset A).filter (fun ω => ω v = a ∧ ∀ y ∈ Y, p y (ω y))).card : ℕ) : ℝ) *
      (A v).card ≤ (∏ y ∈ Y, c y) * (Fintype.piFinset A).card := by
  convert card_cond_le' A Y hvY p c hc (fun y hy => by convert h y hy using 4) using 5

/-- one of finitely many values is at most the average -/
theorem exists_le_avg {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) (B : ℝ)
    (h : ∑ x ∈ s, f x ≤ B * s.card) : ∃ x ∈ s, f x ≤ B := by
  by_contra hc
  push Not at hc
  have : ∑ x ∈ s, B < ∑ x ∈ s, f x := Finset.sum_lt_sum_of_nonempty hs hc
  simp at this
  linarith

/-! ### Binomial estimates -/

theorem choose_ratio (N t : ℕ) (ht : t ≤ N) (hN : 0 < N) :
    ∀ b : ℕ, ((N - t).choose b : ℝ) ≤ (1 - (t : ℝ) / N) ^ b * N.choose b := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 ≤ 1 - (t : ℝ) / N := by
    rw [sub_nonneg, div_le_one hNr]; exact_mod_cast ht
  intro b
  induction b with
  | zero => simp
  | succ b ih =>
    have e1 := Nat.choose_succ_right_eq (N - t) b
    have e2 := Nat.choose_succ_right_eq N b
    have hb : (0 : ℝ) < b + 1 := by positivity
    have key : (((N - t - b : ℕ)) : ℝ) ≤ (1 - (t : ℝ) / N) * ((N - b : ℕ) : ℝ) := by
      by_cases h1 : b ≤ N - t
      · have h2 : b ≤ N := by omega
        rw [Nat.cast_sub h1, Nat.cast_sub ht, Nat.cast_sub h2]
        rw [sub_mul, one_mul, div_mul_eq_mul_div, mul_sub]
        have : (t : ℝ) * N / N = t := by field_simp
        rw [mul_comm (t : ℝ) (N : ℝ)] at this ⊢
        rw [sub_div, this]
        have : 0 ≤ (t : ℝ) * b / N := by positivity
        linarith
      · rw [show N - t - b = 0 by omega]
        simp only [Nat.cast_zero]
        positivity
    have e1' : ((N - t).choose (b + 1) : ℝ) * (b + 1) = ((N - t).choose b) * ((N - t - b : ℕ) : ℝ) := by
      exact_mod_cast e1
    have e2' : (N.choose (b + 1) : ℝ) * (b + 1) = (N.choose b) * ((N - b : ℕ) : ℝ) := by
      exact_mod_cast e2
    have : ((N - t).choose (b + 1) : ℝ) * (b + 1) ≤
        (1 - (t : ℝ) / N) ^ (b + 1) * N.choose (b + 1) * (b + 1) := by
      rw [e1', mul_assoc, e2', pow_succ]
      calc ((N - t).choose b : ℝ) * ((N - t - b : ℕ) : ℝ)
          ≤ ((1 - (t : ℝ) / N) ^ b * N.choose b) * ((1 - (t : ℝ) / N) * ((N - b : ℕ) : ℝ)) :=
            mul_le_mul ih key (Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hb

/-- `C(s, h) ≤ (s/ℓ)^h C(ℓ, h)` for `s ≤ ℓ` -/
theorem choose_ratio2 (s l : ℕ) (hsl : s ≤ l) (hl : 0 < l) :
    ∀ h : ℕ, (s.choose h : ℝ) ≤ ((s : ℝ) / l) ^ h * l.choose h := by
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  intro h
  induction h with
  | zero => simp
  | succ h ih =>
    have e1 := Nat.choose_succ_right_eq s h
    have e2 := Nat.choose_succ_right_eq l h
    have hb : (0 : ℝ) < h + 1 := by positivity
    have key : ((s - h : ℕ) : ℝ) ≤ ((s : ℝ) / l) * ((l - h : ℕ) : ℝ) := by
      by_cases h1 : h ≤ s
      · rw [Nat.cast_sub h1, Nat.cast_sub (h1.trans hsl)]
        rw [mul_sub, div_mul_cancel₀ _ hlr.ne']
        have : (s : ℝ) / l * h ≤ h := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hlr]
          have : (s : ℝ) ≤ l := by exact_mod_cast hsl
          nlinarith
        linarith
      · rw [show s - h = 0 by omega]
        simp only [Nat.cast_zero]
        positivity
    have e1' : (s.choose (h + 1) : ℝ) * (h + 1) = (s.choose h) * ((s - h : ℕ) : ℝ) := by
      exact_mod_cast e1
    have e2' : (l.choose (h + 1) : ℝ) * (h + 1) = (l.choose h) * ((l - h : ℕ) : ℝ) := by
      exact_mod_cast e2
    have : (s.choose (h + 1) : ℝ) * (h + 1) ≤
        ((s : ℝ) / l) ^ (h + 1) * l.choose (h + 1) * (h + 1) := by
      rw [e1', mul_assoc, e2', pow_succ]
      calc (s.choose h : ℝ) * ((s - h : ℕ) : ℝ)
          ≤ (((s : ℝ) / l) ^ h * l.choose h) * (((s : ℝ) / l) * ((l - h : ℕ) : ℝ)) :=
            mul_le_mul ih key (Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hb

theorem choose_le_exp (N h : ℕ) (hh : 0 < h) :
    (N.choose h : ℝ) ≤ ((N : ℝ) * Real.exp 1 / h) ^ h := by
  have h1 : (N.choose h : ℝ) ≤ (N : ℝ) ^ h / h.factorial := Nat.choose_le_pow_div h N
  have h2 : (h : ℝ) ^ h / h.factorial ≤ Real.exp h := Real.pow_div_factorial_le_exp (x := (h : ℝ)) (by positivity) h
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hf : (0 : ℝ) < h.factorial := by exact_mod_cast Nat.factorial_pos h
  have h3 : (1 : ℝ) / h.factorial ≤ Real.exp h / (h : ℝ) ^ h := by
    rw [div_le_div_iff₀ hf (by positivity), one_mul]
    rw [div_le_iff₀ hf] at h2
    linarith
  calc (N.choose h : ℝ) ≤ (N : ℝ) ^ h / h.factorial := h1
    _ = (N : ℝ) ^ h * (1 / h.factorial) := by ring
    _ ≤ (N : ℝ) ^ h * (Real.exp h / (h : ℝ) ^ h) := by gcongr
    _ = ((N : ℝ) * Real.exp 1 / h) ^ h := by
      rw [div_pow, mul_pow, ← Real.exp_nat_mul, mul_one]
      ring

/-! ### Uniform subsets -/

theorem filter_disj_eq {α : Type*} [DecidableEq α] (W X : Finset α) (b : ℕ) :
    (W.powersetCard b).filter (fun c => Disjoint c X) = (W \ X).powersetCard b := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_sdiff]
  tauto

theorem card_avoid_le {α : Type*} [DecidableEq α] (W X : Finset α) (hX : X ⊆ W) (b : ℕ) :
    ((((W.powersetCard b).filter (fun c => Disjoint c X)).card : ℕ) : ℝ) ≤
      Real.exp (-(b : ℝ) * X.card / W.card) * (W.powersetCard b).card := by
  rw [filter_disj_eq, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset hX]
  by_cases hW : W.card = 0
  · have : X.card = 0 := by have := Finset.card_le_card hX; omega
    rw [hW, this]; simp
  have hWpos : 0 < W.card := Nat.pos_of_ne_zero hW
  refine (choose_ratio W.card X.card (Finset.card_le_card hX) hWpos b).trans ?_
  gcongr
  have hq : 0 ≤ 1 - (X.card : ℝ) / W.card := by
    rw [sub_nonneg, div_le_one (by exact_mod_cast hWpos)]; exact_mod_cast Finset.card_le_card hX
  calc (1 - (X.card : ℝ) / W.card) ^ b ≤ (Real.exp (-((X.card : ℝ) / W.card))) ^ b := by
        gcongr
        have := Real.add_one_le_exp (-((X.card : ℝ) / W.card))
        linarith
    _ = Real.exp (-(b : ℝ) * X.card / W.card) := by
        rw [← Real.exp_nat_mul]; congr 1; ring

theorem card_contain_le {α : Type*} [DecidableEq α] (L Q : Finset α) (s : ℕ) :
    ((((L.powersetCard s).filter (fun a => Q ⊆ a)).card : ℕ) : ℝ) ≤
      ((s : ℝ) / L.card) ^ Q.card * (L.powersetCard s).card := by
  rw [Finset.card_powersetCard]
  by_cases hzero : (L.powersetCard s).filter (fun a => Q ⊆ a) = ∅
  · rw [hzero]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  obtain ⟨a0, ha0⟩ := Finset.nonempty_iff_ne_empty.2 hzero
  rw [Finset.mem_filter, Finset.mem_powersetCard] at ha0
  have hQL : Q ⊆ L := ha0.2.trans ha0.1.1
  have hQs : Q.card ≤ s := ha0.1.2 ▸ Finset.card_le_card ha0.2
  have hsL : s ≤ L.card := ha0.1.2 ▸ Finset.card_le_card ha0.1.1
  have hcount : ((L.powersetCard s).filter (fun a => Q ⊆ a)).card =
      (L.card - Q.card).choose (s - Q.card) := by
    rw [← Finset.card_sdiff_of_subset hQL, ← Finset.card_powersetCard]
    refine Finset.card_nbij' (fun a => a \ Q) (fun b => b ∪ Q) ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at ha
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      refine ⟨Finset.sdiff_subset_sdiff ha.1.1 le_rfl, ?_⟩
      rw [Finset.card_sdiff_of_subset ha.2, ha.1.2]
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hb
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
      have hdisj : Disjoint b Q := by
        rw [Finset.subset_sdiff] at hb; exact hb.1.2
      refine ⟨⟨Finset.union_subset (hb.1.trans Finset.sdiff_subset) hQL, ?_⟩,
        Finset.subset_union_right⟩
      rw [Finset.card_union_of_disjoint hdisj, hb.2]; omega
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at ha
      exact Finset.sdiff_union_of_subset ha.2
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hb
      have hdisj : Disjoint b Q := by
        rw [Finset.subset_sdiff] at hb; exact hb.1.2
      exact Finset.union_sdiff_cancel_right hdisj
  rw [hcount]
  by_cases hL0 : L.card = 0
  · have hs0 : s = 0 := by omega
    have hq0 : Q.card = 0 := by omega
    rw [hL0, hs0, hq0]; simp
  have hLpos : 0 < L.card := Nat.pos_of_ne_zero hL0
  have hcm := Nat.choose_mul (n := L.card) hQs
  have hpos : (0 : ℝ) < (L.card.choose Q.card : ℕ) := by
    exact_mod_cast Nat.choose_pos (hQs.trans hsL)
  have hcm' : ((L.card - Q.card).choose (s - Q.card) : ℝ) * (L.card.choose Q.card) =
      (L.card.choose s) * (s.choose Q.card) := by
    rw [mul_comm]; exact_mod_cast hcm.symm
  have h2 := choose_ratio2 s L.card hsL hLpos Q.card
  refine le_of_mul_le_mul_right ?_ hpos
  rw [hcm']
  calc (L.card.choose s : ℝ) * (s.choose Q.card) ≤
      (L.card.choose s) * (((s : ℝ) / L.card) ^ Q.card * L.card.choose Q.card) := by gcongr
    _ = _ := by ring

end LowDiameterNashWilliams.Main.Dev.L43
end

section
/-! Lemma 4.3, part T: restoring one supplying tree.

`T` is a spanning tree, `D` a set of leaves of `T` (deleted vertices), `att v` (for `v ∈ D`)
an edge joining `v` to a vertex outside `D`. `Tm` = edges of `T` with no end in `D`,
`Vt = Tm ∪ att '' D`. Then `Vt` is a spanning tree, `diam Vt ≤ diam T + 2` and every internal
vertex of `Vt` is internal in `T` or the far end of some `att v`. -/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L43
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33
  LowDiameterNashWilliams.Main.Dev.L41

variable {n m : ℕ}

/-- the edges of `T` with no end in `D` -/
noncomputable def Tm (ends : Fin m → Sym2 (Fin n)) (T : Edges m) (D : Finset (Fin n)) :
    Edges m :=
  T.filter fun e => ∀ x ∈ ends e, x ∉ D

/-- the restored tree -/
noncomputable def Vt (ends : Fin m → Sym2 (Fin n)) (T : Edges m) (D : Finset (Fin n))
    (att : Fin n → Fin m) : Edges m :=
  Tm ends T D ∪ D.image att

theorem mem_ends_iff {ends : Fin m → Sym2 (Fin n)} {e : Fin m} {u w : Fin n}
    (h : ends e = s(u, w)) (x : Fin n) : x ∈ ends e ↔ x = u ∨ x = w := by
  rw [h, Sym2.mem_iff]

/-- a leaf has a unique edge -/
theorem leaf_edge (ends : Fin m → Sym2 (Fin n)) {T : Edges m} {v : Fin n}
    (h : degIn ends T v = 1) : ∃ e ∈ T, v ∈ ends e ∧ ∀ e' ∈ T, v ∈ ends e' → e' = e := by
  unfold degIn at h
  obtain ⟨e, he⟩ := Finset.card_eq_one.1 h
  have hm : e ∈ T.filter (fun e => v ∈ ends e) := by rw [he]; exact Finset.mem_singleton_self e
  rw [Finset.mem_filter] at hm
  refine ⟨e, hm.1, hm.2, fun e' he' hv => ?_⟩
  have : e' ∈ T.filter (fun e => v ∈ ends e) := Finset.mem_filter.2 ⟨he', hv⟩
  rw [he] at this
  exact Finset.mem_singleton.1 this

theorem leaf_adj (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) {T : Edges m} {v y z : Fin n}
    (h : degIn ends T v = 1) (hy : (edgeGraph ends T).Adj v y) (hz : (edgeGraph ends T).Adj v z) :
    y = z := by
  obtain ⟨e, heT, hve, huniq⟩ := leaf_edge ends h
  rw [adjS ends hs] at hy hz
  obtain ⟨e1, he1, h1⟩ := hy
  obtain ⟨e2, he2, h2⟩ := hz
  have := huniq e1 he1 (by rw [h1]; exact Sym2.mem_mk_left _ _)
  have := huniq e2 he2 (by rw [h2]; exact Sym2.mem_mk_left _ _)
  subst e1; subst e2
  rw [h1] at h2
  exact (Sym2.congr_right.1 h2)

theorem walk_stays {G : SimpleGraph (Fin n)} (P : Fin n → Prop)
    (hstep : ∀ a y, P a → G.Adj a y → P y) {a b : Fin n} (p : G.Walk a b) (ha : P a) : P b := by
  induction p with
  | nil => exact ha
  | cons h p ih => exact ih (hstep _ _ ha h)

/-- in a spanning tree on at least three vertices no two leaves are adjacent -/
theorem no_adj_leaves (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (hn : 3 ≤ n)
    {T : Edges m} (hT : IsSpanningTree ends T) {e : Fin m} (he : e ∈ T) {u w : Fin n}
    (huw : ends e = s(u, w)) (hu : degIn ends T u = 1) (hw : degIn ends T w = 1) : False := by
  obtain ⟨z, hz⟩ : ∃ z : Fin n, z ≠ u ∧ z ≠ w := by
    have hc : (Finset.univ \ {u, w} : Finset (Fin n)).card ≥ 1 := by
      have h1 := Finset.card_le_card_sdiff_add_card (s := (Finset.univ : Finset (Fin n)))
        (t := {u, w})
      have h2 : ({u, w} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.1 hc
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or] at hz
    exact ⟨z, hz⟩
  obtain ⟨p⟩ := connected_of_tree ends hT u z
  have := walk_stays (G := edgeGraph ends T) (fun x => x = u ∨ x = w) ?_ p (Or.inl rfl)
  · rcases this with h | h
    · exact hz.1 h
    · exact hz.2 h
  intro a y ha hay
  rw [adjS ends hs] at hay
  obtain ⟨e', he', he'e⟩ := hay
  have hdeg : degIn ends T a = 1 := by rcases ha with rfl | rfl <;> assumption
  obtain ⟨f, hfT, haf, huniq⟩ := leaf_edge ends hdeg
  have h1 := huniq e' he' (by rw [he'e]; exact Sym2.mem_mk_left _ _)
  have h2 := huniq e he (by rcases ha with rfl | rfl <;> rw [huw] <;> simp)
  subst h1
  rw [← h2, huw] at he'e
  have : y ∈ s(u, w) := by rw [he'e]; exact Sym2.mem_mk_right _ _
  rwa [Sym2.mem_iff] at this

section Restore

variable (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (T : Edges m) (D : Finset (Fin n))
  (att : Fin n → Fin m)

/-- hypotheses of the restoration -/
structure RHyp : Prop where
  three : 3 ≤ n
  tree : IsSpanningTree ends T
  leaf : ∀ v ∈ D, degIn ends T v = 1
  att_spec : ∀ v ∈ D, ∃ x, x ∉ D ∧ ends (att v) = s(v, x)

variable {ends T D att}

theorem tm_adj (hs : Simple ends) {a y : Fin n} (h : (edgeGraph ends T).Adj a y) (ha : a ∉ D)
    (hy : y ∉ D) : (edgeGraph ends (Tm ends T D)).Adj a y := by
  rw [adjS ends hs] at h ⊢
  obtain ⟨e, he, hey⟩ := h
  refine ⟨e, Finset.mem_filter.2 ⟨he, fun x hx => ?_⟩, hey⟩
  rcases (mem_ends_iff hey x).1 hx with rfl | rfl <;> assumption

/-- a walk of `T` between vertices outside `D` shortens to a walk of `Tm` -/
theorem shorten (hs : Simple ends) (hleaf : ∀ v ∈ D, degIn ends T v = 1) :
    ∀ (N : ℕ) {a b : Fin n} (p : (edgeGraph ends T).Walk a b), p.length ≤ N → a ∉ D → b ∉ D →
      ∃ q : (edgeGraph ends (Tm ends T D)).Walk a b, q.length ≤ p.length := by
  intro N
  induction N with
  | zero =>
    intro a b p hp ha hb
    match p with
    | .nil => exact ⟨.nil, le_refl _⟩
    | .cons _ _ => simp at hp
  | succ N ih =>
    intro a b p hp ha hb
    match p with
    | .nil => exact ⟨.nil, le_refl _⟩
    | .cons (v := y) hay p' =>
      by_cases hy : y ∈ D
      · match p' with
        | .nil => exact absurd hy hb
        | .cons (v := z) hyz p'' =>
          have hza : z = a := leaf_adj ends hs (hleaf y hy) hyz hay.symm
          subst hza
          obtain ⟨q, hq⟩ := ih p'' (by simp at hp; omega) ha hb
          exact ⟨q, by simp; omega⟩
      · obtain ⟨q, hq⟩ := ih p' (by simp at hp; omega) hy hb
        exact ⟨.cons (tm_adj hs hay ha hy) q, by simp; omega⟩

theorem dist_mono {F F' : Edges m} (h : F ⊆ F') (a b : Fin n) :
    distance ends F' a b ≤ distance ends F a b := by
  unfold distance
  refine le_iInf fun p => ?_
  refine iInf_le_of_le (p.map (SimpleGraph.Hom.ofLE
    (LowDiameterNashWilliams.Dev.Forest.edgeGraph_mono ends h))) ?_
  rw [SimpleGraph.Walk.length_map]

theorem dist_tm (hs : Simple ends) (hleaf : ∀ v ∈ D, degIn ends T v = 1) {a b : Fin n}
    (ha : a ∉ D) (hb : b ∉ D) : distance ends (Tm ends T D) a b ≤ distance ends T a b := by
  unfold distance
  refine le_iInf fun p => ?_
  obtain ⟨q, hq⟩ := shorten hs hleaf p.length p le_rfl ha hb
  exact iInf_le_of_le q (by exact_mod_cast hq)

theorem rch_tm (hs : Simple ends) (hT : IsSpanningTree ends T)
    (hleaf : ∀ v ∈ D, degIn ends T v = 1) {a b : Fin n} (ha : a ∉ D) (hb : b ∉ D) :
    Rch ends (Tm ends T D) a b := by
  obtain ⟨p⟩ := connected_of_tree ends hT a b
  obtain ⟨q, -⟩ := shorten hs hleaf p.length p le_rfl ha hb
  exact ⟨q⟩

theorem tm_sub_vt : Tm ends T D ⊆ Vt ends T D att := Finset.subset_union_left

theorem att_mem_vt {v : Fin n} (hv : v ∈ D) : att v ∈ Vt ends T D att :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem att hv)

/-- the anchor of a vertex: itself outside `D`, its attachment end inside `D` -/
theorem anchor (h : RHyp ends T D att) (hs : Simple ends) (v : Fin n) :
    ∃ w, w ∉ D ∧ (v = w ∨ (v ∈ D ∧ (edgeGraph ends (Vt ends T D att)).Adj v w)) := by
  by_cases hv : v ∈ D
  · obtain ⟨x, hx, hex⟩ := h.att_spec v hv
    refine ⟨x, hx, Or.inr ⟨hv, ?_⟩⟩
    rw [adjS ends hs]
    exact ⟨att v, att_mem_vt hv, hex⟩
  · exact ⟨v, hv, Or.inl rfl⟩

theorem rch_vt (h : RHyp ends T D att) (hs : Simple ends) (a b : Fin n) :
    Rch ends (Vt ends T D att) a b := by
  obtain ⟨a', ha', hav⟩ := anchor h hs a
  obtain ⟨b', hb', hbv⟩ := anchor h hs b
  have hmid : Rch ends (Vt ends T D att) a' b' :=
    rch_mono ends tm_sub_vt (rch_tm hs h.tree h.leaf ha' hb')
  have h1 : Rch ends (Vt ends T D att) a a' := by
    rcases hav with rfl | ⟨-, hadj⟩
    · exact SimpleGraph.Reachable.refl _
    · exact hadj.reachable
  have h2 : Rch ends (Vt ends T D att) b b' := by
    rcases hbv with rfl | ⟨-, hadj⟩
    · exact SimpleGraph.Reachable.refl _
    · exact hadj.reachable
  exact h1.trans (hmid.trans h2.symm)

/-- distances in the restored tree -/
theorem dist_vt (h : RHyp ends T D att) (hs : Simple ends) (a b : Fin n) :
    distance ends (Vt ends T D att) a b ≤ diameter ends T + 2 := by
  obtain ⟨a', ha', hav⟩ := anchor h hs a
  obtain ⟨b', hb', hbv⟩ := anchor h hs b
  have hmid : distance ends (Vt ends T D att) a' b' ≤ diameter ends T :=
    (dist_mono tm_sub_vt a' b').trans ((dist_tm hs h.leaf ha' hb').trans
      (le_iSup_of_le a' (le_iSup_of_le b' le_rfl)))
  have h1 : distance ends (Vt ends T D att) a b' ≤ distance ends (Vt ends T D att) a' b' + 1 := by
    rcases hav with rfl | ⟨-, hadj⟩
    · exact le_self_add
    · exact dist_adj ends _ hadj b'
  have h2 : distance ends (Vt ends T D att) a b ≤ distance ends (Vt ends T D att) a b' + 1 := by
    rcases hbv with rfl | ⟨-, hadj⟩
    · exact le_self_add
    · rw [dist_symm ends _ a b, dist_symm ends _ a b']
      exact dist_adj ends _ hadj a
  calc distance ends (Vt ends T D att) a b ≤ distance ends (Vt ends T D att) a b' + 1 := h2
    _ ≤ distance ends (Vt ends T D att) a' b' + 1 + 1 := by gcongr
    _ ≤ diameter ends T + 1 + 1 := by gcongr
    _ = diameter ends T + 2 := by rw [add_assoc]; norm_num

theorem diam_vt (h : RHyp ends T D att) (hs : Simple ends) :
    diameter ends (Vt ends T D att) ≤ diameter ends T + 2 :=
  iSup_le fun a => iSup_le fun b => dist_vt h hs a b

/-- the attachment of `v` is incident only to `v` among the deleted vertices -/
theorem att_ends_D (h : RHyp ends T D att) {v x : Fin n} (hv : v ∈ D) (hx : x ∈ D)
    (hxe : x ∈ ends (att v)) : x = v := by
  obtain ⟨y, hy, hey⟩ := h.att_spec v hv
  rcases (mem_ends_iff hey x).1 hxe with rfl | rfl
  · rfl
  · exact absurd hx hy

theorem att_inj (h : RHyp ends T D att) : Set.InjOn att (D : Set (Fin n)) := by
  intro v hv w hw hvw
  have : w ∈ ends (att v) := by
    rw [hvw]; obtain ⟨y, -, hey⟩ := h.att_spec w hw; rw [hey]; exact Sym2.mem_mk_left _ _
  exact (att_ends_D h hv hw this).symm

theorem tm_disj_att (h : RHyp ends T D att) : Disjoint (Tm ends T D) (D.image att) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he'
  obtain ⟨y, -, hey⟩ := h.att_spec v hv
  exact (Finset.mem_filter.1 he).2 v (by rw [hey]; exact Sym2.mem_mk_left _ _) hv

theorem card_tm (h : RHyp ends T D att) (hs : Simple ends) :
    (Tm ends T D).card + D.card = T.card := by
  have hbu : T.filter (fun e => ¬ ∀ x ∈ ends e, x ∉ D) =
      D.biUnion (fun v => T.filter (fun e => v ∈ ends e)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_biUnion, not_forall, not_not]
    constructor
    · rintro ⟨he, x, hx, hxD⟩; exact ⟨x, hxD, he, hx⟩
    · rintro ⟨x, hxD, he, hx⟩; exact ⟨he, x, hx, hxD⟩
  have hdisj : (D : Set (Fin n)).PairwiseDisjoint (fun v => T.filter (fun e => v ∈ ends e)) := by
    intro v hv w hw hvw
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_filter] at he he'
    obtain ⟨a, b, hab⟩ := exists_ends ends e
    have hv' := (mem_ends_iff hab v).1 he.2
    have hw' := (mem_ends_iff hab w).1 he'.2
    have hvw' : ends e = s(v, w) := by
      rcases hv' with rfl | rfl <;> rcases hw' with rfl | rfl
      · exact absurd rfl hvw
      · exact hab
      · rw [hab, Sym2.eq_swap]
      · exact absurd rfl hvw
    exact no_adj_leaves ends hs h.three h.tree he.1 hvw' (h.leaf v hv) (h.leaf w hw)
  have h1 := Finset.card_filter_add_card_filter_not (s := T)
    (p := fun e => ∀ x ∈ ends e, x ∉ D)
  rw [hbu, Finset.card_biUnion hdisj] at h1
  have h2 : ∑ v ∈ D, (T.filter (fun e => v ∈ ends e)).card = D.card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun v hv => ?_
    exact h.leaf v hv
  rw [h2] at h1
  exact h1

theorem card_vt (h : RHyp ends T D att) (hs : Simple ends) :
    (Vt ends T D att).card + 1 = n := by
  unfold Vt
  rw [Finset.card_union_of_disjoint (tm_disj_att h), Finset.card_image_of_injOn (att_inj h),
    card_tm h hs]
  exact tree_card ends h.tree

theorem tree_vt (h : RHyp ends T D att) (hs : Simple ends) :
    IsSpanningTree ends (Vt ends T D att) :=
  tree_of_conn ends hs (by have := h.three; omega) _ (rch_vt h hs) (card_vt h hs)

theorem internal_vt (h : RHyp ends T D att) {x : Fin n}
    (hx : x ∈ internal ends (Vt ends T D att)) :
    x ∈ internal ends T ∨ ∃ v ∈ D, x ≠ v ∧ x ∈ ends (att v) := by
  unfold internal at hx ⊢
  rw [Finset.mem_filter] at hx ⊢
  unfold degIn at hx ⊢
  by_cases hxD : x ∈ D
  · exfalso
    have hsub : (Vt ends T D att).filter (fun e => x ∈ ends e) ⊆ {att x} := by
      intro e he
      rw [Finset.mem_filter] at he
      rcases Finset.mem_union.1 he.1 with he1 | he1
      · exact absurd hxD ((Finset.mem_filter.1 he1).2 x he.2)
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he1
        rw [att_ends_D h hv hxD he.2]; exact Finset.mem_singleton_self _
    have := Finset.card_le_card hsub
    simp at this; omega
  by_cases hhead : ∃ v ∈ D, x ≠ v ∧ x ∈ ends (att v)
  · exact Or.inr hhead
  left
  refine ⟨Finset.mem_univ _, le_trans hx.2 (Finset.card_le_card ?_)⟩
  intro e he
  rw [Finset.mem_filter] at he ⊢
  refine ⟨?_, he.2⟩
  rcases Finset.mem_union.1 he.1 with he1 | he1
  · exact (Finset.mem_filter.1 he1).1
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he1
    exfalso
    by_cases hxv : x = v
    · exact hxD (hxv ▸ hv)
    · exact hhead ⟨v, hv, hxv, he.2⟩

end Restore

end LowDiameterNashWilliams.Main.Dev.L43
end

section
/-! Lemma 4.3, part D: the global restoration, given the attachments.

Selections `Jv v ⊆ J` (trees where `v` is a deleted leaf), protected indices `pr v ⊆ Jv v`.
`Prot v` / `Res v` are the leaf edges of `v` in the trees `pr v` / `Jv v \ pr v`.
After an exchange `(U, R')` of `P = ⋃_{i∈I} T_i ∪ ⋃_v Res v`, attachments `att v j`
(`j ∈ Jv v`), a bijection from `Jv v` onto `Prot v ∪ R' v` whose far ends stay in tree `j`,
restore the supplying trees (`restore`). -/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L43
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33
  LowDiameterNashWilliams.Main.Dev.L41

variable {n m k : ℕ}

/-- leaf edges of `v` in the trees indexed by `a` -/
noncomputable def LE (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (v : Fin n)
    (a : Finset (Fin k)) : Edges m :=
  a.biUnion fun j => (T j).filter fun e => v ∈ ends e

theorem mem_LE {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {v : Fin n} {a : Finset (Fin k)}
    {e : Fin m} : e ∈ LE ends T v a ↔ ∃ j ∈ a, e ∈ T j ∧ v ∈ ends e := by
  simp [LE]

theorem tree_unique {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} (hT : TreePartition ends T)
    {e : Fin m} {i i' : Fin k} (h : e ∈ T i) (h' : e ∈ T i') : i = i' := by
  by_contra hne
  exact Finset.disjoint_left.1 (hT.1.2 i i' hne) h h'

theorem two_leaves {ends : Fin m → Sym2 (Fin n)} (hs : Simple ends) (hn : 3 ≤ n)
    {F : Edges m} (hF : IsSpanningTree ends F) {e : Fin m} (he : e ∈ F) {v w : Fin n}
    (hv : v ∈ ends e) (hw : w ∈ ends e) (hvw : v ≠ w) (hdv : degIn ends F v = 1)
    (hdw : degIn ends F w = 1) : False := by
  obtain ⟨a, b, hab⟩ := exists_ends ends e
  have hv' := (mem_ends_iff hab v).1 hv
  have hw' := (mem_ends_iff hab w).1 hw
  have hvw' : ends e = s(v, w) := by
    rcases hv' with rfl | rfl <;> rcases hw' with rfl | rfl
    · exact absurd rfl hvw
    · exact hab
    · rw [hab, Sym2.eq_swap]
    · exact absurd rfl hvw
  exact no_adj_leaves ends hs hn hF he hvw' hdv hdw

/-- the card of `LE` -/
theorem card_LE {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} (hT : TreePartition ends T)
    {v : Fin n} {a : Finset (Fin k)} (ha : ∀ j ∈ a, degIn ends (T j) v = 1) :
    (LE ends T v a).card = a.card := by
  unfold LE
  rw [Finset.card_biUnion]
  · rw [Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl fun j hj => ha j hj
  · intro i _ j _ hij
    exact Finset.disjoint_filter_filter (hT.1.2 i j hij)

section Global

variable (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (I J : Finset (Fin k))
  (Jv pr : Fin n → Finset (Fin k))

noncomputable def Prot (v : Fin n) : Edges m := LE ends T v (pr v)

noncomputable def Res (v : Fin n) : Edges m := LE ends T v (Jv v \ pr v)

noncomputable def Pset : Edges m := I.biUnion T ∪ Finset.univ.biUnion (Res ends T Jv pr)

noncomputable def Dj (j : Fin k) : Finset (Fin n) := Finset.univ.filter fun v => j ∈ Jv v

structure GHyp : Prop where
  simple : Simple ends
  three : 3 ≤ n
  part : TreePartition ends T
  disj : Disjoint I J
  cover : I ∪ J = Finset.univ
  jsub : ∀ v, Jv v ⊆ J
  leaf : ∀ v, ∀ j ∈ Jv v, degIn ends (T j) v = 1
  prsub : ∀ v, pr v ⊆ Jv v

variable {ends T I J Jv pr}

theorem not_I_of_J (h : GHyp ends T I J Jv pr) {j : Fin k} (hj : j ∈ J) : j ∉ I :=
  fun hi => Finset.disjoint_left.1 h.disj hi hj

theorem res_owner (h : GHyp ends T I J Jv pr) : OwnerReserves ends (Res ends T Jv pr) := by
  refine ⟨fun v e he => ?_, fun v w hvw => ?_⟩
  · obtain ⟨j, -, -, hv⟩ := mem_LE.1 he; exact hv
  · rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨j, hj, hej, hv⟩ := mem_LE.1 he
    obtain ⟨j', hj', hej', hw⟩ := mem_LE.1 he'
    have := tree_unique h.part hej hej'
    subst this
    exact two_leaves h.simple h.three (h.part.1.1 j) hej hv hw hvw
      (h.leaf v j (Finset.sdiff_subset hj)) (h.leaf w j (Finset.sdiff_subset hj'))

theorem res_sub (h : GHyp ends T I J Jv pr) (v : Fin n) : Res ends T Jv pr v ⊆ J.biUnion T := by
  intro e he
  obtain ⟨j, hj, hej, -⟩ := mem_LE.1 he
  exact Finset.mem_biUnion.2 ⟨j, h.jsub v (Finset.sdiff_subset hj), hej⟩

theorem prot_not_P (h : GHyp ends T I J Jv pr) {v : Fin n} {e : Fin m}
    (he : e ∈ Prot ends T pr v) : e ∉ Pset ends T I Jv pr := by
  obtain ⟨j, hj, hej, hv⟩ := mem_LE.1 he
  have hjJ : j ∈ J := h.jsub v (h.prsub v hj)
  intro hP
  rcases Finset.mem_union.1 hP with hP | hP
  · obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.1 hP
    have := tree_unique h.part hej hei
    subst this
    exact not_I_of_J h hjJ hi
  · obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.1 hP
    obtain ⟨j', hj', hej', hw'⟩ := mem_LE.1 hw
    have := tree_unique h.part hej hej'
    subst this
    by_cases hvw : v = w
    · subst hvw; exact (Finset.mem_sdiff.1 hj').2 hj
    · exact two_leaves h.simple h.three (h.part.1.1 j) hej hv hw' hvw
        (h.leaf v j (h.prsub v hj)) (h.leaf w j (Finset.sdiff_subset hj'))

theorem tm_not_P (h : GHyp ends T I J Jv pr) {j : Fin k} (hj : j ∉ I) {e : Fin m}
    (he : e ∈ Tm ends (T j) (Dj Jv j)) : e ∉ Pset ends T I Jv pr := by
  rw [Tm, Finset.mem_filter] at he
  intro hP
  rcases Finset.mem_union.1 hP with hP | hP
  · obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.1 hP
    have := tree_unique h.part he.1 hei
    subst this
    exact hj hi
  · obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.1 hP
    obtain ⟨j', hj', hej', hw'⟩ := mem_LE.1 hw
    have := tree_unique h.part he.1 hej'
    subst this
    exact he.2 w hw' (by simp [Dj]; exact Finset.sdiff_subset hj')

section Exchange

variable {U : Trees k m} {R' : Fin n → Edges m}

/-- the edges available at `v` after the exchange -/
noncomputable def Ev (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (pr : Fin n → Finset (Fin k))
    (R' : Fin n → Edges m) (v : Fin n) : Edges m :=
  Prot ends T pr v ∪ R' v

theorem R'_sub_P (hX : ExchangePartition ends I U R' (Pset ends T I Jv pr)) (v : Fin n) :
    R' v ⊆ Pset ends T I Jv pr := by
  intro e he
  rw [← hX.2.2.2.2]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _, he⟩)

theorem Ev_disj (h : GHyp ends T I J Jv pr)
    (hX : ExchangePartition ends I U R' (Pset ends T I Jv pr)) {v w : Fin n} (hvw : v ≠ w) :
    Disjoint (Ev ends T pr R' v) (Ev ends T pr R' w) := by
  rw [Finset.disjoint_left]
  intro e he he'
  rcases Finset.mem_union.1 he with he | he <;> rcases Finset.mem_union.1 he' with he' | he'
  · obtain ⟨j, hj, hej, hv⟩ := mem_LE.1 he
    obtain ⟨j', hj', hej', hw⟩ := mem_LE.1 he'
    have := tree_unique h.part hej hej'
    subst this
    exact two_leaves h.simple h.three (h.part.1.1 j) hej hv hw hvw
      (h.leaf v j (h.prsub v hj)) (h.leaf w j (h.prsub w hj'))
  · exact prot_not_P h he (R'_sub_P hX w he')
  · exact prot_not_P h he' (R'_sub_P hX v he)
  · exact Finset.disjoint_left.1 (hX.2.2.1.2 v w hvw) he he'

theorem tm_disj_Ev (h : GHyp ends T I J Jv pr)
    (hX : ExchangePartition ends I U R' (Pset ends T I Jv pr)) {j : Fin k} (hj : j ∉ I)
    (v : Fin n) : Disjoint (Tm ends (T j) (Dj Jv j)) (Ev ends T pr R' v) := by
  rw [Finset.disjoint_left]
  intro e he he'
  rcases Finset.mem_union.1 he' with he' | he'
  · obtain ⟨j', hj', hej', hv⟩ := mem_LE.1 he'
    rw [Tm, Finset.mem_filter] at he
    have := tree_unique h.part he.1 hej'
    subst this
    exact he.2 v hv (by simp [Dj]; exact h.prsub v hj')
  · exact tm_not_P h hj he (R'_sub_P hX v he')

/-- hypotheses on the attachments -/
structure AttHyp (att : Fin n → Fin k → Fin m) : Prop where
  mem : ∀ v, ∀ j ∈ Jv v, att v j ∈ Ev ends T pr R' v
  inj : ∀ v, Set.InjOn (att v) (Jv v : Set (Fin k))
  surj : ∀ v, Ev ends T pr R' v ⊆ (Jv v).image (att v)
  head : ∀ v, ∀ j ∈ Jv v, ∃ x, j ∉ Jv x ∧ ends (att v j) = s(v, x)

/-- the restored family -/
noncomputable def Vfam (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (I : Finset (Fin k))
    (Jv : Fin n → Finset (Fin k)) (U : Trees k m) (att : Fin n → Fin k → Fin m) :
    Trees k m := fun i =>
  if i ∈ I then U i else Vt ends (T i) (Dj Jv i) (fun v => att v i)

theorem rhyp (h : GHyp ends T I J Jv pr) {att : Fin n → Fin k → Fin m}
    (ha : AttHyp (ends := ends) (T := T) (Jv := Jv) (pr := pr) (R' := R') att) (j : Fin k) :
    RHyp ends (T j) (Dj Jv j) (fun v => att v j) := by
  refine ⟨h.three, h.part.1.1 j, fun v hv => ?_, fun v hv => ?_⟩
  · simp only [Dj, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact h.leaf v j hv
  · simp only [Dj, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨x, hx, hex⟩ := ha.head v j hv
    exact ⟨x, by simp [Dj, hx], hex⟩

theorem restore (h : GHyp ends T I J Jv pr)
    (hX : ExchangePartition ends I U R' (Pset ends T I Jv pr)) {att : Fin n → Fin k → Fin m}
    (ha : AttHyp (ends := ends) (T := T) (Jv := Jv) (pr := pr) (R' := R') att) :
    TreePartition ends (Vfam ends T I Jv U att) ∧ (∀ i ∈ I, Vfam ends T I Jv U att i = U i) ∧
      ∀ j ∈ J, diameter ends (Vfam ends T I Jv U att j) ≤ diameter ends (T j) + 2 ∧
        ∀ x ∈ internal ends (Vfam ends T I Jv U att j), x ∈ internal ends (T j) ∨
          ∃ v, j ∈ Jv v ∧ x ≠ v ∧ x ∈ ends (att v j) := by
  have hVJ : ∀ j, j ∉ I → Vfam ends T I Jv U att j = Vt ends (T j) (Dj Jv j) (fun v => att v j) :=
    fun j hj => by simp [Vfam, hj]
  have hVI : ∀ i ∈ I, Vfam ends T I Jv U att i = U i := fun i hi => by simp [Vfam, hi]
  -- membership in a restored tree
  have hmemVt : ∀ j e, e ∈ Vt ends (T j) (Dj Jv j) (fun v => att v j) →
      e ∈ Tm ends (T j) (Dj Jv j) ∨ ∃ v, j ∈ Jv v ∧ e = att v j := by
    intro j e he
    rcases Finset.mem_union.1 he with he | he
    · exact Or.inl he
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
      simp only [Dj, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact Or.inr ⟨v, hv, rfl⟩
  have hUP : ∀ i ∈ I, U i ⊆ Pset ends T I Jv pr := by
    intro i hi e he
    rw [← hX.2.2.2.2]
    exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨i, hi, he⟩)
  refine ⟨⟨⟨fun i => ?_, fun i i' hii' => ?_⟩, ?_⟩, hVI, fun j hj => ?_⟩
  · by_cases hi : i ∈ I
    · rw [hVI i hi]; exact hX.1 i hi
    · rw [hVJ i hi]; exact tree_vt (rhyp h ha i) h.simple
  · -- disjointness
    have key : ∀ i i', i ∈ I → i' ∉ I →
        Disjoint (Vfam ends T I Jv U att i) (Vfam ends T I Jv U att i') := by
      intro i i' hi hi'
      rw [hVI i hi, hVJ i' hi', Finset.disjoint_left]
      intro e he he'
      rcases hmemVt i' e he' with he' | ⟨v, hv, rfl⟩
      · exact tm_not_P h hi' he' (hUP i hi he)
      · rcases Finset.mem_union.1 (ha.mem v i' hv) with hp | hr
        · exact prot_not_P h hp (hUP i hi he)
        · exact Finset.disjoint_left.1 (hX.2.2.2.1 i hi v) he hr
    by_cases hi : i ∈ I <;> by_cases hi' : i' ∈ I
    · rw [hVI i hi, hVI i' hi']; exact hX.2.1 i hi i' hi' hii'
    · exact key i i' hi hi'
    · exact (key i' i hi' hi).symm
    · rw [hVJ i hi, hVJ i' hi', Finset.disjoint_left]
      intro e he he'
      rcases hmemVt i e he with he | ⟨v, hv, rfl⟩ <;>
        rcases hmemVt i' _ he' with he' | ⟨w, hw, hvw⟩
      · exact Finset.disjoint_left.1 (h.part.1.2 i i' hii')
          (Finset.mem_filter.1 he).1 (Finset.mem_filter.1 he').1
      · rw [hvw] at he
        exact Finset.disjoint_left.1 (tm_disj_Ev h hX hi w) he (ha.mem w i' hw)
      · exact Finset.disjoint_left.1 (tm_disj_Ev h hX hi' v) he' (ha.mem v i hv)
      · by_cases hvw' : v = w
        · subst hvw'
          exact hii' (ha.inj v hv hw hvw)
        · exact Finset.disjoint_left.1 (Ev_disj h hX hvw') (ha.mem v i hv)
            (hvw ▸ ha.mem w i' hw)
  · -- cover
    rw [Finset.eq_univ_iff_forall]
    intro e
    rw [Finset.mem_biUnion]
    -- edges of `E_v` are attachments
    have hEv : ∀ v, e ∈ Ev ends T pr R' v → ∃ i, i ∈ Finset.univ ∧ e ∈ Vfam ends T I Jv U att i := by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (ha.surj v hv)
      have hjI : j ∉ I := not_I_of_J h (h.jsub v hj)
      refine ⟨j, Finset.mem_univ _, ?_⟩
      rw [hVJ j hjI]
      exact att_mem_vt (by simp [Dj, hj])
    by_cases hP : e ∈ Pset ends T I Jv pr
    · rw [← hX.2.2.2.2] at hP
      rcases Finset.mem_union.1 hP with hP | hP
      · obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.1 hP
        exact ⟨i, Finset.mem_univ _, by rw [hVI i hi]; exact he⟩
      · obtain ⟨v, -, hv⟩ := Finset.mem_biUnion.1 hP
        exact hEv v (Finset.mem_union_right _ hv)
    · obtain ⟨t, ht⟩ : ∃ t, e ∈ T t := by
        have : e ∈ Finset.univ.biUnion T := by rw [h.part.2]; exact Finset.mem_univ e
        simpa using this
      have htI : t ∉ I := fun hti =>
        hP (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨t, hti, ht⟩))
      by_cases htm : e ∈ Tm ends (T t) (Dj Jv t)
      · exact ⟨t, Finset.mem_univ _, by rw [hVJ t htI]; exact tm_sub_vt htm⟩
      · have : ∃ v ∈ ends e, v ∈ Dj Jv t := by
          by_contra hc
          push_neg at hc
          exact htm (Finset.mem_filter.2 ⟨ht, hc⟩)
        obtain ⟨v, hve, hvD⟩ := this
        simp only [Dj, Finset.mem_filter, Finset.mem_univ, true_and] at hvD
        by_cases hpr : t ∈ pr v
        · exact hEv v (Finset.mem_union_left _ (mem_LE.2 ⟨t, hpr, ht, hve⟩))
        · exact absurd (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _,
            mem_LE.2 ⟨t, Finset.mem_sdiff.2 ⟨hvD, hpr⟩, ht, hve⟩⟩)) hP
  · have hjI : j ∉ I := not_I_of_J h hj
    rw [hVJ j hjI]
    refine ⟨diam_vt (rhyp h ha j) h.simple, fun x hx => ?_⟩
    rcases internal_vt (rhyp h ha j) hx with h1 | ⟨v, hv, hxv, hxe⟩
    · exact Or.inl h1
    · simp only [Dj, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact Or.inr ⟨v, hv, hxv, hxe⟩

end Exchange

end Global

end LowDiameterNashWilliams.Main.Dev.L43
end

section
/-! Lemma 4.3, part R: choosing the selections by averaging.

`A v` = `{∅}` on `S`, the `2r`-subsets of `L_v` (trees where `v` is a leaf) elsewhere.
A sample `ω ∈ ∏ A v` fails at `v ∉ S` if (t1) `|ω v ∩ ω x| > q` for a neighbour `x`, or
(t2) more than `q` protected heads `y` of `v` have `j ∈ ω y` for some `j ∈ ω v`. Each failure
has a witness (`h = q+1` common indices, or `h` heads), whose probability is at most
`32^{-h}`; summing gives `Σ_ω |Z ω| ≤ |Ω| 32^{-h} (2m C(2r,h) + n 2r C(r,h))` (`sum_Z_le`). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L43
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33
  LowDiameterNashWilliams.Main.Dev.L41

variable {n m k : ℕ}

/-! ### Heads and protected parts -/

/-- the other end of an edge at `v` -/
noncomputable def hd (ends : Fin m → Sym2 (Fin n)) (v : Fin n) (e : Fin m) : Fin n :=
  if h : v ∈ ends e then Sym2.Mem.other h else v

theorem hd_spec {ends : Fin m → Sym2 (Fin n)} {v : Fin n} {e : Fin m} (h : v ∈ ends e) :
    ends e = s(v, hd ends v e) := by
  simp only [hd, dif_pos h]; exact (Sym2.other_spec h).symm

theorem hd_ne {ends : Fin m → Sym2 (Fin n)} (hs : Simple ends) {v : Fin n} {e : Fin m}
    (h : v ∈ ends e) : hd ends v e ≠ v := by
  intro heq
  apply hs.2 e
  rw [hd_spec h, heq]; exact Sym2.mk_isDiag_iff.2 rfl

theorem hd_inj {ends : Fin m → Sym2 (Fin n)} (hs : Simple ends) {v : Fin n} {e e' : Fin m}
    (h : v ∈ ends e) (h' : v ∈ ends e') (heq : hd ends v e = hd ends v e') : e = e' :=
  hs.1 (by rw [hd_spec h, hd_spec h', heq])

theorem hd_injOn {ends : Fin m → Sym2 (Fin n)} (hs : Simple ends) {v : Fin n} (F : Edges m)
    (hF : ∀ e ∈ F, v ∈ ends e) : Set.InjOn (hd ends v) (F : Set (Fin m)) :=
  fun _ he _ he' heq => hd_inj hs (hF _ he) (hF _ he') heq

/-- a fixed `r`-subset -/
noncomputable def pr (r : ℕ) (a : Finset (Fin k)) : Finset (Fin k) :=
  if h : r ≤ a.card then Classical.choose (Finset.exists_subset_card_eq h) else a

theorem pr_sub (r : ℕ) (a : Finset (Fin k)) : pr r a ⊆ a := by
  unfold pr; split_ifs with h
  · exact (Classical.choose_spec (Finset.exists_subset_card_eq h)).1
  · exact le_rfl

theorem pr_card {r : ℕ} {a : Finset (Fin k)} (h : r ≤ a.card) : (pr r a).card = r := by
  unfold pr; rw [dif_pos h]
  exact (Classical.choose_spec (Finset.exists_subset_card_eq h)).2

/-- trees of `J` in which `v` is a leaf -/
noncomputable def Lv (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (J : Finset (Fin k))
    (v : Fin n) : Finset (Fin k) :=
  J.filter fun j => degIn ends (T j) v = 1

/-- the selection space at `v` -/
noncomputable def Asp (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (J : Finset (Fin k))
    (S : Finset (Fin n)) (r : ℕ) (v : Fin n) : Finset (Finset (Fin k)) :=
  if v ∈ S then {∅} else (Lv ends T J v).powersetCard (2 * r)

/-- heads of the protected edges -/
noncomputable def Yh (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (r : ℕ) (v : Fin n)
    (a : Finset (Fin k)) : Finset (Fin n) :=
  (LE ends T v (pr r a)).image (hd ends v)

def t1 (ends : Fin m → Sym2 (Fin n)) (q : ℕ) (ω : Fin n → Finset (Fin k)) (v : Fin n) : Prop :=
  ∀ x, x ≠ v → (∃ e, ends e = s(v, x)) → (ω v ∩ ω x).card ≤ q

def t2 (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (r q : ℕ) (ω : Fin n → Finset (Fin k))
    (v : Fin n) : Prop :=
  ∀ j ∈ ω v, ((LE ends T v (pr r (ω v))).filter (fun e => j ∈ ω (hd ends v e))).card ≤ q

noncomputable def Zset (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (S : Finset (Fin n))
    (r q : ℕ) (ω : Fin n → Finset (Fin k)) : Finset (Fin n) :=
  Finset.univ.filter fun v => v ∉ S ∧ ¬ (t1 ends q ω v ∧ t2 ends T r q ω v)

noncomputable def nbr (ends : Fin m → Sym2 (Fin n)) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x => x ≠ v ∧ ∃ e, ends e = s(v, x)

section Avg

variable {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {J : Finset (Fin k)}
  {S : Finset (Fin n)} {r q : ℕ}

theorem Asp_nonempty (hL : ∀ v, v ∉ S → 64 * r ≤ (Lv ends T J v).card) (v : Fin n) :
    (Asp ends T J S r v).Nonempty := by
  unfold Asp; split_ifs with hv
  · exact Finset.singleton_nonempty _
  · exact Finset.powersetCard_nonempty.2 (by have := hL v hv; omega)

theorem mem_Asp {v : Fin n} (hv : v ∉ S) {a : Finset (Fin k)} (ha : a ∈ Asp ends T J S r v) :
    a ⊆ Lv ends T J v ∧ a.card = 2 * r := by
  unfold Asp at ha; rw [if_neg hv] at ha
  exact Finset.mem_powersetCard.1 ha

theorem mem_Asp_S {v : Fin n} (hv : v ∈ S) {a : Finset (Fin k)} (ha : a ∈ Asp ends T J S r v) :
    a = ∅ := by
  unfold Asp at ha; rw [if_pos hv] at ha
  exact Finset.mem_singleton.1 ha

/-- `Pr[Q ⊆ ω_x] ≤ 32^{-|Q|}` -/
theorem ratio_le (hL : ∀ v, v ∉ S → 64 * r ≤ (Lv ends T J v).card) (x : Fin n)
    (Q : Finset (Fin k)) (hQ : Q.Nonempty) :
    ((((Asp ends T J S r x).filter (fun b => Q ⊆ b)).card : ℕ) : ℝ) ≤
      (1 / 32 : ℝ) ^ Q.card * (Asp ends T J S r x).card := by
  by_cases hx : x ∈ S
  · have : (Asp ends T J S r x).filter (fun b => Q ⊆ b) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro b hb hQb
      rw [mem_Asp_S hx hb] at hQb
      obtain ⟨j, hj⟩ := hQ
      exact absurd (hQb hj) (Finset.notMem_empty j)
    rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  · unfold Asp; rw [if_neg hx]
    refine (card_contain_le _ Q (2 * r)).trans ?_
    have hrat : ((2 * r : ℕ) : ℝ) / (Lv ends T J x).card ≤ 1 / 32 := by
      have := hL x hx
      rcases Nat.eq_zero_or_pos (Lv ends T J x).card with h0 | hpos
      · rw [h0]; simp
      · rw [div_le_div_iff₀ (by exact_mod_cast hpos) (by norm_num)]
        have : ((64 * r : ℕ) : ℝ) ≤ (Lv ends T J x).card := by exact_mod_cast this
        push_cast at this ⊢
        linarith
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hrat _) (by positivity)

theorem card_biUnion_real {α β : Type*} [DecidableEq β] (s : Finset α) (t : α → Finset β) :
    (((s.biUnion t).card : ℕ) : ℝ) ≤ ∑ a ∈ s, (((t a).card : ℕ) : ℝ) := by
  exact_mod_cast Finset.card_biUnion_le

/-- failures of test 1 at a pair `(v, x)` -/
theorem c1_le (hL : ∀ v, v ∉ S → 64 * r ≤ (Lv ends T J v).card) {v x : Fin n} (hv : v ∉ S)
    (hxv : x ≠ v) :
    ((((Fintype.piFinset (Asp ends T J S r)).filter
        (fun ω => ¬ (ω v ∩ ω x).card ≤ q)).card : ℕ) : ℝ) ≤
      ((2 * r).choose (q + 1) : ℝ) * (1 / 32 : ℝ) ^ (q + 1) *
        (Fintype.piFinset (Asp ends T J S r)).card := by
  set A := Asp ends T J S r with hAdef
  set Om := Fintype.piFinset A with hOm
  have hAv : (0 : ℝ) < (A v).card := by exact_mod_cast (Asp_nonempty hL v).card_pos
  have hsub : Om.filter (fun ω => ¬ (ω v ∩ ω x).card ≤ q) ⊆
      (A v).biUnion (fun a => (a.powersetCard (q + 1)).biUnion (fun Q =>
        Om.filter (fun ω => ω v = a ∧ ∀ y ∈ ({x} : Finset (Fin n)), Q ⊆ ω y))) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    obtain ⟨Q, hQsub, hQcard⟩ := Finset.exists_subset_card_eq (s := ω v ∩ ω x) (n := q + 1)
      (by omega)
    refine Finset.mem_biUnion.2 ⟨ω v, Fintype.mem_piFinset.1 hω.1 v, Finset.mem_biUnion.2
      ⟨Q, Finset.mem_powersetCard.2 ⟨hQsub.trans Finset.inter_subset_left, hQcard⟩,
        Finset.mem_filter.2 ⟨hω.1, rfl, ?_⟩⟩⟩
    intro y hy
    rw [Finset.mem_singleton.1 hy]
    exact hQsub.trans Finset.inter_subset_right
  have hterm : ∀ a ∈ A v, ∀ Q ∈ a.powersetCard (q + 1),
      (((Om.filter (fun ω => ω v = a ∧ ∀ y ∈ ({x} : Finset (Fin n)), Q ⊆ ω y)).card : ℕ) : ℝ)
        ≤ (1 / 32 : ℝ) ^ (q + 1) * Om.card / (A v).card := by
    intro a ha Q hQ
    rw [Finset.mem_powersetCard] at hQ
    have hQne : Q.Nonempty := Finset.card_pos.1 (by omega)
    have := card_cond_le A {x} (v := v) (a := a) (by simp [hxv.symm]) (fun _ b => Q ⊆ b)
      (fun _ => (1 / 32 : ℝ) ^ (q + 1)) (fun _ => by positivity) (fun y hy => by
        rw [Finset.mem_singleton.1 hy]
        have := ratio_le hL x Q hQne
        rw [hQ.2] at this; convert this using 3)
    rw [Finset.prod_singleton] at this
    rw [le_div_iff₀ hAv]
    convert this using 3 <;> first | rfl | congr
  have hcardQ : ∀ a ∈ A v, (a.powersetCard (q + 1)).card = (2 * r).choose (q + 1) := by
    intro a ha
    rw [Finset.card_powersetCard, (mem_Asp hv ha).2]
  calc ((((Om.filter (fun ω => ¬ (ω v ∩ ω x).card ≤ q)).card : ℕ) : ℝ))
      ≤ ∑ a ∈ A v, ∑ Q ∈ a.powersetCard (q + 1),
          (((Om.filter (fun ω => ω v = a ∧ ∀ y ∈ ({x} : Finset (Fin n)), Q ⊆ ω y)).card : ℕ) : ℝ)
          := by
        refine (Nat.cast_le.2 (Finset.card_le_card hsub)).trans ?_
        refine (card_biUnion_real _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        exact card_biUnion_real _ _
    _ ≤ ∑ a ∈ A v, ∑ _Q ∈ a.powersetCard (q + 1), (1 / 32 : ℝ) ^ (q + 1) * Om.card / (A v).card :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun Q hQ => hterm a ha Q hQ
    _ = ∑ _a ∈ A v, ((2 * r).choose (q + 1) : ℝ) * ((1 / 32 : ℝ) ^ (q + 1) * Om.card / (A v).card) :=
        Finset.sum_congr rfl fun a ha => by rw [Finset.sum_const, nsmul_eq_mul, hcardQ a ha]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; field_simp

/-- failures of test 2 at `v` -/
theorem c2_le (hs : Simple ends) (hT : TreePartition ends T)
    (hL : ∀ v, v ∉ S → 64 * r ≤ (Lv ends T J v).card) {v : Fin n} (hv : v ∉ S) :
    ((((Fintype.piFinset (Asp ends T J S r)).filter
        (fun ω => ¬ t2 ends T r q ω v)).card : ℕ) : ℝ) ≤
      ((2 * r : ℕ) : ℝ) * (r.choose (q + 1) : ℝ) * (1 / 32 : ℝ) ^ (q + 1) *
        (Fintype.piFinset (Asp ends T J S r)).card := by
  set A := Asp ends T J S r with hAdef
  set Om := Fintype.piFinset A with hOm
  have hAv : (0 : ℝ) < (A v).card := by exact_mod_cast (Asp_nonempty hL v).card_pos
  -- edges of `LE v (pr a)` contain `v`
  have hLEv : ∀ a : Finset (Fin k), ∀ e ∈ LE ends T v (pr r a), v ∈ ends e := by
    intro a e he; obtain ⟨_, _, _, h⟩ := mem_LE.1 he; exact h
  have hsub : Om.filter (fun ω => ¬ t2 ends T r q ω v) ⊆
      (A v).biUnion (fun a => a.biUnion (fun j => ((Yh ends T r v a).powersetCard (q + 1)).biUnion
        (fun Q => Om.filter (fun ω => ω v = a ∧ ∀ y ∈ Q, j ∈ ω y)))) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    obtain ⟨hωO, hω2⟩ := hω
    unfold t2 at hω2
    push Not at hω2
    obtain ⟨j, hj, hjq⟩ := hω2
    obtain ⟨F, hFsub, hFcard⟩ := Finset.exists_subset_card_eq
      (s := (LE ends T v (pr r (ω v))).filter (fun e => j ∈ ω (hd ends v e))) (n := q + 1)
      (by omega)
    have hFv : ∀ e ∈ F, v ∈ ends e := fun e he =>
      hLEv _ e (Finset.mem_filter.1 (hFsub he)).1
    refine Finset.mem_biUnion.2 ⟨ω v, Fintype.mem_piFinset.1 hωO v, Finset.mem_biUnion.2
      ⟨j, hj, Finset.mem_biUnion.2 ⟨F.image (hd ends v), Finset.mem_powersetCard.2 ⟨?_, ?_⟩,
        Finset.mem_filter.2 ⟨hωO, rfl, ?_⟩⟩⟩⟩
    · intro y hy
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.1 (hFsub he)).1
    · rw [Finset.card_image_of_injOn (hd_injOn hs F hFv), hFcard]
    · intro y hy
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy
      exact (Finset.mem_filter.1 (hFsub he)).2
  have hterm : ∀ a ∈ A v, ∀ j ∈ a, ∀ Q ∈ (Yh ends T r v a).powersetCard (q + 1),
      (((Om.filter (fun ω => ω v = a ∧ ∀ y ∈ Q, j ∈ ω y)).card : ℕ) : ℝ)
        ≤ (1 / 32 : ℝ) ^ (q + 1) * Om.card / (A v).card := by
    intro a ha j hj Q hQ
    rw [Finset.mem_powersetCard] at hQ
    have hvQ : v ∉ Q := by
      intro hvQ
      obtain ⟨e, he, hev⟩ := Finset.mem_image.1 (hQ.1 hvQ)
      exact hd_ne hs (hLEv a e he) hev
    have := card_cond_le A Q (v := v) (a := a) hvQ (fun _ b => j ∈ b)
      (fun _ => (1 / 32 : ℝ)) (fun _ => by positivity) (fun y _ => by
        have := ratio_le hL y {j} (Finset.singleton_nonempty j)
        rw [Finset.card_singleton, pow_one] at this
        convert this using 4
        simp)
    rw [Finset.prod_const, hQ.2] at this
    rw [le_div_iff₀ hAv]
    convert this using 3 <;> first | rfl | congr
  have hcardY : ∀ a ∈ A v, ((Yh ends T r v a).powersetCard (q + 1)).card ≤ r.choose (q + 1) := by
    intro a ha
    rw [Finset.card_powersetCard]
    apply Nat.choose_le_choose
    refine Finset.card_image_le.trans ?_
    have hal := mem_Asp hv ha
    rw [card_LE hT (fun j hj => by
      have := hal.1 (pr_sub r a hj)
      exact (Finset.mem_filter.1 this).2)]
    rw [pr_card (by omega)]
  have hcarda : ∀ a ∈ A v, a.card = 2 * r := fun a ha => (mem_Asp hv ha).2
  set B : ℝ := (1 / 32 : ℝ) ^ (q + 1) * Om.card / (A v).card with hB
  have hB0 : 0 ≤ B := by positivity
  calc ((((Om.filter (fun ω => ¬ t2 ends T r q ω v)).card : ℕ) : ℝ))
      ≤ ∑ a ∈ A v, ∑ j ∈ a, ∑ Q ∈ (Yh ends T r v a).powersetCard (q + 1),
          (((Om.filter (fun ω => ω v = a ∧ ∀ y ∈ Q, j ∈ ω y)).card : ℕ) : ℝ) := by
        refine (Nat.cast_le.2 (Finset.card_le_card hsub)).trans ?_
        refine (card_biUnion_real _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (card_biUnion_real _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        exact card_biUnion_real _ _
    _ ≤ ∑ a ∈ A v, ∑ _j ∈ a, ∑ _Q ∈ (Yh ends T r v a).powersetCard (q + 1), B :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun j hj =>
          Finset.sum_le_sum fun Q hQ => hterm a ha j hj Q hQ
    _ ≤ ∑ _a ∈ A v, ((2 * r : ℕ) : ℝ) * ((r.choose (q + 1) : ℝ) * B) := by
        refine Finset.sum_le_sum fun a ha => ?_
        rw [Finset.sum_const, nsmul_eq_mul, hcarda a ha]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardY a ha) hB0
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hB]; field_simp

theorem nbr_card_le (hs : Simple ends) (v : Fin n) :
    (nbr ends v).card ≤ (Finset.univ.filter (fun e => v ∈ ends e)).card := by
  refine le_trans (Finset.card_le_card (t := (Finset.univ.filter (fun e => v ∈ ends e)).image
    (hd ends v)) ?_) Finset.card_image_le
  intro x hx
  simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨hxv, e, he⟩ := hx
  have hve : v ∈ ends e := by rw [he]; exact Sym2.mem_mk_left _ _
  refine Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨Finset.mem_univ _, hve⟩, ?_⟩
  have := hd_spec hve
  rw [he] at this
  exact (Sym2.congr_right.1 this).symm

theorem sum_deg_le : ∑ v : Fin n, (Finset.univ.filter (fun e => v ∈ ends e)).card ≤ 2 * m := by
  have : ∀ v : Fin n, (Finset.univ.filter (fun e => v ∈ ends e)).card =
      ∑ e : Fin m, if v ∈ ends e then 1 else 0 := fun v => Finset.card_filter _ _
  simp only [this]
  rw [Finset.sum_comm]
  have h2 : ∀ e : Fin m, (∑ v : Fin n, if v ∈ ends e then 1 else 0) ≤ 2 := by
    intro e
    rw [← Finset.card_filter]
    obtain ⟨a, b, hab⟩ := exists_ends ends e
    have : Finset.univ.filter (fun v => v ∈ ends e) ⊆ {a, b} := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      rw [hab, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl <;> simp
    exact (Finset.card_le_card this).trans Finset.card_le_two
  calc ∑ e : Fin m, ∑ v : Fin n, (if v ∈ ends e then 1 else 0) ≤ ∑ _e : Fin m, 2 :=
        Finset.sum_le_sum fun e _ => h2 e
    _ = 2 * m := by simp [mul_comm]

/-- the expected number of failed vertices -/
theorem sum_Z_le (hs : Simple ends) (hT : TreePartition ends T)
    (hL : ∀ v, v ∉ S → 64 * r ≤ (Lv ends T J v).card) :
    ∑ ω ∈ Fintype.piFinset (Asp ends T J S r), ((Zset ends T S r q ω).card : ℝ) ≤
      ((2 * m : ℝ) * (((2 * r).choose (q + 1) : ℝ) * (1 / 32 : ℝ) ^ (q + 1)) +
        n * (((2 * r : ℕ) : ℝ) * (r.choose (q + 1) : ℝ) * (1 / 32 : ℝ) ^ (q + 1))) *
        (Fintype.piFinset (Asp ends T J S r)).card := by
  set Om := Fintype.piFinset (Asp ends T J S r) with hOm
  set c1 : ℝ := ((2 * r).choose (q + 1) : ℝ) * (1 / 32 : ℝ) ^ (q + 1) with hc1
  set c2 : ℝ := ((2 * r : ℕ) : ℝ) * (r.choose (q + 1) : ℝ) * (1 / 32 : ℝ) ^ (q + 1) with hc2
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have hZ : ∀ ω, ((Zset ends T S r q ω).card : ℝ) = ∑ v : Fin n,
      (if v ∉ S ∧ ¬ (t1 ends q ω v ∧ t2 ends T r q ω v) then (1 : ℝ) else 0) := by
    intro ω; unfold Zset; rw [Finset.card_filter]; push_cast; rfl
  simp only [hZ]
  rw [Finset.sum_comm]
  have hv : ∀ v : Fin n, ∑ ω ∈ Om,
      (if v ∉ S ∧ ¬ (t1 ends q ω v ∧ t2 ends T r q ω v) then (1 : ℝ) else 0) ≤
        ((nbr ends v).card * c1 + c2) * Om.card := by
    intro v
    rw [Finset.sum_boole]
    by_cases hvS : v ∈ S
    · have : Om.filter (fun ω => v ∉ S ∧ ¬ (t1 ends q ω v ∧ t2 ends T r q ω v)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro ω _ h; exact h.1 hvS
      rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
    have hsub : Om.filter (fun ω => v ∉ S ∧ ¬ (t1 ends q ω v ∧ t2 ends T r q ω v)) ⊆
        (nbr ends v).biUnion (fun x => Om.filter (fun ω => ¬ (ω v ∩ ω x).card ≤ q)) ∪
          Om.filter (fun ω => ¬ t2 ends T r q ω v) := by
      intro ω hω
      rw [Finset.mem_filter] at hω
      obtain ⟨hωO, -, hbad⟩ := hω
      by_cases h1 : t1 ends q ω v
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hωO, fun h2 => hbad ⟨h1, h2⟩⟩)
      · unfold t1 at h1
        push Not at h1
        obtain ⟨x, hxv, hadj, hxq⟩ := h1
        refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨x, ?_, ?_⟩)
        · simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hxv, hadj⟩
        · exact Finset.mem_filter.2 ⟨hωO, by omega⟩
    refine (Nat.cast_le.2 (Finset.card_le_card hsub)).trans ?_
    refine (Nat.cast_le.2 (Finset.card_union_le _ _)).trans ?_
    push_cast
    have hA := card_biUnion_real (nbr ends v) (fun x => Om.filter (fun ω => ¬ (ω v ∩ ω x).card ≤ q))
    have hB : ∑ x ∈ nbr ends v, ((((Om.filter (fun ω => ¬ (ω v ∩ ω x).card ≤ q)).card : ℕ) : ℝ))
        ≤ ∑ _x ∈ nbr ends v, c1 * Om.card := by
      refine Finset.sum_le_sum fun x hx => ?_
      have hxv : x ≠ v := by
        simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx.1
      exact c1_le hL hvS hxv
    have hC := c2_le (q := q) hs hT hL hvS
    rw [Finset.sum_const, nsmul_eq_mul] at hB
    have : (((nbr ends v).biUnion (fun x => Om.filter (fun ω => ¬ (ω v ∩ ω x).card ≤ q))).card : ℝ)
        ≤ (nbr ends v).card * (c1 * Om.card) := by exact_mod_cast hA.trans hB
    nlinarith
  calc ∑ v : Fin n, ∑ ω ∈ Om,
        (if v ∉ S ∧ ¬ (t1 ends q ω v ∧ t2 ends T r q ω v) then (1 : ℝ) else 0)
      ≤ ∑ v : Fin n, ((nbr ends v).card * c1 + c2) * Om.card := Finset.sum_le_sum fun v _ => hv v
    _ = ((∑ v : Fin n, ((nbr ends v).card : ℝ)) * c1 + n * c2) * Om.card := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_mul]; simp
    _ ≤ ((2 * m : ℝ) * c1 + n * c2) * Om.card := by
        gcongr
        have : ∑ v : Fin n, (nbr ends v).card ≤ 2 * m :=
          (Finset.sum_le_sum fun v _ => nbr_card_le hs v).trans sum_deg_le
        exact_mod_cast this

/-- a good selection exists -/
theorem select (hs : Simple ends) (hT : TreePartition ends T)
    (hL : ∀ v, v ∉ S → 64 * r ≤ (Lv ends T J v).card) :
    ∃ ω : Fin n → Finset (Fin k), (∀ v, ω v ∈ Asp ends T J S r v) ∧
      ((Zset ends T S r q ω).card : ℝ) ≤
        (2 * m : ℝ) * (((2 * r).choose (q + 1) : ℝ) * (1 / 32 : ℝ) ^ (q + 1)) +
          n * (((2 * r : ℕ) : ℝ) * (r.choose (q + 1) : ℝ) * (1 / 32 : ℝ) ^ (q + 1)) := by
  have hne : (Fintype.piFinset (Asp ends T J S r)).Nonempty :=
    Fintype.piFinset_nonempty.2 (fun v => Asp_nonempty hL v)
  obtain ⟨ω, hω, hle⟩ := exists_le_avg _ hne _ _ (sum_Z_le (q := q) hs hT hL)
  exact ⟨ω, Fintype.mem_piFinset.1 hω, hle⟩

end Avg

end LowDiameterNashWilliams.Main.Dev.L43
end

section
/-! Lemma 4.3, part M: matchings through Lemma 4.4.

`encN`: a bipartite relation between two `M`-element finsets `A`, `B`, encoded as a
neighbour map on `Fin M`. `pm_exists` (Lemma 4.4 (i)): degree sums `≥ 5M/4` give an injection
`g : A → B` inside the relation. `count_fail` (Lemma 4.4 (ii)): when the relation is restricted
by independent random sets `C a` (`b` matched to `a` only if `φ b ∈ C a`) with avoidance
probabilities `≤ e^{-p|Y|}`, the number of samples without such an injection is at most
`4 M^{-11}` times the number of samples. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators ENNReal NNReal

namespace LowDiameterNashWilliams.Main.Dev.L43
open LowDiameterNashWilliams.Main

section Encode

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

noncomputable def eqv {γ : Type*} [DecidableEq γ] (A : Finset γ) {M : ℕ} (hA : A.card = M) :
    {x // x ∈ A} ≃ Fin M :=
  Fintype.equivFinOfCardEq (by simp [hA])

noncomputable def encN (A : Finset α) (B : Finset β) {M : ℕ} (hA : A.card = M)
    (hB : B.card = M) (Rel : α → β → Prop) : Fin M → Finset (Fin M) := fun i =>
  Finset.univ.filter fun l => Rel ((eqv A hA).symm i).1 ((eqv B hB).symm l).1

theorem card_enc {γ : Type*} [DecidableEq γ] (A : Finset γ) {M : ℕ} (hA : A.card = M)
    (P : γ → Prop) :
    (Finset.univ.filter fun i : Fin M => P ((eqv A hA).symm i).1).card = (A.filter P).card := by
  refine Finset.card_bij (fun i _ => ((eqv A hA).symm i).1) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨((eqv A hA).symm i).2, hi.2⟩
  · intro i _ j _ hij
    exact (eqv A hA).symm.injective (Subtype.ext hij)
  · intro x hx
    rw [Finset.mem_filter] at hx
    refine ⟨eqv A hA ⟨x, hx.1⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]; simp [hx.2]
    · simp

theorem pm_att [Nonempty β] {A : Finset α} {B : Finset β} {M : ℕ} {hA : A.card = M}
    {hB : B.card = M} {Rel : α → β → Prop} (h : PerfectMatching (encN A B hA hB Rel)) :
    ∃ g : α → β, (∀ a ∈ A, g a ∈ B ∧ Rel a (g a)) ∧ Set.InjOn g (A : Set α) := by
  obtain ⟨f, hf⟩ := h
  let g : α → β := fun a =>
    if ha : a ∈ A then ((eqv B hB).symm (f (eqv A hA ⟨a, ha⟩))).1 else Classical.arbitrary β
  refine ⟨g, fun a ha => ?_, fun a ha a' ha' hg => ?_⟩
  · have := hf (eqv A hA ⟨a, ha⟩)
    simp only [encN, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.symm_apply_apply] at this
    simp only [g, dif_pos ha]
    exact ⟨((eqv B hB).symm _).2, this⟩
  · simp only [Finset.mem_coe] at ha ha'
    simp only [g, dif_pos ha, dif_pos ha'] at hg
    have h1 := (eqv B hB).symm.injective (Subtype.ext hg)
    have h2 := f.injective h1
    have h3 := (eqv A hA).injective h2
    exact congrArg Subtype.val h3

theorem leftMin_ge {A : Finset α} {B : Finset β} {M : ℕ} (hA : A.card = M)
    (hB : B.card = M) (Rel : α → β → Prop) (d : ℕ) (hM : 0 < M)
    (hd : ∀ b ∈ B, d ≤ (A.filter fun a => Rel a b).card) :
    d ≤ leftMin (encN A B hA hB Rel) := by
  unfold leftMin
  rw [dif_pos ⟨⟨0, hM⟩, Finset.mem_univ _⟩]
  refine Finset.le_inf' _ _ fun l _ => ?_
  have := card_enc A hA (fun a => Rel a ((eqv B hB).symm l).1)
  simp only [encN, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [this]
  exact hd _ ((eqv B hB).symm l).2

theorem rightMin_ge {A : Finset α} {B : Finset β} {M : ℕ} (hA : A.card = M)
    (hB : B.card = M) (Rel : α → β → Prop) (d : ℕ) (hM : 0 < M)
    (hd : ∀ a ∈ A, d ≤ (B.filter fun b => Rel a b).card) :
    d ≤ rightMin (encN A B hA hB Rel) := by
  unfold rightMin
  rw [dif_pos ⟨⟨0, hM⟩, Finset.mem_univ _⟩]
  refine Finset.le_inf' _ _ fun i _ => ?_
  have := card_enc B hB (fun b => Rel ((eqv A hA).symm i).1 b)
  simp only [encN]
  rw [this]
  exact hd _ ((eqv A hA).symm i).2

theorem delta_enc {A : Finset α} {B : Finset β} {M : ℕ} (hA : A.card = M)
    (hB : B.card = M) (Rel : α → β → Prop) (dl dr : ℕ) (hM : 0 < M)
    (hl : ∀ b ∈ B, dl ≤ (A.filter fun a => Rel a b).card)
    (hr : ∀ a ∈ A, dr ≤ (B.filter fun b => Rel a b).card) (h5 : 5 * M ≤ 4 * (dl + dr)) :
    (5 : ℝ) * M / 4 ≤ (leftMin (encN A B hA hB Rel) : ℝ) + rightMin (encN A B hA hB Rel) := by
  have h1 := leftMin_ge hA hB Rel dl hM hl
  have h2 := rightMin_ge hA hB Rel dr hM hr
  have : (5 : ℝ) * M ≤ 4 * ((dl : ℝ) + dr) := by exact_mod_cast h5
  have h1' : (dl : ℝ) ≤ leftMin (encN A B hA hB Rel) := by exact_mod_cast h1
  have h2' : (dr : ℝ) ≤ rightMin (encN A B hA hB Rel) := by exact_mod_cast h2
  linarith

/-- Lemma 4.4 (i) in the finset form -/
theorem pm_exists [Nonempty β] {A : Finset α} {B : Finset β} {M : ℕ} (hA : A.card = M)
    (hB : B.card = M) (hM : 2 ≤ M) (Rel : α → β → Prop) (dl dr : ℕ)
    (hl : ∀ b ∈ B, dl ≤ (A.filter fun a => Rel a b).card)
    (hr : ∀ a ∈ A, dr ≤ (B.filter fun b => Rel a b).card) (h5 : 5 * M ≤ 4 * (dl + dr)) :
    ∃ g : α → β, (∀ a ∈ A, g a ∈ B ∧ Rel a (g a)) ∧ Set.InjOn g (A : Set α) :=
  pm_att ((lemma_4_4 M hM _ (delta_enc hA hB Rel dl dr (by omega) hl hr h5)).1)

end Encode

/-! ### The probabilistic part -/

section Prob

variable {α γ : Type*} [Fintype α] [DecidableEq α]

theorem pmf_ofReal_sum {M : ℕ} (ρ : Finset (Fin M) → ℝ) (h0 : ∀ S, 0 ≤ ρ S)
    (h1 : ∑ S, ρ S = 1) : ∑ S, ENNReal.ofReal (ρ S) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ => h0 S), h1, ENNReal.ofReal_one]

theorem fail_count {M : ℕ} (hM : 2 ≤ M) (N : Fin M → Finset (Fin M))
    (hδ : (5 : ℝ) * M / 4 ≤ (leftMin N : ℝ) + rightMin N) (ι : Fin M → α)
    (hι : Function.Injective ι) (Ω : α → Finset γ) (hΩ : ∀ a, (Ω a).Nonempty)
    (g : Fin M → γ → Finset (Fin M)) (hg : ∀ i c, g i c ⊆ N i) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p ≤ 1) (hpM : 96 * Real.log M ≤ p * M)
    (hav : ∀ i X, X ⊆ N i → ((((Ω (ι i)).filter (fun c => Disjoint (g i c) X)).card : ℕ) : ℝ) ≤
      Real.exp (-p * X.card) * (Ω (ι i)).card) :
    ((((Fintype.piFinset Ω).filter
        (fun C => ¬ PerfectMatching (fun i => g i (C (ι i))))).card : ℕ) : ℝ) ≤
      4 * (M : ℝ) ^ (-(11 : ℤ)) * (Fintype.piFinset Ω).card := by
  -- weights
  set w : Fin M → Finset (Fin M) → ℕ := fun i S => ((Ω (ι i)).filter (fun c => g i c = S)).card
    with hw
  have htot : ∀ i, (0 : ℝ) < (Ω (ι i)).card := fun i => by exact_mod_cast (hΩ (ι i)).card_pos
  set ρ : Fin M → Finset (Fin M) → ℝ := fun i S => (w i S : ℝ) / (Ω (ι i)).card with hρ
  have hρ0 : ∀ i S, 0 ≤ ρ i S := fun i S => by positivity
  have hfib : ∀ i (Q : Finset (Fin M) → Prop) [DecidablePred Q],
      ∑ S, (if Q S then (w i S : ℝ) else 0) = (((Ω (ι i)).filter (fun c => Q (g i c))).card : ℝ) := by
    intro i Q _
    rw [Finset.card_eq_sum_card_fiberwise (f := g i) (t := Finset.univ.filter Q)]
    · push_cast
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun S _ => ?_
      split_ifs with hQ
      · have : (Ω (ι i)).filter (fun c => g i c = S) =
            ((Ω (ι i)).filter (fun c => Q (g i c))).filter (fun c => g i c = S) := by
          ext c; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hc, rfl⟩; exact ⟨⟨hc, hQ⟩, rfl⟩
          · rintro ⟨⟨hc, -⟩, rfl⟩; exact ⟨hc, rfl⟩
        simp only [hw, this]
      · rfl
    · intro c hc
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact hc.2
  have hρsum : ∀ i, ∑ S, ρ i S = 1 := by
    intro i
    have := hfib i (fun _ => True)
    simp only [if_true] at this
    rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at this
    simp only [hρ, ← Finset.sum_div, this]
    exact div_self (htot i).ne'
  let μ : Fin M → PMF (Finset (Fin M)) := fun i =>
    PMF.ofFintype (fun S => ENNReal.ofReal (ρ i S)) (pmf_ofReal_sum _ (hρ0 i) (hρsum i))
  have hμ : ∀ i S, μ i S = ENNReal.ofReal (ρ i S) := fun i S => PMF.ofFintype_apply _ _
  have hsupp : ∀ i S, μ i S ≠ 0 → S ⊆ N i := by
    intro i S hS
    rw [hμ, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hS
    have : 0 < w i S := by
      by_contra h0
      simp only [hρ, Nat.pos_iff_ne_zero, not_not] at h0
      simp [hρ, h0] at hS
    obtain ⟨c, hc⟩ := Finset.card_pos.1 this
    rw [Finset.mem_filter] at hc
    rw [← hc.2]; exact hg i c
  have havoid : ∀ i X, X ⊆ N i →
      avoidance (μ i) X ≤ ENNReal.ofReal (Real.exp (-p * X.card)) := by
    intro i X hX
    unfold avoidance
    have : ∑ S : Finset (Fin M), (if Disjoint S X then μ i S else 0) =
        ENNReal.ofReal (∑ S, if Disjoint S X then ρ i S else 0) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun S _ => by split_ifs <;> simp [hρ0])]
      refine Finset.sum_congr rfl fun S _ => ?_
      split_ifs <;> simp [hμ]
    rw [this]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : ∑ S, (if Disjoint S X then ρ i S else 0) =
        (∑ S, if Disjoint S X then (w i S : ℝ) else 0) / (Ω (ι i)).card := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun S _ => ?_
      split_ifs <;> simp [hρ]
    have hf := hfib i (fun S => Disjoint S X)
    rw [e, hf, div_le_iff₀ (htot i)]
    exact hav i X hX
  have hmain := (lemma_4_4 M hM N hδ).2 μ p hp0 hp1 hsupp havoid hpM
  -- matching probability as a real number
  have hmp : matchingProbability μ =
      ENNReal.ofReal (∑ s : Fin M → Finset (Fin M),
        if PerfectMatching s then ∏ i, ρ i (s i) else 0) := by
    unfold matchingProbability
    rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => by
      split_ifs
      · exact Finset.prod_nonneg fun i _ => hρ0 i _
      · exact le_refl _)]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs
    · rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hρ0 i _)]
      simp [hμ]
    · simp
  rw [hmp, ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun s _ => by
    split_ifs
    · exact Finset.prod_nonneg fun i _ => hρ0 i _
    · exact le_refl _)] at hmain
  have htotal : ∑ s : Fin M → Finset (Fin M), ∏ i, ρ i (s i) = 1 := by
    rw [← Fintype.prod_sum]
    simp [hρsum]
  have hbad : ∑ s : Fin M → Finset (Fin M),
      (if PerfectMatching s then 0 else ∏ i, ρ i (s i)) ≤ 4 * (M : ℝ) ^ (-(11 : ℤ)) := by
    have : ∑ s : Fin M → Finset (Fin M), (if PerfectMatching s then 0 else ∏ i, ρ i (s i)) =
        1 - ∑ s : Fin M → Finset (Fin M), if PerfectMatching s then ∏ i, ρ i (s i) else 0 := by
      rw [← htotal, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs <;> ring
    rw [this]; linarith
  -- counting the samples with a given restricted graph
  have hcount : ∀ s : Fin M → Finset (Fin M),
      ((((Fintype.piFinset Ω).filter (fun C => (fun i => g i (C (ι i))) = s)).card : ℕ) : ℝ) =
        (∏ i, ρ i (s i)) * (Fintype.piFinset Ω).card := by
    intro s
    have hf : (Fintype.piFinset Ω).filter (fun C => (fun i => g i (C (ι i))) = s) =
        (Fintype.piFinset Ω).filter
          (fun C => ∀ a, ∀ i, ι i = a → g i (C a) = s i) := by
      apply Finset.filter_congr
      intro C _
      constructor
      · rintro h a i rfl; exact congrFun h i
      · intro h; funext i; exact h (ι i) i rfl
    have hf2 := pi_filter_eq Ω (fun a c => ∀ i, ι i = a → g i c = s i)
    have hf3 : (Fintype.piFinset Ω).filter (fun C => (fun i => g i (C (ι i))) = s) =
        Fintype.piFinset fun a => (Ω a).filter (fun c => ∀ i, ι i = a → g i c = s i) := by
      rw [hf]; convert hf2
    rw [hf3, Fintype.card_piFinset, Fintype.card_piFinset]
    push_cast
    set F : α → ℝ := fun a =>
      (((Ω a).filter (fun c => ∀ i, ι i = a → g i c = s i)).card : ℝ) with hF
    have hFi : ∀ i, F (ι i) = w i (s i) := by
      intro i
      simp only [hF, hw]
      congr 3
      ext c
      constructor
      · intro h; exact h i rfl
      · intro h i' hi'; rw [hι hi']; exact h
    have hFo : ∀ a ∉ Finset.univ.image ι, F a = (Ω a).card := by
      intro a ha
      simp only [hF]
      congr 2
      apply Finset.filter_true_of_mem
      intro c _ i hi
      exact absurd (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩) ha
    rw [← Finset.prod_mul_prod_compl (Finset.univ.image ι) F,
      ← Finset.prod_mul_prod_compl (Finset.univ.image ι) (fun a => ((Ω a).card : ℝ)),
      Finset.prod_image (fun i _ j _ h => hι h), Finset.prod_image (fun i _ j _ h => hι h)]
    rw [Finset.prod_congr rfl (fun a ha => hFo a (Finset.mem_compl.1 ha))]
    rw [Finset.prod_congr rfl (fun i _ => hFi i)]
    have : ∀ i, (w i (s i) : ℝ) = ρ i (s i) * (Ω (ι i)).card := by
      intro i; simp only [hρ]; field_simp [(htot i).ne']
    rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_mul_distrib]
    ring
  -- total count
  have hsplit : ((((Fintype.piFinset Ω).filter
        (fun C => ¬ PerfectMatching (fun i => g i (C (ι i))))).card : ℕ) : ℝ) =
      ∑ s : Fin M → Finset (Fin M), (if PerfectMatching s then 0 else
        ((((Fintype.piFinset Ω).filter (fun C => (fun i => g i (C (ι i))) = s)).card : ℕ) : ℝ)) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun C => fun i => g i (C (ι i)))
      (t := Finset.univ.filter fun s => ¬ PerfectMatching s)]
    · push_cast
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs with hs
      · rfl
      · congr 2; ext C; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hC, -⟩, h⟩; exact ⟨hC, h⟩
        · rintro ⟨hC, rfl⟩; exact ⟨⟨hC, hs⟩, rfl⟩
    · intro C hC
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
      exact hC.2
  rw [hsplit]
  calc ∑ s : Fin M → Finset (Fin M), (if PerfectMatching s then 0 else
        ((((Fintype.piFinset Ω).filter (fun C => (fun i => g i (C (ι i))) = s)).card : ℕ) : ℝ))
      = (∑ s : Fin M → Finset (Fin M), (if PerfectMatching s then 0 else ∏ i, ρ i (s i))) *
          (Fintype.piFinset Ω).card := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs
        · simp
        · exact hcount s
    _ ≤ 4 * (M : ℝ) ^ (-(11 : ℤ)) * (Fintype.piFinset Ω).card := by
        gcongr

/-- Lemma 4.4 (ii) for a relation restricted by independent random sets -/
theorem count_fail {α β δ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [DecidableEq δ] [Nonempty β] {A : Finset α} {B : Finset β} {M : ℕ} (hA : A.card = M)
    (hB : B.card = M) (hM : 2 ≤ M) (Rel : α → β → Prop) (dl dr : ℕ)
    (hl : ∀ b ∈ B, dl ≤ (A.filter fun a => Rel a b).card)
    (hr : ∀ a ∈ A, dr ≤ (B.filter fun b => Rel a b).card) (h5 : 5 * M ≤ 4 * (dl + dr))
    (φ : β → δ) (hφ : Set.InjOn φ (B : Set β)) (Ω : α → Finset (Finset δ))
    (hΩ : ∀ a, (Ω a).Nonempty) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hpM : 96 * Real.log M ≤ p * M)
    (hav : ∀ a ∈ A, ∀ Y : Finset δ, Y ⊆ (B.filter (Rel a)).image φ →
      ((((Ω a).filter (fun c => Disjoint c Y)).card : ℕ) : ℝ) ≤
        Real.exp (-p * Y.card) * (Ω a).card) :
    ((((Fintype.piFinset Ω).filter (fun C => ¬ ∃ g : α → β,
        (∀ a ∈ A, g a ∈ B ∧ (Rel a (g a) ∧ φ (g a) ∈ C a)) ∧ Set.InjOn g (A : Set α))).card
          : ℕ) : ℝ) ≤ 4 * (M : ℝ) ^ (-(11 : ℤ)) * (Fintype.piFinset Ω).card := by
  set eA := eqv A hA
  set eB := eqv B hB
  let ι : Fin M → α := fun i => (eA.symm i).1
  have hι : Function.Injective ι := fun i j h => eA.symm.injective (Subtype.ext h)
  let gf : Fin M → Finset δ → Finset (Fin M) := fun i c =>
    encN A B hA hB (fun a b => Rel a b ∧ φ b ∈ c) i
  have hsub : (Fintype.piFinset Ω).filter (fun C => ¬ ∃ g : α → β,
        (∀ a ∈ A, g a ∈ B ∧ (Rel a (g a) ∧ φ (g a) ∈ C a)) ∧ Set.InjOn g (A : Set α)) ⊆
      (Fintype.piFinset Ω).filter (fun C => ¬ PerfectMatching (fun i => gf i (C (ι i)))) := by
    intro C hC
    rw [Finset.mem_filter] at hC ⊢
    refine ⟨hC.1, fun hpm => hC.2 ?_⟩
    exact pm_att (A := A) (B := B) (hA := hA) (hB := hB)
      (Rel := fun a b => Rel a b ∧ φ b ∈ C a) hpm
  refine le_trans (Nat.cast_le.2 (Finset.card_le_card hsub)) ?_
  refine fail_count hM (encN A B hA hB Rel) (delta_enc hA hB Rel dl dr (by omega) hl hr h5)
    ι hι Ω hΩ gf ?_ p hp0 hp1 hpM ?_
  · intro i c l hl
    simp only [gf, encN, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    simp only [encN, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hl.1
  · intro i X hX
    set Y := X.image (fun l => φ (eB.symm l).1) with hY
    have hYsub : Y ⊆ (B.filter (Rel (ι i))).image φ := by
      intro y hy
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hy
      have := hX hl
      simp only [encN, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact Finset.mem_image_of_mem φ (Finset.mem_filter.2 ⟨(eB.symm l).2, this⟩)
    have hYcard : Y.card = X.card := by
      rw [hY, Finset.card_image_of_injOn]
      intro l _ l' _ h
      have := hφ (eB.symm l).2 (eB.symm l').2 h
      exact eB.symm.injective (Subtype.ext this)
    have hfil : (Ω (ι i)).filter (fun c => Disjoint (gf i c) X) =
        (Ω (ι i)).filter (fun c => Disjoint c Y) := by
      apply Finset.filter_congr
      intro c _
      rw [Finset.disjoint_left, Finset.disjoint_left]
      constructor
      · intro h y hyc hyY
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hyY
        have := hX hl
        simp only [encN, Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact h (by simp only [gf, encN, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨this, hyc⟩) hl
      · intro h l hl hlX
        simp only [gf, encN, Finset.mem_filter, Finset.mem_univ, true_and] at hl
        exact h hl.2 (Finset.mem_image_of_mem _ hlX)
    rw [hfil, ← hYcard]
    exact hav (ι i) (eA.symm i).2 Y hYsub

end Prob

end LowDiameterNashWilliams.Main.Dev.L43
end

section
/-! Lemma 4.3, part S: matchings after an exchange, and the sampled attachment points.

With the selections frozen (`FHyp`: both tests hold), after any exchange `(U, R')` every
active vertex `v` has `2r` available edges `Ev v` and `2r` selected trees `Jv v`; an edge `e`
may serve tree `j` iff `j ∉ Jv (head e)`. Degrees `≥ 2r - q` and `≥ r - q` give Lemma 4.4 (i).
Sampling `C_j` uniformly among the `min(b, |W_j|)`-subsets of `W_j = {x : j ∉ Jv x}` and
applying Lemma 4.4 (ii) (`count_fail`) shows that some sample has at most
`4 n (2r)^{-11}` failed vertices; the attachments use heads in `C_j` except at failed
vertices, so `|int V_j| ≤ |int T_j| + b + 4 n (2r)^{-11}` (`restore_all`). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L43
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33
  LowDiameterNashWilliams.Main.Dev.L41

variable {n m k : ℕ}

/-- the frozen selections satisfy both tests -/
structure FHyp (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (I J : Finset (Fin k))
    (Jv : Fin n → Finset (Fin k)) (r q : ℕ) : Prop where
  g : GHyp ends T I J Jv (fun v => pr r (Jv v))
  r1 : 1 ≤ r
  q4 : 4 * q ≤ r
  card : ∀ v, Jv v ≠ ∅ → (Jv v).card = 2 * r
  t1 : ∀ v x, Jv v ≠ ∅ → x ≠ v → (∃ e, ends e = s(v, x)) → (Jv v ∩ Jv x).card ≤ q
  t2 : ∀ v, ∀ j ∈ Jv v,
    ((Prot ends T (fun v => pr r (Jv v)) v).filter (fun e => j ∈ Jv (hd ends v e))).card ≤ q

section S

variable {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {I J : Finset (Fin k)}
  {Jv : Fin n → Finset (Fin k)} {r q : ℕ} {U : Trees k m} {R' : Fin n → Edges m}

local notation "PR" => (fun v => pr r (Jv v))

theorem prot_card (h : FHyp ends T I J Jv r q) {v : Fin n} (hv : Jv v ≠ ∅) :
    (Prot ends T PR v).card = r := by
  unfold Prot
  rw [card_LE h.g.part (fun j hj => h.g.leaf v j (h.g.prsub v hj))]
  exact pr_card (by rw [h.card v hv]; omega)

theorem res_card (h : FHyp ends T I J Jv r q) {v : Fin n} (hv : Jv v ≠ ∅) :
    (Res ends T Jv PR v).card = r := by
  unfold Res
  rw [card_LE h.g.part (fun j hj => h.g.leaf v j (Finset.sdiff_subset hj)),
    Finset.card_sdiff_of_subset (h.g.prsub v), pr_card (by rw [h.card v hv]; omega), h.card v hv]
  omega

theorem res_empty (h : FHyp ends T I J Jv r q) {v : Fin n} (hv : Jv v = ∅) :
    Res ends T Jv PR v = ∅ := by
  unfold Res LE; rw [hv]; simp

theorem prot_empty (h : FHyp ends T I J Jv r q) {v : Fin n} (hv : Jv v = ∅) :
    Prot ends T PR v = ∅ := by
  unfold Prot LE
  have : pr r (Jv v) = ∅ := Finset.subset_empty.1 (hv ▸ pr_sub r (Jv v))
  simp [this]

variable (hX : ExchangePartition ends I U R' (Pset ends T I Jv (fun v => pr r (Jv v))))
  (hR' : ∀ v, (R' v).card = (Res ends T Jv (fun v => pr r (Jv v)) v).card)

include hX in
theorem Ev_mem (h : FHyp ends T I J Jv r q) {v : Fin n} {e : Fin m}
    (he : e ∈ Ev ends T PR R' v) : v ∈ ends e := by
  rcases Finset.mem_union.1 he with he | he
  · obtain ⟨_, _, _, h⟩ := mem_LE.1 he; exact h
  · exact hX.2.2.1.1 v e he

include hX hR' in
theorem Ev_card (h : FHyp ends T I J Jv r q) {v : Fin n} (hv : Jv v ≠ ∅) :
    (Ev ends T PR R' v).card = 2 * r := by
  unfold Ev
  rw [Finset.card_union_of_disjoint, prot_card h hv, hR' v, res_card h hv]
  · ring
  · rw [Finset.disjoint_left]
    intro e he he'
    exact prot_not_P h.g he (R'_sub_P hX v he')

include hX hR' in
theorem Ev_empty (h : FHyp ends T I J Jv r q) {v : Fin n} (hv : Jv v = ∅) :
    Ev ends T PR R' v = ∅ := by
  unfold Ev
  rw [prot_empty h hv, Finset.empty_union]
  exact Finset.card_eq_zero.1 (by rw [hR' v, res_empty h hv]; rfl)

include hX in
theorem deg_left (h : FHyp ends T I J Jv r q) {v : Fin n} (hv : Jv v ≠ ∅) {e : Fin m}
    (he : e ∈ Ev ends T PR R' v) :
    2 * r - q ≤ ((Jv v).filter fun j => j ∉ Jv (hd ends v e)).card := by
  have hve := Ev_mem hX h he
  have h1 := h.t1 v (hd ends v e) hv (hd_ne h.g.simple hve) ⟨e, hd_spec hve⟩
  rw [Finset.filter_notMem_eq_sdiff, Finset.card_sdiff, h.card v hv, Finset.inter_comm]
  omega

theorem deg_right (h : FHyp ends T I J Jv r q) {v : Fin n} (hv : Jv v ≠ ∅) {j : Fin k}
    (hj : j ∈ Jv v) :
    r - q ≤ ((Ev ends T PR R' v).filter fun e => j ∉ Jv (hd ends v e)).card := by
  have h1 := h.t2 v j hj
  have h2 := Finset.card_filter_add_card_filter_not (s := Prot ends T PR v)
    (p := fun e => j ∈ Jv (hd ends v e))
  rw [prot_card h hv] at h2
  have h3 : ((Prot ends T PR v).filter fun e => j ∉ Jv (hd ends v e)) ⊆
      ((Ev ends T PR R' v).filter fun e => j ∉ Jv (hd ends v e)) :=
    Finset.filter_subset_filter _ Finset.subset_union_left
  have := Finset.card_le_card h3
  omega

/-! ### Sampling -/

/-- vertices kept in tree `j` -/
noncomputable def Wj (Jv : Fin n → Finset (Fin k)) (j : Fin k) : Finset (Fin n) :=
  Finset.univ.filter fun x => j ∉ Jv x

/-- the sample space of `C_j` -/
noncomputable def Om2 (Jv : Fin n → Finset (Fin k)) (b : ℕ) (j : Fin k) :
    Finset (Finset (Fin n)) :=
  (Wj Jv j).powersetCard (min b (Wj Jv j).card)

theorem Om2_nonempty (b : ℕ) (j : Fin k) : (Om2 Jv b j).Nonempty :=
  Finset.powersetCard_nonempty.2 (min_le_right _ _)

theorem avoid_bound {b : ℕ} (hb : b ≤ n) (j : Fin k) (Y : Finset (Fin n))
    (hY : Y ⊆ Wj Jv j) :
    ((((Om2 Jv b j).filter (fun c => Disjoint c Y)).card : ℕ) : ℝ) ≤
      Real.exp (-((b : ℝ) / n) * Y.card) * (Om2 Jv b j).card := by
  refine (card_avoid_le _ Y hY _).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [Real.exp_le_exp]
  -- `min(b, |W|) / |W| ≥ b / n`
  rcases Nat.eq_zero_or_pos (Wj Jv j).card with h0 | hpos
  · have : Y.card = 0 := by have := Finset.card_le_card hY; omega
    rw [this]; simp
  have hWn : (Wj Jv j).card ≤ n := by
    have := Finset.card_le_univ (Wj Jv j); simpa using this
  have hWr : (0 : ℝ) < (Wj Jv j).card := by exact_mod_cast hpos
  have hnr : (0 : ℝ) < n := by
    have : 0 < n := lt_of_lt_of_le hpos hWn
    exact_mod_cast this
  have key : (b : ℝ) / n ≤ ((min b (Wj Jv j).card : ℕ) : ℝ) / (Wj Jv j).card := by
    rcases le_total b (Wj Jv j).card with hle | hle
    · rw [min_eq_left hle]
      exact div_le_div_of_nonneg_left (by positivity) hWr (by exact_mod_cast hWn)
    · rw [min_eq_right hle, div_self hWr.ne', div_le_one hnr]
      exact_mod_cast hb
  have hY0 : (0 : ℝ) ≤ Y.card := by positivity
  calc -((b : ℝ) / n) * Y.card = -(((b : ℝ) / n) * Y.card) := by ring
    _ ≥ -((((min b (Wj Jv j).card : ℕ) : ℝ) / (Wj Jv j).card) * Y.card) := by
        apply neg_le_neg; exact mul_le_mul_of_nonneg_right key hY0
    _ = -((min b (Wj Jv j).card : ℕ) : ℝ) * Y.card / (Wj Jv j).card := by ring

/-- `g` attaches `v` inside `C` -/
def Good (ends : Fin m → Sym2 (Fin n)) (Jv : Fin n → Finset (Fin k)) (Ev : Edges m)
    (v : Fin n) (C : Fin k → Finset (Fin n)) (g : Fin k → Fin m) : Prop :=
  (∀ j ∈ Jv v, g j ∈ Ev ∧ (j ∉ Jv (hd ends v (g j)) ∧ hd ends v (g j) ∈ C j)) ∧
    Set.InjOn g (Jv v : Set (Fin k))

/-- the failed vertices of a sample -/
noncomputable def Fail (ends : Fin m → Sym2 (Fin n)) (Jv : Fin n → Finset (Fin k))
    (Ev : Fin n → Edges m) (C : Fin k → Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => Jv v ≠ ∅ ∧ ¬ ∃ g, Good ends Jv (Ev v) v C g

include hX hR' in
theorem fail_v (h : FHyp ends T I J Jv r q) {b : ℕ} (hb1 : 1 ≤ b) (hbn : b ≤ n)
    (hpM : 96 * Real.log ((2 * r : ℕ) : ℝ) ≤ (b : ℝ) / n * ((2 * r : ℕ) : ℝ)) (v : Fin n) :
    ((((Fintype.piFinset (Om2 Jv b)).filter (fun C =>
        Jv v ≠ ∅ ∧ ¬ ∃ g, Good ends Jv (Ev ends T PR R' v) v C g)).card : ℕ) : ℝ) ≤
      4 * ((2 * r : ℕ) : ℝ) ^ (-(11 : ℤ)) * (Fintype.piFinset (Om2 Jv b)).card := by
  by_cases hv : Jv v = ∅
  · have : (Fintype.piFinset (Om2 Jv b)).filter (fun C =>
        Jv v ≠ ∅ ∧ ¬ ∃ g, Good ends Jv (Ev ends T PR R' v) v C g) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro C _ hC; exact hC.1 hv
    rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  have hEc := Ev_card hX hR' h hv
  obtain ⟨e0, he0⟩ : (Ev ends T PR R' v).Nonempty := by
    rw [← Finset.card_pos, hEc]; have := h.r1; omega
  have : Nonempty (Fin m) := ⟨e0⟩
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hcf := count_fail (A := Jv v) (B := Ev ends T PR R' v) (M := 2 * r) (h.card v hv) hEc
    (by have := h.r1; omega) (fun j e => j ∉ Jv (hd ends v e)) (2 * r - q) (r - q)
    (fun e he => by convert deg_left hX h hv he using 2; congr)
    (fun j hj => by convert deg_right (R' := R') h hv hj using 2; congr)
    (by have := h.q4; omega) (hd ends v)
    (hd_injOn h.g.simple _ (fun e he => Ev_mem hX h he)) (Om2 Jv b) (Om2_nonempty b)
    ((b : ℝ) / n) (by have : (0 : ℝ) < b := by exact_mod_cast hb1
                      positivity)
    (by rw [div_le_one hnpos]; exact_mod_cast hbn) hpM
    (fun j _ Y hY => by
      refine avoid_bound hbn j Y ?_
      intro y hy
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 (hY hy)
      simp only [Wj, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Finset.filter_congr_decidable] at he
      exact (Finset.mem_filter.1 he).2)
  convert hcf using 3
  ext C
  simp only [Finset.mem_filter, ne_eq, hv, not_false_eq_true, true_and, Good]

include hX hR' in
/-- a sample with few failed vertices -/
theorem good_sample (h : FHyp ends T I J Jv r q) {b : ℕ} (hb1 : 1 ≤ b) (hbn : b ≤ n)
    (hpM : 96 * Real.log ((2 * r : ℕ) : ℝ) ≤ (b : ℝ) / n * ((2 * r : ℕ) : ℝ)) :
    ∃ C ∈ Fintype.piFinset (Om2 Jv b),
      ((Fail ends Jv (Ev ends T PR R') C).card : ℝ) ≤ n * (4 * ((2 * r : ℕ) : ℝ) ^ (-(11 : ℤ))) := by
  have hne : (Fintype.piFinset (Om2 Jv b)).Nonempty :=
    Fintype.piFinset_nonempty.2 (fun j => Om2_nonempty b j)
  refine exists_le_avg _ hne _ _ ?_
  have hF : ∀ C, ((Fail ends Jv (Ev ends T PR R') C).card : ℝ) = ∑ v : Fin n,
      (if Jv v ≠ ∅ ∧ ¬ ∃ g, Good ends Jv (Ev ends T PR R' v) v C g then (1 : ℝ) else 0) := by
    intro C; unfold Fail; rw [Finset.card_filter]; push_cast; rfl
  simp only [hF]
  rw [Finset.sum_comm]
  calc ∑ v : Fin n, ∑ C ∈ Fintype.piFinset (Om2 Jv b),
        (if Jv v ≠ ∅ ∧ ¬ ∃ g, Good ends Jv (Ev ends T PR R' v) v C g then (1 : ℝ) else 0)
      ≤ ∑ _v : Fin n, 4 * ((2 * r : ℕ) : ℝ) ^ (-(11 : ℤ)) * (Fintype.piFinset (Om2 Jv b)).card :=
        Finset.sum_le_sum fun v _ => by
          rw [Finset.sum_boole]; exact fail_v hX hR' h hb1 hbn hpM v
    _ = _ := by simp; ring

include hX hR' in
theorem exists_att (h : FHyp ends T I J Jv r q) (hm : 0 < m) {b : ℕ} (C : Fin k → Finset (Fin n))
    (hC : C ∈ Fintype.piFinset (Om2 Jv b)) (v : Fin n) :
    ∃ g : Fin k → Fin m, (∀ j ∈ Jv v, g j ∈ Ev ends T PR R' v ∧ j ∉ Jv (hd ends v (g j))) ∧
      Set.InjOn g (Jv v : Set (Fin k)) ∧
      (v ∉ Fail ends Jv (Ev ends T PR R') C → ∀ j ∈ Jv v, hd ends v (g j) ∈ C j) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  by_cases hv : Jv v = ∅
  · refine ⟨fun _ => ⟨0, hm⟩, ?_, ?_, ?_⟩ <;> simp [hv]
  by_cases hf : v ∈ Fail ends Jv (Ev ends T PR R') C
  · have hEc := Ev_card hX hR' h hv
    obtain ⟨g, hg1, hg2⟩ := pm_exists (h.card v hv) hEc (by have := h.r1; omega)
      (fun j e => j ∉ Jv (hd ends v e)) (2 * r - q) (r - q)
      (fun e he => by convert deg_left hX h hv he using 2; congr)
      (fun j hj => by convert deg_right (R' := R') h hv hj using 2; congr)
      (by have := h.q4; omega)
    exact ⟨g, hg1, hg2, fun h' => absurd hf h'⟩
  · have : ∃ g, Good ends Jv (Ev ends T PR R' v) v C g := by
      by_contra hc
      exact hf (Finset.mem_filter.2 ⟨Finset.mem_univ _, hv, hc⟩)
    obtain ⟨g, hg1, hg2⟩ := this
    exact ⟨g, fun j hj => ⟨(hg1 j hj).1, (hg1 j hj).2.1⟩, hg2, fun _ j hj => (hg1 j hj).2.2⟩

include hX hR' in
/-- restoration after an arbitrary exchange -/
theorem restore_all (h : FHyp ends T I J Jv r q) (hm : 0 < m) {b : ℕ} (hb1 : 1 ≤ b)
    (hbn : b ≤ n)
    (hpM : 96 * Real.log ((2 * r : ℕ) : ℝ) ≤ (b : ℝ) / n * ((2 * r : ℕ) : ℝ)) :
    ∃ V : Trees k m, TreePartition ends V ∧ (∀ i ∈ I, V i = U i) ∧
      ∀ j ∈ J, diameter ends (V j) ≤ diameter ends (T j) + 2 ∧
        ((internal ends (V j)).card : ℝ) ≤ (internal ends (T j)).card + b +
          n * (4 * ((2 * r : ℕ) : ℝ) ^ (-(11 : ℤ))) := by
  obtain ⟨C, hC, hFail⟩ := good_sample hX hR' h hb1 hbn hpM
  let att : Fin n → Fin k → Fin m := fun v => Classical.choose (exists_att hX hR' h hm C hC v)
  have hatt : ∀ v, (∀ j ∈ Jv v, att v j ∈ Ev ends T PR R' v ∧ j ∉ Jv (hd ends v (att v j))) ∧
      Set.InjOn (att v) (Jv v : Set (Fin k)) ∧
      (v ∉ Fail ends Jv (Ev ends T PR R') C → ∀ j ∈ Jv v, hd ends v (att v j) ∈ C j) :=
    fun v => Classical.choose_spec (exists_att hX hR' h hm C hC v)
  have ha : AttHyp (ends := ends) (T := T) (Jv := Jv) (pr := PR) (R' := R') att := by
    refine ⟨fun v j hj => ((hatt v).1 j hj).1, fun v => (hatt v).2.1, fun v => ?_,
      fun v j hj => ⟨hd ends v (att v j), ((hatt v).1 j hj).2,
        hd_spec (Ev_mem hX h ((hatt v).1 j hj).1)⟩⟩
    by_cases hv : Jv v = ∅
    · rw [Ev_empty hX hR' h hv]; exact Finset.empty_subset _
    have hsub : (Jv v).image (att v) ⊆ Ev ends T PR R' v := by
      intro e he
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 he
      exact ((hatt v).1 j hj).1
    have hcard : (Ev ends T PR R' v).card ≤ ((Jv v).image (att v)).card := by
      rw [Finset.card_image_of_injOn (hatt v).2.1, Ev_card hX hR' h hv, h.card v hv]
    rw [Finset.eq_of_subset_of_card_le hsub hcard]
  obtain ⟨hV1, hV2, hV3⟩ := restore h.g hX ha
  refine ⟨Vfam ends T I Jv U att, hV1, hV2, fun j hj => ⟨(hV3 j hj).1, ?_⟩⟩
  -- the internal vertices
  have hsub : internal ends (Vfam ends T I Jv U att j) ⊆ internal ends (T j) ∪
      (C j ∪ (Fail ends Jv (Ev ends T PR R') C).image (fun v => hd ends v (att v j))) := by
    intro x hx
    rcases (hV3 j hj).2 x hx with h1 | ⟨v, hjv, hxv, hxe⟩
    · exact Finset.mem_union_left _ h1
    · have hve := Ev_mem hX h ((hatt v).1 j hjv).1
      have hxh : x = hd ends v (att v j) := by
        rw [hd_spec hve, Sym2.mem_iff] at hxe
        rcases hxe with h' | h'
        · exact absurd h' hxv
        · exact h'
      by_cases hf : v ∈ Fail ends Jv (Ev ends T PR R') C
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_image.2 ⟨v, hf, hxh.symm⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (hxh ▸ (hatt v).2.2 hf j hjv))
  have hCj : (C j).card ≤ b := by
    have := (Fintype.mem_piFinset.1 hC) j
    rw [Om2, Finset.mem_powersetCard] at this
    rw [this.2]; exact min_le_left _ _
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (internal ends (T j))
    (C j ∪ (Fail ends Jv (Ev ends T PR R') C).image (fun v => hd ends v (att v j)))
  have h3 := Finset.card_union_le (C j)
    ((Fail ends Jv (Ev ends T PR R') C).image (fun v => hd ends v (att v j)))
  have h4 := Finset.card_image_le (s := Fail ends Jv (Ev ends T PR R') C)
    (f := fun v => hd ends v (att v j))
  have : ((internal ends (Vfam ends T I Jv U att j)).card : ℝ) ≤
      (internal ends (T j)).card + b + (Fail ends Jv (Ev ends T PR R') C).card := by
    have : (internal ends (Vfam ends T I Jv U att j)).card ≤
        (internal ends (T j)).card + b + (Fail ends Jv (Ev ends T PR R') C).card := by omega
    exact_mod_cast this
  linarith

end S

end LowDiameterNashWilliams.Main.Dev.L43
end

section
/-!
# Lemma 4.3 (restoring the supplying trees): the argument with explicit constants

Notation: `r = ⌊k/8192⌋`, `q = ⌊r/4⌋`, `h = q + 1`, `L_v = {j ∈ J : deg_{T_j} v = 1}`.
Constants: `C = 786434 = 48·16384 + 2`; `K` is large enough that `r ≥ 2`, `k ≥ 16384`,
`3 k² (e/4)^h ≤ 1`, `48 log(2r) ≤ r`, `4 k ≤ (2r)^11` (all hold eventually in `k`).

**0. Preliminaries.** A tree partition of a simple graph has `m = k(n-1) ≤ n(n-1)/2`, so
`n ≥ 2k ≥ 3`. In a spanning tree on `n ≥ 3` vertices no two leaves are adjacent.
For `v ∉ S`, `|L_v| ≥ k/128 ≥ 2r` and `2r/|L_v| ≤ (k/4096)/(k/128) = 1/32`.

**1. Choice of the selections (averaging, module L43R; counting tools in L43P).** Sample space
`Ω = ∏_v A_v`, `A_v = {∅}` for `v ∈ S`, `A_v = (2r)-subsets of L_v` otherwise.
For `a ∈ A_v` let `pr a ⊆ a` be a fixed `r`-subset, `Prot(v,a)` the leaf edges of `v` in the
trees `pr a`, `P(v,a)` their other ends (`|P(v,a)| = r` by simplicity).
Tests at `v ∉ S`: (t1) `|ω_v ∩ ω_x| ≤ q` for every neighbour `x` of `v`;
(t2) `|{x ∈ P(v,ω_v) : j ∈ ω_x}| ≤ q` for every `j ∈ ω_v`. `Z(ω)` = vertices failing a test.
Counting lemma: for `a ∈ A_v`, `v ∉ Y`, predicates with `|{b ∈ A_y : p_y b}| ≤ c_y |A_y|`,
`#{ω : ω_v = a ∧ ∀ y ∈ Y, p_y ω_y} · |A_v| ≤ (∏_Y c_y) |Ω|`.
Uniform subsets: `#{a ∈ (s-subsets of L) : Q ⊆ a} ≤ (s/|L|)^{|Q|} C(|L|,s)`, so
`Pr[Q ⊆ ω_x] ≤ 32^{-|Q|}` (and `= 0` for `x ∈ S`).
A failure of (t1) at `(v,x)` is witnessed by `a = ω_v` and an `h`-subset `Q ⊆ a` with
`Q ⊆ ω_x`; of (t2) by `a = ω_v`, `j ∈ a`, an `h`-subset `Q ⊆ P(v,a)` with `j ∈ ω_y` (y ∈ Q).
Hence `Σ_ω |Z(ω)| ≤ |Ω| 32^{-h} (Σ_v deg v · C(2r,h) + n · 2r · C(r,h))
  ≤ |Ω| · 3kn · C(2r,h) 32^{-h} ≤ |Ω| · 3kn (e/4)^h ≤ |Ω| n/k`,
using `Σ deg ≤ 2m ≤ 2kn`, `2r ≤ k`, `C(2r,h) ≤ (2re/h)^h ≤ (8e)^h` (as `2r < 8h`).
Pick `ω` with `|Z| ≤ n/k`; `H = S ∪ Z`; `J_v = ω_v` off `H`, `∅` on `H`;
`R_v` = leaf edges of `v` in the trees `J_v \ pr J_v` (size `r`); `Prot_v` = those of `pr J_v`.
Shrinking `J_x` to `∅` on `H` keeps both tests. Reserves are owner-disjoint (no adjacent leaves).

**2. Matching (modules L43M: Lemma 4.4 interface; L43S: application).** After a repartition `(U, R')`, for `v` with `J_v ≠ ∅` let
`E_v = Prot_v ∪ R'_v` (`2r` edges at `v`, distinct heads by simplicity). Bipartite graph
`B_v` between `E_v` and `J_v`: `e ~ j` iff `j ∉ J_{head e}`. Degrees: an edge has
`≥ 2r - q`, an index has `≥ r - q` (protected heads), sum `≥ 3r - 2q ≥ (5/4)(2r)`.
`lemma_4_4 (i)` gives a perfect matching. Sampling: for `j` let `W_j = {x : j ∉ J_x}`
(vertex set of `T_j⁻`) and `C_j` a uniform `min(b,|W_j|)`-subset of `W_j`,
`b = ⌈48 n log(2r) / r⌉ ≤ n`, `p = b/n`; `Pr[C_j ∩ X = ∅] ≤ (1 - |X|/|W_j|)^b ≤ e^{-p|X|}`
and `p·2r ≥ 96 log(2r)`. `lemma_4_4 (ii)` (via the pushforward PMFs) gives
`Pr[restricted B_v has no perfect matching] ≤ 4(2r)^{-11}`; averaging over the `C`'s gives a
sample with at most `4n(2r)^{-11} ≤ n/k` failed vertices; failed vertices use an unrestricted
matching.

**3. Restoration (modules L43T: one tree; L43D: the partition; deterministic).** `T_j⁻ = T_j` minus the leaf edges of the
deleted vertices `D_j = {v : j ∈ J_v}`; `V_j = T_j⁻ ∪ {att(v,j) : v ∈ D_j}`. A walk in
`T_j` between vertices of `W_j` can be shortened to a walk in `T_j⁻` (a deleted vertex is a
leaf, entered and left through its unique neighbour), so distances in `T_j⁻` are at most
those in `T_j`; `V_j` is connected with `n - 1` edges, hence a spanning tree; every vertex is
within one edge of `W_j`, so `diam V_j ≤ diam T_j + 2`; `int V_j ⊆ int T_j ∪ heads_j` and
`heads_j ⊆ C_j ∪ (heads of failed vertices)`, so
`|int V_j| ≤ |int T_j| + b + n/k ≤ |int T_j| + 786434 (n/k) log k`
(`b ≤ 48·16384 (n/k) log k + 1`, `1 ≤ n/k ≤ (n/k) log k`).
The families `V_i = U_i` (`i ∈ I`), `V_j` (`j ∈ J`) partition `E(G)`.
-/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L43
open LowDiameterNashWilliams.Main LowDiameterNashWilliams.Main.Dev.L33
  LowDiameterNashWilliams.Main.Dev.L41

/-! ### Numerics -/

theorem eventually_small : ∃ H0 : ℕ, ∀ h : ℕ, H0 ≤ h →
    3 * (32768 : ℝ) ^ 2 * ((h : ℝ) ^ 2 * (Real.exp 1 / 4) ^ h) ≤ 1 := by
  have hρ : |Real.exp 1 / 4| < 1 := by
    rw [abs_of_pos (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hρ
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (3 * (32768 : ℝ) ^ 2) by positivity))
  obtain ⟨H0, hH0⟩ := Filter.eventually_atTop.1 hev
  refine ⟨H0, fun h hh => ?_⟩
  have := hH0 h hh
  rw [lt_div_iff₀ (by positivity)] at this
  linarith

theorem log_le_of_large {r : ℕ} (hr : 9216 ≤ r) : 48 * Real.log (2 * r) ≤ r := by
  have hr0 : (0 : ℝ) < r := by have : 0 < r := by omega
                               exact_mod_cast this
  have hx : (0 : ℝ) ≤ (r : ℝ) / 48 := by positivity
  have h2 := Real.pow_div_factorial_le_exp (x := (r : ℝ) / 48) hx 2
  have hr' : (9216 : ℝ) ≤ r := by exact_mod_cast hr
  have hexp : 2 * (r : ℝ) ≤ Real.exp ((r : ℝ) / 48) := by
    refine le_trans ?_ h2
    simp only [Nat.factorial, Nat.succ_eq_add_one, Nat.cast_ofNat]
    norm_num
    nlinarith
  have := (Real.log_le_log (by positivity) hexp)
  rw [Real.log_exp] at this
  linarith

theorem choose_pow_le {r h : ℕ} (hh : 0 < h) (h2r : 2 * r ≤ 8 * h) :
    ((2 * r).choose h : ℝ) * (1 / 32 : ℝ) ^ h ≤ (Real.exp 1 / 4) ^ h := by
  have h1 := choose_le_exp (2 * r) h hh
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have h3 : ((2 * r : ℕ) : ℝ) * Real.exp 1 / h ≤ 8 * Real.exp 1 := by
    rw [div_le_iff₀ hhr]
    have : ((2 * r : ℕ) : ℝ) ≤ 8 * h := by exact_mod_cast h2r
    have he := Real.exp_pos 1
    nlinarith
  calc ((2 * r).choose h : ℝ) * (1 / 32 : ℝ) ^ h
      ≤ (((2 * r : ℕ) : ℝ) * Real.exp 1 / h) ^ h * (1 / 32 : ℝ) ^ h := by gcongr
    _ ≤ (8 * Real.exp 1) ^ h * (1 / 32 : ℝ) ^ h := by gcongr
    _ = (Real.exp 1 / 4) ^ h := by rw [← mul_pow]; congr 1; ring

/-! ### Counting edges -/

theorem m_eq {n m k : ℕ} {ends : Fin m → Sym2 (Fin n)} {T : Trees k m}
    (hT : TreePartition ends T) : m = k * (n - 1) := by
  have h1 : (Finset.univ.biUnion T).card = m := by rw [hT.2]; simp
  rw [Finset.card_biUnion (fun i _ j _ hij => hT.1.2 i j hij)] at h1
  have h2 : ∀ i, (T i).card = n - 1 := fun i => by
    have := tree_card ends (hT.1.1 i); omega
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  exact h1.symm

theorem m_le_choose {n m : ℕ} {ends : Fin m → Sym2 (Fin n)} (hs : Simple ends) :
    m ≤ n.choose 2 := by
  have := Fintype.card_le_of_injective
    (fun e => (⟨ends e, hs.2 e⟩ : {a : Sym2 (Fin n) // ¬ a.IsDiag}))
    (fun e e' h => hs.1 (congrArg Subtype.val h))
  rw [Sym2.card_subtype_not_diag, Fintype.card_fin, Fintype.card_fin] at this
  exact this

theorem two_k_le {n m k : ℕ} {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} (hn : 2 ≤ n)
    (hs : Simple ends) (hT : TreePartition ends T) : 2 * k ≤ n := by
  have h1 := m_eq hT
  have h2 := m_le_choose hs
  rw [Nat.choose_two_right] at h2
  have h3 : k * (n - 1) * 2 ≤ n * (n - 1) := by
    rw [h1] at h2
    have := Nat.div_mul_le_self (n * (n - 1)) 2
    omega
  have h4 : 0 < n - 1 := by omega
  have : 2 * k * (n - 1) ≤ n * (n - 1) := by nlinarith
  exact Nat.le_of_mul_le_mul_right this h4

/-! ### The three numerical steps of the assembly -/

theorem Zarith {n m k r q H0 : ℕ}
    (hH0 : ∀ h : ℕ, H0 ≤ h → 3 * (32768 : ℝ) ^ 2 * ((h : ℝ) ^ 2 * (Real.exp 1 / 4) ^ h) ≤ 1)
    (hq : H0 ≤ q + 1) (hkq : k ≤ 32768 * (q + 1)) (h2r8 : 2 * r ≤ 8 * (q + 1))
    (h2rk : 2 * r ≤ k) (hmk : m ≤ k * n) (hk : 0 < k) (z : ℝ)
    (hZ : z ≤ (2 * m : ℝ) * (((2 * r).choose (q + 1) : ℝ) * (1 / 32 : ℝ) ^ (q + 1)) +
          n * (((2 * r : ℕ) : ℝ) * (r.choose (q + 1) : ℝ) * (1 / 32 : ℝ) ^ (q + 1))) :
    z ≤ n / k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set X : ℝ := ((2 * r).choose (q + 1) : ℝ) * (1 / 32 : ℝ) ^ (q + 1) with hX
  have hX0 : 0 ≤ X := by positivity
  have hXe : X ≤ (Real.exp 1 / 4) ^ (q + 1) := choose_pow_le (by omega) h2r8
  have hC2 : ((2 * r : ℕ) : ℝ) * (r.choose (q + 1) : ℝ) * (1 / 32 : ℝ) ^ (q + 1) ≤ k * X := by
    have h1 : (r.choose (q + 1) : ℝ) ≤ ((2 * r).choose (q + 1) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose _ (by omega)
    have h2 : ((2 * r : ℕ) : ℝ) ≤ k := by exact_mod_cast h2rk
    rw [hX, ← mul_assoc]
    have : (0 : ℝ) ≤ (1 / 32 : ℝ) ^ (q + 1) := by positivity
    have : (0 : ℝ) ≤ (r.choose (q + 1) : ℝ) := by positivity
    gcongr
  have hmk' : (m : ℝ) ≤ k * n := by exact_mod_cast hmk
  have hsum : z ≤ 3 * k * n * X := by
    refine hZ.trans ?_
    have h1 : (2 * m : ℝ) * X ≤ 2 * (k * n) * X := by gcongr
    have h2 : (n : ℝ) * (((2 * r : ℕ) : ℝ) * (r.choose (q + 1) : ℝ) * (1 / 32 : ℝ) ^ (q + 1))
        ≤ n * (k * X) := by gcongr
    nlinarith
  have hkh : (k : ℝ) ≤ 32768 * ((q + 1 : ℕ) : ℝ) := by exact_mod_cast hkq
  have hsmall := hH0 (q + 1) hq
  have hk2 : (k : ℝ) ^ 2 ≤ (32768 : ℝ) ^ 2 * ((q + 1 : ℕ) : ℝ) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hkpos.le hkh 2
  have he0 : (0 : ℝ) ≤ (Real.exp 1 / 4) ^ (q + 1) := by positivity
  have h3 : 3 * (k : ℝ) ^ 2 * X ≤ 1 := by
    calc 3 * (k : ℝ) ^ 2 * X ≤ 3 * ((32768 : ℝ) ^ 2 * ((q + 1 : ℕ) : ℝ) ^ 2) *
          (Real.exp 1 / 4) ^ (q + 1) := by gcongr
      _ = 3 * (32768 : ℝ) ^ 2 * (((q + 1 : ℕ) : ℝ) ^ 2 * (Real.exp 1 / 4) ^ (q + 1)) := by ring
      _ ≤ 1 := hsmall
  have hz0 : z * k ≤ 3 * k * n * X * k := by
    exact mul_le_mul_of_nonneg_right hsum hkpos.le
  rw [le_div_iff₀ hkpos]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  calc z * k ≤ 3 * k * n * X * k := hz0
    _ = n * (3 * (k : ℝ) ^ 2 * X) := by ring
    _ ≤ n * 1 := by gcongr
    _ = n := mul_one _

theorem b_exists {n r : ℕ} (hn : 1 ≤ n) (hr : 9216 ≤ r) :
    ∃ b : ℕ, 1 ≤ b ∧ b ≤ n ∧
      96 * Real.log ((2 * r : ℕ) : ℝ) ≤ (b : ℝ) / n * ((2 * r : ℕ) : ℝ) ∧
      (b : ℝ) < 48 * (n : ℝ) * Real.log ((2 * r : ℕ) : ℝ) / r + 1 := by
  set L2 := Real.log ((2 * r : ℕ) : ℝ) with hL2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h2r : (2 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by
    have : 2 ≤ 2 * r := by omega
    exact_mod_cast this
  have hL2pos : 0 < L2 := Real.log_pos (by linarith)
  have hrpos : (0 : ℝ) < r := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hL2le : 48 * L2 ≤ r := by
    have := log_le_of_large hr
    rw [hL2]; push_cast; exact this
  refine ⟨⌈48 * (n : ℝ) * L2 / r⌉₊, ?_, ?_, ?_, Nat.ceil_lt_add_one (by positivity)⟩
  · refine Nat.one_le_iff_ne_zero.2 (fun h => ?_)
    have hbge : 48 * (n : ℝ) * L2 / r ≤ (⌈48 * (n : ℝ) * L2 / r⌉₊ : ℝ) := Nat.le_ceil _
    rw [h, Nat.cast_zero] at hbge
    have : 0 < 48 * (n : ℝ) * L2 / r := by positivity
    linarith
  · rw [Nat.ceil_le, div_le_iff₀ hrpos]
    nlinarith
  · have hbge : 48 * (n : ℝ) * L2 / r ≤ (⌈48 * (n : ℝ) * L2 / r⌉₊ : ℝ) := Nat.le_ceil _
    have h1 : 48 * L2 / r * ((2 * r : ℕ) : ℝ) = 96 * L2 := by
      push_cast; field_simp; ring
    have h2 : 48 * L2 / r ≤ (⌈48 * (n : ℝ) * L2 / r⌉₊ : ℝ) / n := by
      rw [le_div_iff₀ hnpos]
      calc 48 * L2 / r * n = 48 * (n : ℝ) * L2 / r := by ring
        _ ≤ _ := hbge
    calc 96 * L2 = 48 * L2 / r * ((2 * r : ℕ) : ℝ) := h1.symm
      _ ≤ (⌈48 * (n : ℝ) * L2 / r⌉₊ : ℝ) / n * ((2 * r : ℕ) : ℝ) := by gcongr

theorem tail_arith {n k r b : ℕ} (hk3 : 3 ≤ k) (h2k : 2 * k ≤ n) (hkr : k ≤ 16384 * r)
    (h2rk : 2 * r ≤ k) (hr2 : 2 ≤ r)
    (hblt : (b : ℝ) < 48 * (n : ℝ) * Real.log ((2 * r : ℕ) : ℝ) / r + 1) :
    (b : ℝ) + n * (4 * ((2 * r : ℕ) : ℝ) ^ (-(11 : ℤ))) ≤ 786434 * ((n : ℝ) / k * Real.log k) := by
  set L2 := Real.log ((2 * r : ℕ) : ℝ) with hL2
  have hkpos : (0 : ℝ) < k := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hrpos : (0 : ℝ) < r := by
    have : 0 < r := by omega
    exact_mod_cast this
  have h2r : (2 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by
    have : 2 ≤ 2 * r := by omega
    exact_mod_cast this
  have hk2r : ((2 * r : ℕ) : ℝ) ≤ k := by exact_mod_cast h2rk
  have hL2k : L2 ≤ Real.log k := Real.log_le_log (by linarith) hk2r
  have hlogk : 1 ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le hkpos]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    linarith
  have hk16 : (k : ℝ) ≤ 16384 * r := by exact_mod_cast hkr
  have hnk : 1 ≤ (n : ℝ) / k := by
    rw [le_div_iff₀ hkpos, one_mul]
    have : (2 * k : ℝ) ≤ n := by exact_mod_cast h2k
    linarith
  have hterm1 : 48 * (n : ℝ) * L2 / r ≤ 786432 * ((n : ℝ) / k * Real.log k) := by
    rw [div_le_iff₀ hrpos]
    have h1 : 48 * (n : ℝ) * L2 ≤ 48 * n * Real.log k := by gcongr
    have h3 : 1 ≤ 16384 * (r : ℝ) / k := by rw [le_div_iff₀ hkpos]; linarith
    have h4 : 0 ≤ 48 * ((n : ℝ) * Real.log k) := by positivity
    have h5 : 786432 * ((n : ℝ) / k * Real.log k) * r =
        48 * ((n : ℝ) * Real.log k) * (16384 * r / k) := by ring
    have h6 : 48 * ((n : ℝ) * Real.log k) * 1 ≤ 48 * ((n : ℝ) * Real.log k) * (16384 * r / k) :=
      mul_le_mul_of_nonneg_left h3 h4
    rw [h5]
    linarith
  have hpow : (4 : ℝ) * k ≤ ((2 * r : ℕ) : ℝ) ^ 11 := by
    have h1 : (4 : ℕ) ^ 10 ≤ (2 * r) ^ 10 := Nat.pow_le_pow_left (by omega) 10
    have h0 : (4 : ℕ) ^ 10 = 1048576 := by norm_num
    rw [h0] at h1
    have h2 : 4 * k ≤ (2 * r) ^ 10 * (2 * r) := by
      have : 4 * k ≤ 1048576 * (2 * r) := by omega
      exact this.trans (Nat.mul_le_mul_right _ h1)
    rw [← pow_succ] at h2
    exact_mod_cast h2
  have hterm2 : (n : ℝ) * (4 * ((2 * r : ℕ) : ℝ) ^ (-(11 : ℤ))) ≤ (n : ℝ) / k := by
    have hpos : (0 : ℝ) < ((2 * r : ℕ) : ℝ) ^ 11 := by positivity
    have hz : ((2 * r : ℕ) : ℝ) ^ (11 : ℤ) = ((2 * r : ℕ) : ℝ) ^ (11 : ℕ) := by norm_cast
    rw [zpow_neg, hz, div_eq_mul_one_div (n : ℝ) k]
    gcongr
    rw [← div_eq_mul_inv, div_le_div_iff₀ hpos hkpos, one_mul]
    linarith
  have hnl : (n : ℝ) / k ≤ (n : ℝ) / k * Real.log k :=
    le_mul_of_one_le_right (by positivity) hlogk
  linarith

end LowDiameterNashWilliams.Main.Dev.L43

namespace LowDiameterNashWilliams.Main
set_option maxRecDepth 100000 in
open LowDiameterNashWilliams.Main.Dev.L43 LowDiameterNashWilliams.Main.Dev.L33 in
theorem chk_lemma_4_3 :
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 2 ≤ K ∧ ∀ n m k : ℕ, 2 ≤ n → K ≤ k →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Trees k m)
    (I J : Finset (Fin k)) (S : Finset (Fin n)),
  Simple ends → TreePartition ends T → Disjoint I J → I ∪ J = Finset.univ →
  (∀ v, v ∉ S → (k : ℝ) / 128 ≤ leafCount ends T J v) →
  ∃ (H : Finset (Fin n)) (R : Fin n → Edges m),
    S ⊆ H ∧ ((H \ S).card : ℝ) ≤ (n : ℝ) / k ∧ OwnerReserves ends R ∧
    (∀ v, R v ⊆ J.biUnion T) ∧
    (∀ v, (v ∉ H → (R v).card = k / 8192) ∧ (v ∈ H → R v = ∅)) ∧
    ∀ (U : Trees k m) (R' : Fin n → Edges m),
      ExchangePartition ends I U R' (I.biUnion T ∪ Finset.univ.biUnion R) →
      (∀ v, (R' v).card = (R v).card) →
      ∃ V : Trees k m, TreePartition ends V ∧ (∀ i ∈ I, V i = U i) ∧
        ∀ j ∈ J, diameter ends (V j) ≤ diameter ends (T j) + 2 ∧
          ((internal ends (V j)).card : ℝ) ≤ (internal ends (T j)).card +
            C * ((n : ℝ) / k * Real.log k) := by
  obtain ⟨H0, hH0⟩ := eventually_small
  refine ⟨786434, by norm_num, 32768 * (H0 + 20000), by omega, ?_⟩
  intro n m k hn hk ends T I J S hs hT hIJ hcov hleaf
  -- the numbers
  set r := k / 8192 with hr
  set q := r / 4 with hq
  have hrk : r * 8192 ≤ k := Nat.div_mul_le_self k 8192
  have hkr : k < 8192 * (r + 1) := Nat.lt_mul_div_succ k (by norm_num)
  have hqr : q * 4 ≤ r := Nat.div_mul_le_self r 4
  have hrq : r < 4 * (q + 1) := Nat.lt_mul_div_succ r (by norm_num)
  have hr_big : 4 * (H0 + 20000) ≤ r := by omega
  have hq_big : H0 + 20000 ≤ q := by omega
  have h2k : 2 * k ≤ n := two_k_le hn hs hT
  have hn3 : 3 ≤ n := by omega
  have hmeq : m = k * (n - 1) := m_eq hT
  have hm : 0 < m := by rw [hmeq]; exact Nat.mul_pos (by omega) (by omega)
  have hkpos : (0 : ℝ) < k := by have : 0 < k := by omega
                                 exact_mod_cast this
  have hnpos : (0 : ℝ) < n := by have : 0 < n := by omega
                                 exact_mod_cast this
  -- leaf counts
  have hL : ∀ v, v ∉ S → 64 * r ≤ (Lv ends T J v).card := by
    intro v hv
    have h1 := hleaf v hv
    have h2 : ((64 * r : ℕ) : ℝ) ≤ (k : ℝ) / 128 := by
      have : (r : ℝ) * 8192 ≤ k := by exact_mod_cast hrk
      push_cast; linarith
    have h3 : ((64 * r : ℕ) : ℝ) ≤ (Lv ends T J v).card := h2.trans h1
    exact_mod_cast h3
  obtain ⟨ω, hωA, hZ⟩ := select (q := q) hs hT hL
  set Z := Zset ends T S r q ω with hZdef
  set H := S ∪ Z with hHdef
  set Jv : Fin n → Finset (Fin k) := fun v => if v ∈ H then ∅ else ω v with hJv
  -- the bound on `Z`
  have hZk : (Z.card : ℝ) ≤ n / k :=
    Zarith hH0 (by omega) (by omega) (by omega) (by omega)
      (by rw [hmeq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (by omega) _ hZ
  -- the frozen selections
  have hωL : ∀ v, v ∉ S → ω v ⊆ Lv ends T J v ∧ (ω v).card = 2 * r :=
    fun v hv => mem_Asp hv (hωA v)
  have hJvsub : ∀ v, Jv v ⊆ ω v := by
    intro v; simp only [hJv]; split_ifs
    · exact Finset.empty_subset _
    · exact le_rfl
  have hJvH : ∀ v, v ∉ H → Jv v = ω v := fun v hv => by simp only [hJv, if_neg hv]
  have hJvH' : ∀ v, v ∈ H → Jv v = ∅ := fun v hv => by simp only [hJv, if_pos hv]
  have hJne : ∀ v, Jv v ≠ ∅ → v ∉ H ∧ v ∉ S ∧ v ∉ Z := by
    intro v hv
    have h1 : v ∉ H := fun h => hv (hJvH' v h)
    refine ⟨h1, fun h => h1 (Finset.mem_union_left _ h), fun h => h1 (Finset.mem_union_right _ h)⟩
  have hJL : ∀ v, Jv v ⊆ Lv ends T J v := by
    intro v
    by_cases hv : v ∈ H
    · rw [hJvH' v hv]; exact Finset.empty_subset _
    · rw [hJvH v hv]; exact (hωL v (fun h => hv (Finset.mem_union_left _ h))).1
  have htests : ∀ v, Jv v ≠ ∅ → t1 ends q ω v ∧ t2 ends T r q ω v := by
    intro v hv
    obtain ⟨-, h2, h3⟩ := hJne v hv
    by_contra hc
    exact h3 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h2, hc⟩)
  have hF : FHyp ends T I J Jv r q := {
    g := { simple := hs, three := hn3, part := hT, disj := hIJ, cover := hcov,
           jsub := fun v => (hJL v).trans (Finset.filter_subset _ _),
           leaf := fun v j hj => (Finset.mem_filter.1 (hJL v hj)).2,
           prsub := fun v => pr_sub r (Jv v) }
    r1 := by omega
    q4 := by omega
    card := fun v hv => by
      obtain ⟨h1, h2, -⟩ := hJne v hv
      rw [hJvH v h1]; exact (hωL v h2).2
    t1 := fun v x hv hxv hadj => by
      calc (Jv v ∩ Jv x).card ≤ (ω v ∩ ω x).card :=
            Finset.card_le_card (Finset.inter_subset_inter (hJvsub v) (hJvsub x))
        _ ≤ q := (htests v hv).1 x hxv hadj
    t2 := fun v j hj => by
      have hv : Jv v ≠ ∅ := Finset.ne_empty_of_mem hj
      obtain ⟨h1, -, -⟩ := hJne v hv
      have hjω : j ∈ ω v := hJvsub v hj
      refine le_trans (Finset.card_le_card ?_) ((htests v hv).2 j hjω)
      intro e he
      rw [Finset.mem_filter] at he ⊢
      refine ⟨?_, hJvsub _ he.2⟩
      have := he.1
      simp only [Prot] at this
      rw [hJvH v h1] at this
      exact this }
  refine ⟨H, Res ends T Jv (fun v => pr r (Jv v)), Finset.subset_union_left, ?_, res_owner hF.g,
    res_sub hF.g, ?_, ?_⟩
  · have : H \ S ⊆ Z := by
      intro v hv
      rw [Finset.mem_sdiff, Finset.mem_union] at hv
      tauto
    exact (Nat.cast_le.2 (Finset.card_le_card this)).trans hZk
  · intro v
    refine ⟨fun hv => ?_, fun hv => res_empty hF (hJvH' v hv)⟩
    have hvS : v ∉ S := fun h => hv (Finset.mem_union_left _ h)
    have hne : Jv v ≠ ∅ := by
      rw [hJvH v hv]; intro h
      have := (hωL v hvS).2
      rw [h, Finset.card_empty] at this; omega
    exact res_card hF hne
  · intro U R' hX hR'
    obtain ⟨b, hb1, hbn, hpM, hblt⟩ := b_exists (n := n) (r := r) (by omega) (by omega)
    obtain ⟨V, hV1, hV2, hV3⟩ := restore_all hX hR' hF hm hb1 hbn hpM
    refine ⟨V, hV1, hV2, fun j hj => ⟨(hV3 j hj).1, (hV3 j hj).2.trans ?_⟩⟩
    have := tail_arith (n := n) (k := k) (r := r) (b := b) (by omega) h2k (by omega) (by omega)
      (by omega) hblt
    linarith

end LowDiameterNashWilliams.Main
end

theorem solution : type_of% @LowDiameterNashWilliams.Main.chk_lemma_4_3 := @LowDiameterNashWilliams.Main.chk_lemma_4_3
