-- Prove2me | solution 1 for LowDiameterNashWilliams.Main.lemma_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T19:47:27.023356+00:00
-- url     : https://prove2.me/submissions/a30b6ad5-a0c0-4b66-99a2-8eff75118917
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Definitions.Def_LowDiameterNashWilliams_Main_Geometry
import Definitions.Def_LowDiameterNashWilliams_Main_Reserves
import Definitions.Def_LowDiameterNashWilliams_Main_Sampling
import Definitions.Def_LowDiameterNashWilliams_Main_Computation
import Theorems.Thm_LowDiameterNashWilliams_Main_lemma_4_2

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

/-- a forest with `n - 1` edges is a spanning tree -/
theorem tree_of_forest (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (hn : 0 < n)
    (F : Finset (Fin m)) (hF : IsForest ends F) (hcard : F.card + 1 = n) :
    IsSpanningTree ends F := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [tree_iff ends hs hn]
  rw [forest_iff ends hs] at hF
  set H := edgeGraph ends F with hH
  obtain ⟨T', hle, -, hT'⟩ :=
    (SimpleGraph.connected_top (V := Fin n)).exists_isTree_le_of_le_of_isAcyclic
      (le_top : H ≤ ⊤) hF
  have hc' := (SimpleGraph.isTree_iff_connected_and_card.1 hT').2
  have hcH : Nat.card H.edgeSet = F.card := ncard_edgeSet ends hs F
  rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hc'
  have hsub : H.edgeSet ⊆ T'.edgeSet := SimpleGraph.edgeSet_mono hle
  have heq : H.edgeSet = T'.edgeSet := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]; omega
  have : H = T' := SimpleGraph.edgeSet_inj.1 heq
  rw [this]; exact hT'

/-- a walk that avoids an end `v` of `g` does not use `g` -/
theorem rch_avoid (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) {F : Finset (Fin m)}
    {g : Fin m} {v : Fin n} (hv : v ∈ ends g) {x y : Fin n} (p : (edgeGraph ends F).Walk x y)
    (hp : v ∉ p.support) : Rch ends (F.erase g) x y := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab q ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hp
    obtain ⟨e, he, hee⟩ := (adjS ends hs F a b).1 hab
    have hne : e ≠ g := by
      rintro rfl
      rw [hee, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact hp.1 rfl
      · exact hp.2 (SimpleGraph.Walk.start_mem_support q)
    exact (rch_of_edge ends (Finset.mem_erase.2 ⟨hne, he⟩) hee).trans (ih hp.2)

/-- inserting a new edge `f = vp` into a spanning tree and removing the first edge `g` at `v`
of the tree path from `v` to `p` gives a spanning tree -/
theorem tree_exchange (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) {U : Finset (Fin m)}
    (hU : IsSpanningTree ends U) {f : Fin m} (hf : f ∉ U) {v p : Fin n}
    (hfe : ends f = s(v, p)) :
    ∃ g ∈ U, v ∈ ends g ∧ IsSpanningTree ends (insert f (U.erase g)) := by
  have hvp : v ≠ p := by
    rintro rfl; exact hs.2 f (by rw [hfe]; simp)
  have hn : 0 < n := Fin.pos v
  obtain ⟨P, hP⟩ := (connected_of_tree ends hU v p).exists_isPath
  cases P with
  | nil => exact absurd rfl hvp
  | @cons _ w _ hvw q =>
    obtain ⟨g, hg, hge⟩ := (adjS ends hs U v w).1 hvw
    have hvg : v ∈ ends g := by rw [hge]; simp
    refine ⟨g, hg, hvg, ?_⟩
    have hvq : v ∉ q.support := (SimpleGraph.Walk.cons_isPath_iff _ _).1 hP |>.2
    have hwp : Rch ends (U.erase g) w p := rch_avoid ends hs hvg q hvq
    have hforest : IsForest ends (U.erase g) :=
      LowDiameterNashWilliams.Dev.Forest.isForest_mono ends (Finset.erase_subset g U) hU.2.2.2.1
    have hnr : ¬ Rch ends (U.erase g) v p := by
      intro h
      exact hU.2.2.2.1 g hg v w hge (h.trans hwp.symm)
    have hfn : f ∉ U.erase g := fun h => hf (Finset.mem_of_mem_erase h)
    have hF := isForest_insert ends hforest hfn hfe hnr
    apply tree_of_forest ends hs hn _ hF
    rw [Finset.card_insert_of_notMem hfn, Finset.card_erase_of_mem hg]
    have := tree_card ends hU
    have : 0 < U.card := Finset.card_pos.2 ⟨g, hg⟩
    omega

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

/-- the forest to insert: owned edges, at most one per owner, with a height function -/
def Insertable (ends : Fin m → Sym2 (Fin n)) (R : Fin n → Edges m) (F : Finset (Fin m)) :
    Prop :=
  (∀ f ∈ F, ∃ v, f ∈ R v) ∧
  (∀ v, ∀ f ∈ F, ∀ g ∈ F, f ∈ R v → g ∈ R v → f = g) ∧
  ∃ h : Fin n → ℕ, ∀ v, ∀ f ∈ F, f ∈ R v → ∀ b, ends f = s(v, b) → h b < h v

theorem insertable_mono (ends : Fin m → Sym2 (Fin n)) (R : Fin n → Edges m)
    {F F' : Finset (Fin m)} (hsub : F' ⊆ F) (hF : Insertable ends R F) :
    Insertable ends R F' := by
  obtain ⟨h1, h2, h, h3⟩ := hF
  exact ⟨fun f hf => h1 f (hsub hf), fun v f hf g hg => h2 v f (hsub hf) g (hsub hg),
    h, fun v f hf => h3 v f (hsub hf)⟩

/-- the result of inserting -/
def Inserted (ends : Fin m → Sym2 (Fin n)) (T : Edges m) (R : Fin n → Edges m)
    (F : Finset (Fin m)) (U : Edges m) (R1 : Fin n → Edges m) : Prop :=
  IsSpanningTree ends U ∧ OwnerReserves ends R1 ∧ (∀ v, Disjoint U (R1 v)) ∧
    U ∪ Finset.univ.biUnion R1 = T ∪ Finset.univ.biUnion R ∧
    (∀ v, (R1 v).card = (R v).card) ∧ F ⊆ U ∧ ∀ v, R v \ F ⊆ R1 v

theorem insert_all (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (T : Edges m)
    (R : Fin n → Edges m) (hT : IsSpanningTree ends T) (hR : OwnerReserves ends R)
    (hTR : ∀ v, Disjoint T (R v)) :
    ∀ (k : ℕ) (F : Finset (Fin m)), F.card = k → Insertable ends R F →
      ∃ U R1, Inserted ends T R F U R1 := by
  intro k
  induction k with
  | zero =>
    intro F hF _
    rw [Finset.card_eq_zero] at hF
    subst hF
    refine ⟨T, R, hT, hR, hTR, rfl, fun _ => rfl, Finset.empty_subset _, fun v => ?_⟩
    simp
  | succ k ih =>
    intro F hFk hF
    obtain ⟨hown, hinj, h, hht⟩ := hF
    have hFne : F.Nonempty := Finset.card_pos.1 (by omega)
    set S := Finset.univ.filter fun v => ∃ f ∈ F, f ∈ R v with hS
    have hSne : S.Nonempty := by
      obtain ⟨f, hf⟩ := hFne
      obtain ⟨v, hv⟩ := hown f hf
      exact ⟨v, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, f, hf, hv⟩⟩
    obtain ⟨v, hvS, hvmax⟩ := Finset.exists_max_image S h hSne
    obtain ⟨f0, hf0F, hf0R⟩ := (Finset.mem_filter.1 hvS).2
    have hdeg : ∀ g ∈ F, v ∈ ends g → g = f0 := by
      intro g hg hvg
      obtain ⟨w, hw⟩ := hown g hg
      by_cases hwv : w = v
      · subst hwv; exact hinj w g hg f0 hf0F hw hf0R
      · exfalso
        have hwg : w ∈ ends g := hR.1 w g hw
        have hge : ends g = s(w, v) := (Sym2.mem_and_mem_iff hwv).1 ⟨hwg, hvg⟩
        have hlt := hht w g hg hw v hge
        have hwS : w ∈ S := by
          rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, g, hg, hw⟩
        have := hvmax w hwS
        omega
    set F' := F.erase f0 with hF'
    have hF'k : F'.card = k := by rw [Finset.card_erase_of_mem hf0F]; omega
    have hF'ins : Insertable ends R F' :=
      insertable_mono ends R (Finset.erase_subset f0 F) ⟨hown, hinj, h, hht⟩
    obtain ⟨U', R1', hU', hR1', hUR1', hun', hcard', hFU', hsub'⟩ := ih F' hF'k hF'ins
    have hf0R1 : f0 ∈ R1' v := hsub' v (by
      rw [Finset.mem_sdiff]; exact ⟨hf0R, fun h => (Finset.notMem_erase f0 F) h⟩)
    have hf0U : f0 ∉ U' := Finset.disjoint_right.1 (hUR1' v) hf0R1
    obtain ⟨p, hp⟩ := Sym2.mem_iff_exists.1 (hR.1 v f0 hf0R)
    obtain ⟨g, hgU, hvg, hU⟩ := tree_exchange ends hs hU' hf0U hp
    have hgf0 : g ≠ f0 := fun h => hf0U (h ▸ hgU)
    have hgF : g ∉ F := fun h => hgf0 (hdeg g h hvg)
    have hgR : ∀ x, g ∉ R1' x := fun x => Finset.disjoint_left.1 (hUR1' x) hgU
    have hf0x : ∀ x, x ≠ v → f0 ∉ R1' x := fun x hx h =>
      Finset.disjoint_left.1 (hR1'.2 v x (Ne.symm hx)) hf0R1 h
    set R1 : Fin n → Edges m := Function.update R1' v (insert g ((R1' v).erase f0)) with hR1
    have hmem : ∀ x e, e ∈ R1 x ↔
        (x = v ∧ (e = g ∨ (e ≠ f0 ∧ e ∈ R1' v))) ∨ (x ≠ v ∧ e ∈ R1' x) := by
      intro x e
      by_cases hx : x = v
      · subst hx
        simp [hR1, Function.update_self, Finset.mem_insert, Finset.mem_erase]
      · simp [hR1, Function.update_of_ne hx, hx]
    set U := insert f0 (U'.erase g) with hUdef
    have hmemU : ∀ e, e ∈ U ↔ e = f0 ∨ (e ≠ g ∧ e ∈ U') := by
      intro e; simp [hUdef, Finset.mem_insert, Finset.mem_erase]
    refine ⟨U, R1, hU, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro x e he
      rcases (hmem x e).1 he with ⟨rfl, rfl | ⟨-, he'⟩⟩ | ⟨-, he'⟩
      · exact hvg
      · exact hR1'.1 x e he'
      · exact hR1'.1 x e he'
    · intro x y hxy
      rw [Finset.disjoint_left]
      intro e hex hey
      rw [hmem] at hex hey
      rcases hex with ⟨rfl, hex⟩ | ⟨hxv, hex⟩ <;> rcases hey with ⟨rfl, hey⟩ | ⟨hyv, hey⟩
      · exact hxy rfl
      · rcases hex with rfl | ⟨-, hex⟩
        · exact hgR y hey
        · exact Finset.disjoint_left.1 (hR1'.2 x y hxy) hex hey
      · rcases hey with rfl | ⟨-, hey⟩
        · exact hgR x hex
        · exact Finset.disjoint_left.1 (hR1'.2 x y hxy) hex hey
      · exact Finset.disjoint_left.1 (hR1'.2 x y hxy) hex hey
    · intro x
      rw [Finset.disjoint_left]
      intro e heU heR
      rw [hmemU] at heU
      rw [hmem] at heR
      rcases heU with rfl | ⟨heg, heU⟩
      · rcases heR with ⟨-, h1 | ⟨h2, -⟩⟩ | ⟨hxv, h3⟩
        · exact hgf0 h1.symm
        · exact h2 rfl
        · exact hf0x x hxv h3
      · rcases heR with ⟨-, h1 | ⟨-, h2⟩⟩ | ⟨-, h3⟩
        · exact heg h1
        · exact Finset.disjoint_left.1 (hUR1' v) heU h2
        · exact Finset.disjoint_left.1 (hUR1' x) heU h3
    · rw [← hun']
      ext e
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
      rw [hmemU]
      constructor
      · rintro ((rfl | ⟨-, he⟩) | ⟨x, hx⟩)
        · exact Or.inr ⟨v, hf0R1⟩
        · exact Or.inl he
        · rw [hmem] at hx
          rcases hx with ⟨rfl, rfl | ⟨-, he⟩⟩ | ⟨-, he⟩
          · exact Or.inl hgU
          · exact Or.inr ⟨_, he⟩
          · exact Or.inr ⟨x, he⟩
      · rintro (he | ⟨x, hx⟩)
        · by_cases heg : e = g
          · subst heg
            exact Or.inr ⟨v, (hmem v e).2 (Or.inl ⟨rfl, Or.inl rfl⟩)⟩
          · exact Or.inl (Or.inr ⟨heg, he⟩)
        · by_cases hef : e = f0
          · exact Or.inl (Or.inl hef)
          · by_cases hxv : x = v
            · subst hxv
              exact Or.inr ⟨x, (hmem x e).2 (Or.inl ⟨rfl, Or.inr ⟨hef, hx⟩⟩)⟩
            · exact Or.inr ⟨x, (hmem x e).2 (Or.inr ⟨hxv, hx⟩)⟩
    · intro x
      rw [← hcard' x]
      by_cases hxv : x = v
      · subst hxv
        rw [hR1, Function.update_self, Finset.card_insert_of_notMem, Finset.card_erase_of_mem hf0R1]
        · have : 0 < (R1' x).card := Finset.card_pos.2 ⟨f0, hf0R1⟩
          omega
        · exact fun h => hgR x (Finset.mem_of_mem_erase h)
      · rw [hR1, Function.update_of_ne hxv]
    · intro e he
      rw [hmemU]
      by_cases hef : e = f0
      · exact Or.inl hef
      · right
        have heF' : e ∈ F' := Finset.mem_erase.2 ⟨hef, he⟩
        exact ⟨fun h => hgF (h ▸ he), hFU' heF'⟩
    · intro x e he
      rw [Finset.mem_sdiff] at he
      have he' : e ∈ R1' x := hsub' x (Finset.mem_sdiff.2
        ⟨he.1, fun h => he.2 (Finset.mem_of_mem_erase h)⟩)
      rw [hmem]
      by_cases hxv : x = v
      · subst hxv
        exact Or.inl ⟨rfl, Or.inr ⟨fun h => he.2 (h ▸ hf0F), he'⟩⟩
      · exact Or.inr ⟨hxv, he'⟩

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

/-- every edge of `F` joins its owner to a vertex of `A` -/
def Cand (ends : Fin m → Sym2 (Fin n)) (R : Fin n → Edges m) (A : Finset (Fin n))
    (F : Finset (Fin m)) : Prop :=
  ∀ f ∈ F, ∃ v, f ∈ R v ∧ ∃ a ∈ A, a ≠ v ∧ ends f = s(v, a)

theorem own_eq {ends : Fin m → Sym2 (Fin n)} {R : Fin n → Edges m} (hR : OwnerReserves ends R)
    {e : Fin m} {v w : Fin n} (hv : e ∈ R v) (hw : e ∈ R w) : v = w := by
  by_contra h
  exact Finset.disjoint_left.1 (hR.2 v w h) hv hw

theorem exists_maxF (ends : Fin m → Sym2 (Fin n)) (R : Fin n → Edges m)
    (hR : OwnerReserves ends R) (A : Finset (Fin n)) :
    ∃ F, Insertable ends R F ∧ Cand ends R A F ∧
      ∀ r, (∀ f ∈ F, f ∉ R r) → ∀ e ∈ R r, ∀ a ∈ A, a ≠ r → ends e = s(r, a) →
        Rch ends F r a := by
  set P := (Finset.univ : Finset (Fin m)).powerset.filter
    fun F => Insertable ends R F ∧ Cand ends R A F with hP
  have h0 : (∅ : Finset (Fin m)) ∈ P := by
    rw [hP, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, ⟨fun f hf => absurd hf (Finset.notMem_empty f),
      fun v f hf => absurd hf (Finset.notMem_empty f), fun _ => 0,
      fun v f hf => absurd hf (Finset.notMem_empty f)⟩, fun f hf => absurd hf (Finset.notMem_empty f)⟩
  obtain ⟨F, hFP, hmax⟩ := Finset.exists_max_image P Finset.card ⟨∅, h0⟩
  rw [hP, Finset.mem_filter] at hFP
  obtain ⟨-, hI, hC⟩ := hFP
  refine ⟨F, hI, hC, ?_⟩
  intro r hr e he a ha har hea
  by_contra hnr
  have heF : e ∉ F := fun h => hr e h he
  obtain ⟨hown, hinj, h, hht⟩ := hI
  have hins : insert e F ∈ P := by
    rw [hP, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.subset_univ _, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro f hf
      rcases Finset.mem_insert.1 hf with hfe | hf
      · exact ⟨r, hfe ▸ he⟩
      · exact hown f hf
    · intro v f hf g hg hfv hgv
      rcases Finset.mem_insert.1 hf with hfe | hf <;>
        rcases Finset.mem_insert.1 hg with hge | hg
      · rw [hfe, hge]
      · exfalso
        have hrv : r = v := own_eq hR he (hfe ▸ hfv)
        exact hr g hg (hrv ▸ hgv)
      · exfalso
        have hrv : r = v := own_eq hR he (hge ▸ hgv)
        exact hr f hf (hrv ▸ hfv)
      · exact hinj v f hf g hg hfv hgv
    · refine ⟨fun x => if Rch ends F r x then h x + h a + 1 else h x, ?_⟩
      intro v f hf hfv b hfb
      rcases Finset.mem_insert.1 hf with hfe | hf
      · subst hfe
        have hrv : r = v := own_eq hR he hfv
        subst hrv
        have hab : a = b := Sym2.congr_right.1 (hea.symm.trans hfb)
        subst hab
        simp only [hnr, if_false, SimpleGraph.Reachable.refl, if_true]
        omega
      · have hvb : Rch ends F v b := rch_of_edge ends hf hfb
        have hlt := hht v f hf hfv b hfb
        by_cases hrv : Rch ends F r v
        · have hrb : Rch ends F r b := hrv.trans hvb
          simp only [hrv, hrb, if_true]
          omega
        · have hrb : ¬ Rch ends F r b := fun h => hrv (h.trans hvb.symm)
          simp only [hrv, hrb, if_false]
          exact hlt
    · intro f hf
      rcases Finset.mem_insert.1 hf with hfe | hf
      · exact ⟨r, hfe ▸ he, a, ha, har, hfe ▸ hea⟩
      · exact hC f hf
  have := hmax _ hins
  rw [Finset.card_insert_of_notMem heF] at this
  omega

/-- along a path starting at a vertex that does not own its first edge, every edge is owned
by its far end; in particular the last vertex owns an edge -/
theorem path_owner (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (R : Fin n → Edges m)
    (hR : OwnerReserves ends R) (F : Finset (Fin m))
    (hown : ∀ f ∈ F, ∃ v, f ∈ R v)
    (hinj : ∀ v, ∀ f ∈ F, ∀ g ∈ F, f ∈ R v → g ∈ R v → f = g) {x w : Fin n}
    (p : (edgeGraph ends F).Walk x w) :
    p.IsPath → x ≠ w → (∀ g ∈ F, g ∈ R x → ∀ z ∈ p.support.tail, ends g ≠ s(x, z)) →
      ∃ g ∈ F, g ∈ R w := by
  induction p with
  | nil => intro _ h; exact absurd rfl h
  | @cons x y w hxy q ih =>
    intro hP hxw hx
    rw [SimpleGraph.Walk.cons_isPath_iff] at hP
    obtain ⟨f, hf, hfe⟩ := (adjS ends hs F x y).1 hxy
    obtain ⟨o, ho⟩ := hown f hf
    have hof : o ∈ ends f := hR.1 o f ho
    rw [hfe, Sym2.mem_iff] at hof
    rcases hof with rfl | rfl
    · exfalso
      refine hx f hf ho y ?_ hfe
      rw [SimpleGraph.Walk.support_cons, List.tail_cons]
      exact SimpleGraph.Walk.start_mem_support q
    · by_cases hyw : o = w
      · subst hyw; exact ⟨f, hf, ho⟩
      · apply ih hP.1 hyw
        intro g hg hgR z hz hgz
        have hgf : g = f := hinj o g hg f hf hgR ho
        subst hgf
        rw [hfe, Sym2.eq_iff] at hgz
        rcases hgz with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hxy.ne h1
        · exact hP.2 (h1 ▸ List.mem_of_mem_tail hz)

theorem nonowner_not_rch (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (R : Fin n → Edges m)
    (hR : OwnerReserves ends R) (F : Finset (Fin m))
    (hown : ∀ f ∈ F, ∃ v, f ∈ R v)
    (hinj : ∀ v, ∀ f ∈ F, ∀ g ∈ F, f ∈ R v → g ∈ R v → f = g) {x w : Fin n}
    (hxw : x ≠ w) (hx : ∀ f ∈ F, f ∉ R x) (hw : ∀ f ∈ F, f ∉ R w) : ¬ Rch ends F x w := by
  intro h
  obtain ⟨p, hp⟩ := h.exists_isPath
  obtain ⟨g, hg, hgw⟩ := path_owner ends hs R hR F hown hinj p hp hxw
    (fun g hg hgx _ _ _ => hx g hg hgx)
  exact hw g hg hgw

/-- the `A`-neighbours of `r` through its reserve -/
noncomputable def Nb (ends : Fin m → Sym2 (Fin n)) (R : Fin n → Edges m) (A : Finset (Fin n))
    (r : Fin n) : Finset (Fin n) :=
  A.filter fun a => a ≠ r ∧ ∃ e ∈ R r, ends e = s(r, a)

theorem nb_card (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (R : Fin n → Edges m)
    (A : Finset (Fin n)) (r : Fin n) :
    reserveNeighbors ends R r A ≤ (Nb ends R A r).card := by
  unfold reserveNeighbors
  let φ : Fin m → Fin n := fun e =>
    if h : ∃ u ∈ A, u ≠ r ∧ ends e = s(r, u) then h.choose else r
  have hφ : ∀ e, (∃ u ∈ A, u ≠ r ∧ ends e = s(r, u)) →
      φ e ∈ A ∧ φ e ≠ r ∧ ends e = s(r, φ e) := by
    intro e h
    simp only [φ, dif_pos h]
    exact h.choose_spec
  apply Finset.card_le_card_of_injOn φ
  · intro e he
    rw [Finset.mem_coe, Finset.mem_filter] at he
    obtain ⟨h1, h2, h3⟩ := hφ e he.2
    rw [Finset.mem_coe, Nb, Finset.mem_filter]
    exact ⟨h1, h2, e, he.1, h3⟩
  · intro e he e' he' hee
    rw [Finset.mem_coe, Finset.mem_filter] at he he'
    apply hs.1
    rw [(hφ e he.2).2.2, (hφ e' he'.2).2.2, hee]

theorem nb_sub (ends : Fin m → Sym2 (Fin n)) (R : Fin n → Edges m) (A : Finset (Fin n))
    (r : Fin n) : Nb ends R A r ⊆ A := Finset.filter_subset _ _

/-- `|F|` plus the number of non-owners is `n` -/
theorem card_F_add (ends : Fin m → Sym2 (Fin n)) (R : Fin n → Edges m)
    (hR : OwnerReserves ends R) (F : Finset (Fin m))
    (hown : ∀ f ∈ F, ∃ v, f ∈ R v)
    (hinj : ∀ v, ∀ f ∈ F, ∀ g ∈ F, f ∈ R v → g ∈ R v → f = g) :
    F.card + (Finset.univ.filter fun v => ¬ ∃ f ∈ F, f ∈ R v).card = n := by
  have h1 : F.card = (Finset.univ.filter fun v => ∃ f ∈ F, f ∈ R v).card := by
    apply Finset.card_bij (fun f hf => (hown f hf).choose)
    · intro f hf
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, f, hf, (hown f hf).choose_spec⟩
    · intro f hf g hg hfg
      have h1 := (hown f hf).choose_spec
      have h2 := (hown g hg).choose_spec
      rw [hfg] at h1
      exact hinj _ f hf g hg h1 h2
    · intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨f, hf, hfv⟩ := hv.2
      exact ⟨f, hf, own_eq hR (hown f hf).choose_spec hfv⟩
  rw [h1, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]

/-- the prepared tree: the output of the first half of the proof of Lemma 4.1 -/
theorem prepare (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (T : Edges m)
    (R : Fin n → Edges m) (hT : IsSpanningTree ends T) (hR : OwnerReserves ends R)
    (hTR : ∀ v, Disjoint T (R v)) (A B : Finset (Fin n)) (d : ℕ) (hd : 1 ≤ d)
    (hN : ∀ v, v ∉ B → d ≤ reserveNeighbors ends R v A) :
    ∃ (U : Edges m) (R1 : Fin n → Edges m) (W : Finset (Fin n)) (c : ℕ),
      IsSpanningTree ends U ∧ OwnerReserves ends R1 ∧ (∀ v, Disjoint U (R1 v)) ∧
      U ∪ Finset.univ.biUnion R1 = T ∪ Finset.univ.biUnion R ∧
      (∀ v, (R1 v).card = (R v).card) ∧ A ∪ B ⊆ W ∧
      (∀ x, x ∉ W → ∃ f ∈ U, ∃ a ∈ W, ends f = s(x, a) ∧ ∀ g ∈ U, x ∈ ends g → g = f) ∧
      (∀ v ∈ W, v ∉ B → d - 1 ≤ ((R1 v).filter fun e => ∀ y ∈ ends e, y ∈ W).card) ∧
      (W \ (A ∪ B)).card + 2 ≤ 2 * c ∧ d * c ≤ d * B.card + A.card := by
  obtain ⟨F, hI, hC, hmax⟩ := exists_maxF ends R hR A
  obtain ⟨U, R1, hU, hR1, hUR1, hun, hcard, hFU, hsub⟩ :=
    insert_all ends hs T R hT hR hTR F.card F rfl hI
  obtain ⟨hown, hinj, -⟩ := hI
  set NO := Finset.univ.filter fun v => ¬ ∃ f ∈ F, f ∈ R v with hNO
  have hFNO := card_F_add ends R hR F hown hinj
  rw [← hNO] at hFNO
  have hnoF : ∀ v, v ∈ NO → ∀ f ∈ F, f ∉ R v := by
    intro v hv f hf hfv
    rw [hNO, Finset.mem_filter] at hv
    exact hv.2 ⟨f, hf, hfv⟩
  -- counting the non-owners
  set NR := NO.filter fun v => v ∉ B with hNR
  have hNOle : NO.card ≤ B.card + NR.card := by
    have : NO ⊆ B ∪ NR := by
      intro v hv
      by_cases hvB : v ∈ B
      · exact Finset.mem_union_left _ hvB
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hv, hvB⟩)
    exact (Finset.card_le_card this).trans (Finset.card_union_le _ _)
  have hnb_rch : ∀ r ∈ NO, ∀ a ∈ Nb ends R A r, Rch ends F r a := by
    intro r hr a ha
    rw [Nb, Finset.mem_filter] at ha
    obtain ⟨haA, har, e, he, hea⟩ := ha
    exact hmax r (hnoF r hr) e he a haA har hea
  have hdisj : (NR : Set (Fin n)).PairwiseDisjoint (Nb ends R A) := by
    intro r1 hr1 r2 hr2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha1 ha2
    rw [Finset.mem_coe, hNR, Finset.mem_filter] at hr1 hr2
    exact nonowner_not_rch ends hs R hR F hown hinj hne (hnoF r1 hr1.1) (hnoF r2 hr2.1)
      ((hnb_rch r1 hr1.1 a ha1).trans (hnb_rch r2 hr2.1 a ha2).symm)
  have hdNR : d * NR.card ≤ A.card := by
    have h1 : (NR.biUnion (Nb ends R A)).card ≤ A.card :=
      Finset.card_le_card (Finset.biUnion_subset.2 fun r _ => nb_sub ends R A r)
    rw [Finset.card_biUnion hdisj] at h1
    have h2 : NR.card • d ≤ ∑ r ∈ NR, (Nb ends R A r).card := by
      apply Finset.card_nsmul_le_sum
      intro r hr
      rw [hNR, Finset.mem_filter] at hr
      exact (hN r hr.2).trans (nb_card ends hs R A r)
    rw [smul_eq_mul] at h2
    rw [mul_comm]; omega
  -- every vertex outside `A ∪ B` owns an edge of `F`
  have hout : ∀ x, x ∉ A → x ∉ B → ∃ f ∈ F, f ∈ R x := by
    intro x hxA hxB
    by_contra hx
    push Not at hx
    have hpos : 0 < (Nb ends R A x).card := lt_of_lt_of_le (by omega)
      ((hN x hxB).trans (nb_card ends hs R A x))
    obtain ⟨a, ha⟩ := Finset.card_pos.1 hpos
    have hrch : Rch ends F x a := by
      rw [Nb, Finset.mem_filter] at ha
      obtain ⟨haA, hax, e, he, hea⟩ := ha
      exact hmax x hx e he a haA hax hea
    have hxa : x ≠ a := fun h => hxA (h ▸ nb_sub ends R A x ha)
    obtain ⟨p⟩ := hrch
    cases p with
    | nil => exact hxa rfl
    | @cons _ y _ hxy _ =>
      obtain ⟨f, hf, hfe⟩ := (adjS ends hs F x y).1 hxy
      obtain ⟨w, hfw, a', ha', -, hfe'⟩ := hC f hf
      have hxf : x ∈ ends f := by rw [hfe]; simp
      rw [hfe', Sym2.mem_iff] at hxf
      rcases hxf with rfl | rfl
      · exact hx f hf hfw
      · exact hxA ha'
  -- the core
  set D := Finset.univ.filter fun x => ∃ e ∈ U \ F, x ∈ ends e with hD
  set W := A ∪ B ∪ D with hW
  have hUcard := tree_card ends hU
  have hFcard : (U \ F).card + F.card = U.card := Finset.card_sdiff_add_card_eq_card hFU
  have hDcard : D.card ≤ 2 * (U \ F).card := by
    have : D ⊆ (U \ F).biUnion fun e => Finset.univ.filter fun x => x ∈ ends e := by
      intro x hx
      rw [hD, Finset.mem_filter] at hx
      obtain ⟨e, he, hxe⟩ := hx.2
      exact Finset.mem_biUnion.2 ⟨e, he, Finset.mem_filter.2 ⟨Finset.mem_univ _, hxe⟩⟩
    refine (Finset.card_le_card this).trans ?_
    refine (Finset.card_biUnion_le_card_mul _ _ 2 ?_).trans (by rw [mul_comm])
    intro e _
    obtain ⟨u, v, huv⟩ := exists_ends ends e
    have : (Finset.univ.filter fun x => x ∈ ends e) ⊆ {u, v} := by
      intro x hx
      rw [Finset.mem_filter, huv, Sym2.mem_iff] at hx
      rcases hx.2 with rfl | rfl <;> simp
    exact (Finset.card_le_card this).trans Finset.card_le_two
  refine ⟨U, R1, W, NO.card, hU, hR1, hUR1, hun, hcard, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; rw [hW]; exact Finset.mem_union_left _ hx
  · intro x hxW
    have hxA : x ∉ A := fun h => hxW (by rw [hW]; simp [h])
    have hxB : x ∉ B := fun h => hxW (by rw [hW]; simp [h])
    have hxD : x ∉ D := fun h => hxW (by rw [hW]; simp [h])
    obtain ⟨f, hf, hfx⟩ := hout x hxA hxB
    obtain ⟨w, hfw, a, ha, -, hfe⟩ := hC f hf
    have hwx : w = x := own_eq hR hfw hfx
    subst hwx
    refine ⟨f, hFU hf, a, by rw [hW]; simp [ha], hfe, ?_⟩
    intro g hg hwg
    have hgF : g ∈ F := by
      by_contra hgF
      exact hxD (by rw [hD, Finset.mem_filter]; exact ⟨Finset.mem_univ _, g, Finset.mem_sdiff.2 ⟨hg, hgF⟩, hwg⟩)
    obtain ⟨w', hgw', a', ha', -, hge⟩ := hC g hgF
    rw [hge, Sym2.mem_iff] at hwg
    rcases hwg with rfl | rfl
    · exact hinj _ g hgF f hf hgw' hfx
    · exact absurd ha' hxA
  · intro v hvW hvB
    set E := (R v).filter fun e => ∃ u ∈ A, u ≠ v ∧ ends e = s(v, u) with hE
    have hEd : d ≤ E.card := hN v hvB
    have hEF : (E ∩ F).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro f hf g hg
      rw [Finset.mem_inter, hE, Finset.mem_filter] at hf hg
      exact hinj v f hf.2 g hg.2 hf.1.1 hg.1.1
    have h1 := Finset.card_sdiff_add_card_inter E F
    have hsub2 : E \ F ⊆ (R1 v).filter fun e => ∀ y ∈ ends e, y ∈ W := by
      intro e he
      rw [Finset.mem_sdiff, hE, Finset.mem_filter] at he
      obtain ⟨⟨heR, u, hu, -, heu⟩, heF⟩ := he
      rw [Finset.mem_filter]
      refine ⟨hsub v (Finset.mem_sdiff.2 ⟨heR, heF⟩), ?_⟩
      intro y hy
      rw [heu, Sym2.mem_iff] at hy
      rcases hy with rfl | rfl
      · exact hvW
      · rw [hW]; simp [hu]
    have := Finset.card_le_card hsub2
    omega
  · have hsubD : W \ (A ∪ B) ⊆ D := by
      intro x hx
      rw [Finset.mem_sdiff, hW, Finset.mem_union] at hx
      tauto
    have := Finset.card_le_card hsubD
    omega
  · have := Nat.mul_le_mul_left d hNOle
    rw [Nat.mul_add] at this
    omega

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

theorem adj_tr (hι : Function.Injective ι) (hends : ∀ i, Sym2.map ι (endsW i) = ends (κ i))
    {S : Finset (Fin m')} {S' : Finset (Fin m)} (hSS : ∀ i ∈ S, κ i ∈ S') {a b : Fin N}
    (h : (edgeGraph endsW S).Adj a b) : (edgeGraph ends S').Adj (ι a) (ι b) := by
  rw [adj_iff] at h ⊢
  obtain ⟨⟨i, hi, hie⟩, hab⟩ := h
  refine ⟨⟨κ i, hSS i hi, ?_⟩, fun h => hab (hι h)⟩
  rw [← hends i, hie, Sym2.map_mk]

/-- the graph homomorphism induced by `ι` -/
def homTr (hι : Function.Injective ι) (hends : ∀ i, Sym2.map ι (endsW i) = ends (κ i))
    {S : Finset (Fin m')} {S' : Finset (Fin m)} (hSS : ∀ i ∈ S, κ i ∈ S') :
    edgeGraph endsW S →g edgeGraph ends S' where
  toFun := ι
  map_rel' h := adj_tr ends endsW ι κ hι hends hSS h

theorem rch_tr (hι : Function.Injective ι) (hends : ∀ i, Sym2.map ι (endsW i) = ends (κ i))
    {S : Finset (Fin m')} {S' : Finset (Fin m)} (hSS : ∀ i ∈ S, κ i ∈ S') {a b : Fin N}
    (h : Rch endsW S a b) : Rch ends S' (ι a) (ι b) :=
  h.map (homTr ends endsW ι κ hι hends hSS)

theorem dist_tr (hι : Function.Injective ι) (hends : ∀ i, Sym2.map ι (endsW i) = ends (κ i))
    {S : Finset (Fin m')} {S' : Finset (Fin m)} (hSS : ∀ i ∈ S, κ i ∈ S') (a b : Fin N) :
    distance ends S' (ι a) (ι b) ≤ distance endsW S a b := by
  unfold distance
  refine le_iInf fun p => ?_
  refine iInf_le_of_le (p.map (homTr ends endsW ι κ hι hends hSS)) ?_
  exact le_of_eq (by exact_mod_cast SimpleGraph.Walk.length_map _ p)

theorem simple_tr (hκ : Function.Injective κ) (hends : ∀ i, Sym2.map ι (endsW i) = ends (κ i))
    (hs : Simple ends) : Simple endsW := by
  refine ⟨fun i j hij => hκ (hs.1 ?_), fun i hi => hs.2 (κ i) ?_⟩
  · rw [← hends i, ← hends j, hij]
  · rw [← hends i]; exact hi.map

theorem forest_tr (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (hends : ∀ i, Sym2.map ι (endsW i) = ends (κ i)) {S : Finset (Fin m')}
    {U : Finset (Fin m)} (hSU : ∀ i ∈ S, κ i ∈ U) (hU : IsForest ends U) :
    IsForest endsW S := by
  intro e he a b hab hr
  have hSS : ∀ i ∈ S.erase e, κ i ∈ U.erase (κ e) := by
    intro i hi
    rw [Finset.mem_erase] at hi ⊢
    exact ⟨fun h => hi.1 (hκ h), hSU i hi.2⟩
  have := rch_tr ends endsW ι κ hι hends hSS hr
  apply hU (κ e) (hSU e he) (ι a) (ι b) _ this
  rw [← hends e, hab, Sym2.map_mk]

end Transport

/-! ### The core step -/

/-- the existential part of Lemma 4.2, as a hypothesis -/
def Shortens (C_D : ℝ) : Prop :=
  ∀ (N m' d' : ℕ), 1 ≤ N → 1 ≤ d' →
  ∀ (endsW : Fin m' → Sym2 (Fin N)) (T : Edges m') (X : Finset (Fin N)) (D : Direction N m'),
    Simple endsW → IsSpanningTree endsW T → Orients endsW (Finset.univ \ T) D →
    (∀ v, v ∉ X → d' ≤ outdegree (Finset.univ \ T) D v) →
    ∃ (Q : Edges m') (D' : Direction N m'), IsSpanningTree endsW Q ∧
      Orients endsW (Finset.univ \ Q) D' ∧
      diameter endsW Q ≤ ENNReal.ofReal (C_D * (X.card + (N : ℝ) / d')) ∧
      ∀ v, outdegree (Finset.univ \ Q) D' v = outdegree (Finset.univ \ T) D v

theorem core_step (C_D : ℝ) (H42 : Shortens C_D)
    (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (U : Edges m) (R1 : Fin n → Edges m)
    (W B : Finset (Fin n)) (d' : ℕ) (hd' : 1 ≤ d')
    (hU : IsSpanningTree ends U) (hR1 : OwnerReserves ends R1)
    (hUR1 : ∀ v, Disjoint U (R1 v)) (hBW : B ⊆ W) (hWne : W.Nonempty)
    (hpend : ∀ x, x ∉ W → ∃ f ∈ U, ∃ a ∈ W, ends f = s(x, a) ∧ ∀ g ∈ U, x ∈ ends g → g = f)
    (hres : ∀ v ∈ W, v ∉ B → d' ≤ ((R1 v).filter fun e => ∀ y ∈ ends e, y ∈ W).card) :
    ∃ (Q : Edges m) (R' : Fin n → Edges m), IsSpanningTree ends Q ∧ OwnerReserves ends R' ∧
      (∀ v, Disjoint Q (R' v)) ∧
      Q ∪ Finset.univ.biUnion R' = U ∪ Finset.univ.biUnion R1 ∧
      (∀ v, (R' v).card = (R1 v).card) ∧
      diameter ends Q ≤ ENNReal.ofReal (C_D * (B.card + (W.card : ℝ) / d')) + 2 ∧
      internal ends Q ⊆ W := by
  have hN : 0 < W.card := Finset.card_pos.2 hWne
  obtain ⟨w0, -⟩ := hWne
  -- vertex transport `ι : Fin N → W`
  set N := W.card with hNdef
  set eW : W ≃ Fin N := W.equivFin with heW
  set ι : Fin N → Fin n := fun i => (eW.symm i).1 with hιdef
  have hιinj : Function.Injective ι := fun i j h => eW.symm.injective (Subtype.ext h)
  have hιW : ∀ i, ι i ∈ W := fun i => (eW.symm i).2
  set gW : Fin n → Fin N := fun x => if hx : x ∈ W then eW ⟨x, hx⟩ else ⟨0, hN⟩ with hgWdef
  have hιg : ∀ x ∈ W, ι (gW x) = x := by
    intro x hx
    simp only [hgWdef, hιdef, dif_pos hx, Equiv.symm_apply_apply]
  have hgι : ∀ i, gW (ι i) = i := fun i => hιinj (hιg _ (hιW i))
  -- edge transport `κ : Fin m' → Ecore`
  set inW : Fin m → Prop := fun e => ∀ y ∈ ends e, y ∈ W with hinW
  set P := U ∪ Finset.univ.biUnion R1 with hP
  set Ecore := P.filter inW with hEcore
  set m' := Ecore.card with hm'
  set eE : Ecore ≃ Fin m' := Ecore.equivFin with heE
  set κ : Fin m' → Fin m := fun i => (eE.symm i).1 with hκdef
  have hκinj : Function.Injective κ := fun i j h => eE.symm.injective (Subtype.ext h)
  have hκE : ∀ i, κ i ∈ Ecore := fun i => (eE.symm i).2
  have hκsurj : ∀ e ∈ Ecore, ∃ i, κ i = e := fun e he => ⟨eE ⟨e, he⟩, by simp [hκdef]⟩
  have hκP : ∀ i, κ i ∈ P := fun i => (Finset.mem_filter.1 (hκE i)).1
  have hκW : ∀ i, inW (κ i) := fun i => (Finset.mem_filter.1 (hκE i)).2
  set endsW : Fin m' → Sym2 (Fin N) := fun i => Sym2.map gW (ends (κ i)) with hendsW
  have hmapback : ∀ z : Sym2 (Fin n), (∀ y ∈ z, y ∈ W) → Sym2.map ι (Sym2.map gW z) = z := by
    intro z hz
    induction z using Sym2.ind with
    | _ x y =>
      rw [Sym2.map_mk, Sym2.map_mk, hιg x (hz x (Sym2.mem_mk_left x y)),
        hιg y (hz y (Sym2.mem_mk_right x y))]
  have hends : ∀ i, Sym2.map ι (endsW i) = ends (κ i) := fun i => hmapback _ (hκW i)
  have hsW : Simple endsW := simple_tr ends endsW ι κ hκinj hends hs
  -- pendant edges
  have hUP : U ⊆ P := Finset.subset_union_left
  have hUcard := tree_card ends hU
  have hpendcard : (U.filter fun e => ¬ inW e).card + N = n := by
    have h1 : (U.filter fun e => ¬ inW e).card = Wᶜ.card := by
      symm
      apply Finset.card_bij (fun x hx => (hpend x (Finset.mem_compl.1 hx)).choose)
      · intro x hx
        obtain ⟨hfU, a, ha, hfe, -⟩ := (hpend x (Finset.mem_compl.1 hx)).choose_spec
        rw [Finset.mem_filter]
        refine ⟨hfU, fun h => Finset.mem_compl.1 hx (h x ?_)⟩
        rw [hfe]; exact Sym2.mem_mk_left _ _
      · intro x hx y hy hxy
        obtain ⟨-, a, ha, hfe, -⟩ := (hpend x (Finset.mem_compl.1 hx)).choose_spec
        obtain ⟨-, b, hb, hge, -⟩ := (hpend y (Finset.mem_compl.1 hy)).choose_spec
        have : x ∈ ends (hpend y (Finset.mem_compl.1 hy)).choose := by
          rw [← hxy, hfe]; exact Sym2.mem_mk_left _ _
        rw [hge, Sym2.mem_iff] at this
        rcases this with h | h
        · exact h
        · exact absurd (h ▸ hb) (Finset.mem_compl.1 hx)
      · intro e he
        rw [Finset.mem_filter] at he
        obtain ⟨heU, hnW⟩ := he
        simp only [hinW, not_forall] at hnW
        obtain ⟨y, hy, hyW⟩ := hnW
        refine ⟨y, Finset.mem_compl.2 hyW, ?_⟩
        obtain ⟨-, -, -, -, huniq⟩ := (hpend y hyW).choose_spec
        exact (huniq e heU hy).symm
    rw [h1, Finset.card_compl, Fintype.card_fin]
    have : N ≤ n := by
      have := Finset.card_le_univ W; simpa using this
    omega
  -- the core tree
  set TW : Finset (Fin m') := Finset.univ.filter fun i => κ i ∈ U with hTW
  have hTWimg : TW.image κ = U.filter inW := by
    ext e
    simp only [Finset.mem_image, hTW, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨hi, hκW i⟩
    · rintro ⟨heU, heW⟩
      obtain ⟨i, rfl⟩ := hκsurj e (Finset.mem_filter.2 ⟨hUP heU, heW⟩)
      exact ⟨i, heU, rfl⟩
  have hTWcard : TW.card + 1 = N := by
    have h1 : TW.card = (U.filter inW).card := by
      rw [← hTWimg, Finset.card_image_of_injective _ hκinj]
    have h2 := Finset.card_filter_add_card_filter_not (s := U) inW
    omega
  have hTWforest : IsForest endsW TW := forest_tr ends endsW ι κ hιinj hκinj hends
    (fun i hi => (Finset.mem_filter.1 hi).2) hU.2.2.2.1
  have hTWtree : IsSpanningTree endsW TW := tree_of_forest endsW hsW hN TW hTWforest hTWcard
  -- the orientation of the core reserve edges away from their owners
  set ori : Fin m → Fin n × Fin n := fun e =>
    if h : ∃ p : Fin n × Fin n, e ∈ R1 p.1 ∧ ends e = s(p.1, p.2) then h.choose else (w0, w0)
    with hori
  have hori_spec : ∀ e v, e ∈ R1 v → (ori e).1 = v ∧ ends e = s(v, (ori e).2) := by
    intro e v hev
    have hex : ∃ p : Fin n × Fin n, e ∈ R1 p.1 ∧ ends e = s(p.1, p.2) := by
      obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 (hR1.1 v e hev)
      exact ⟨(v, b), hev, hb⟩
    have hs' := hex.choose_spec
    have h1 : ori e = hex.choose := by simp only [hori, dif_pos hex]
    rw [h1]
    have hv : hex.choose.1 = v := own_eq hR1 hs'.1 hev
    refine ⟨hv, ?_⟩
    rw [← hv]; exact hs'.2
  set DW : Direction N m' := fun i => (gW (ori (κ i)).1, gW (ori (κ i)).2) with hDW
  have hnotU : ∀ i, i ∉ TW → ∃ v, κ i ∈ R1 v := by
    intro i hi
    have hiU : κ i ∉ U := fun h => hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rcases Finset.mem_union.1 (hκP i) with h | h
    · exact absurd h hiU
    · obtain ⟨v, -, hv⟩ := Finset.mem_biUnion.1 h; exact ⟨v, hv⟩
  have hOri : Orients endsW (Finset.univ \ TW) DW := by
    intro i hi
    obtain ⟨v, hv⟩ := hnotU i (Finset.mem_sdiff.1 hi).2
    obtain ⟨h1, h2⟩ := hori_spec (κ i) v hv
    simp only [hendsW, hDW, h2, h1, Sym2.map_mk]
  have houtW : ∀ w, ((Finset.univ \ TW).filter fun i => (DW i).1 = w).image κ
      = (R1 (ι w)).filter inW := by
    intro w
    ext e
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, ⟨hiT, hiw⟩, rfl⟩
      obtain ⟨v, hv⟩ := hnotU i hiT
      obtain ⟨h1, -⟩ := hori_spec (κ i) v hv
      have hvW : v ∈ W := hκW i v (hR1.1 v _ hv)
      have : v = ι w := by
        rw [← hiw]; simp only [hDW]; rw [h1, hιg v hvW]
      exact ⟨this ▸ hv, hκW i⟩
    · rintro ⟨heR, heW⟩
      have heP : e ∈ P :=
        Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨ι w, Finset.mem_univ _, heR⟩)
      obtain ⟨i, rfl⟩ := hκsurj e (Finset.mem_filter.2 ⟨heP, heW⟩)
      refine ⟨i, ⟨fun hi => ?_, ?_⟩, rfl⟩
      · exact Finset.disjoint_left.1 (hUR1 (ι w)) (Finset.mem_filter.1 hi).2 heR
      · obtain ⟨h1, -⟩ := hori_spec (κ i) (ι w) heR
        simp only [hDW]; rw [h1, hgι]
  have hout : ∀ w, outdegree (Finset.univ \ TW) DW w = ((R1 (ι w)).filter inW).card := by
    intro w; unfold outdegree; rw [← houtW w, Finset.card_image_of_injective _ hκinj]
  -- the exceptional set
  set X : Finset (Fin N) := Finset.univ.filter fun i => ι i ∈ B with hX
  have hXcard : X.card = B.card := by
    have : X.image ι = B := by
      ext b
      simp only [Finset.mem_image, hX, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hb; exact ⟨gW b, by rw [hιg b (hBW hb)]; exact hb, hιg b (hBW hb)⟩
    rw [← this, Finset.card_image_of_injective _ hιinj]
  have hdeg : ∀ w, w ∉ X → d' ≤ outdegree (Finset.univ \ TW) DW w := by
    intro w hw
    rw [hout]
    exact hres (ι w) (hιW w) (fun h => hw (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
  obtain ⟨QW, D', hQW, hOriQ, hdiam, hdegQ⟩ :=
    H42 N m' d' hN hd' endsW TW X DW hsW hTWtree hOri hdeg
  rw [hXcard] at hdiam
  -- the new tree and reserves
  set Pend := U.filter fun e => ¬ inW e with hPend
  set Q := QW.image κ ∪ Pend with hQ
  set R' : Fin n → Edges m := fun v =>
    ((Finset.univ \ QW).filter fun i => ι (D' i).1 = v).image κ ∪
      (R1 v).filter fun e => ¬ inW e with hR'
  have hD'ends : ∀ i, i ∉ QW → ends (κ i) = s(ι (D' i).1, ι (D' i).2) := by
    intro i hi
    rw [← hends i, hOriQ i (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hi⟩), Sym2.map_mk]
  have hmemR' : ∀ v e, e ∈ R' v ↔
      (∃ i, i ∉ QW ∧ ι (D' i).1 = v ∧ κ i = e) ∨ (e ∈ R1 v ∧ ¬ inW e) := by
    intro v e
    simp only [hR', Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and, and_assoc]
  have hmemQ : ∀ e, e ∈ Q ↔ (∃ i, i ∈ QW ∧ κ i = e) ∨ (e ∈ U ∧ ¬ inW e) := by
    intro e
    simp only [hQ, hPend, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  have hQWcard := tree_card endsW hQW
  have hdisjQ : Disjoint (QW.image κ) Pend := by
    rw [Finset.disjoint_left]; intro e he1 he2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 he1
    exact (Finset.mem_filter.1 he2).2 (hκW i)
  have hQcard : Q.card + 1 = n := by
    rw [hQ, Finset.card_union_of_disjoint hdisjQ, Finset.card_image_of_injective _ hκinj]
    omega
  have hQWsub : ∀ i ∈ QW, κ i ∈ Q := fun i hi =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem κ hi)
  have hproj : ∀ x, ∃ y ∈ W, (x = y ∨ (edgeGraph ends Q).Adj x y) := by
    intro x
    by_cases hx : x ∈ W
    · exact ⟨x, hx, Or.inl rfl⟩
    · obtain ⟨f, hfU, a, ha, hfe, -⟩ := hpend x hx
      refine ⟨a, ha, Or.inr ?_⟩
      rw [adj_iff]
      refine ⟨⟨f, Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hfU, fun h => hx (h x ?_)⟩),
        hfe⟩, fun h => hx (h ▸ ha)⟩
      rw [hfe]; exact Sym2.mem_mk_left _ _
  have hconnW : ∀ a ∈ W, ∀ b ∈ W, Rch ends Q a b := by
    intro a ha b hb
    have := rch_tr ends endsW ι κ hιinj hends hQWsub (connected_of_tree endsW hQW (gW a) (gW b))
    rwa [hιg a ha, hιg b hb] at this
  have hQtree : IsSpanningTree ends Q := by
    apply tree_of_conn ends hs (by omega) Q _ hQcard
    intro x y
    obtain ⟨x', hx', hxx⟩ := hproj x
    obtain ⟨y', hy', hyy⟩ := hproj y
    have h1 : Rch ends Q x x' := by
      rcases hxx with h | h
      · rw [h]
      · exact h.reachable
    have h2 : Rch ends Q y y' := by
      rcases hyy with h | h
      · rw [h]
      · exact h.reachable
    exact h1.trans ((hconnW x' hx' y' hy').trans h2.symm)
  refine ⟨Q, R', hQtree, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- owners are ends
    intro v e he
    rcases (hmemR' v e).1 he with ⟨i, hi, hiv, rfl⟩ | ⟨heR, -⟩
    · rw [hD'ends i hi, ← hiv]; exact Sym2.mem_mk_left _ _
    · exact hR1.1 v e heR
  · -- reserves are disjoint
    intro v w hvw
    rw [Finset.disjoint_left]
    intro e hv hw
    rcases (hmemR' v e).1 hv with ⟨i, hi, hiv, rfl⟩ | ⟨heR, heW⟩ <;>
      rcases (hmemR' w _).1 hw with ⟨j, hj, hjw, hji⟩ | ⟨heR', heW'⟩
    · have := hκinj hji; subst this; exact hvw (hiv.symm.trans hjw)
    · exact heW' (hκW i)
    · rw [← hji] at heW; exact heW (hκW j)
    · exact Finset.disjoint_left.1 (hR1.2 v w hvw) heR heR'
  · -- the tree avoids the reserves
    intro v
    rw [Finset.disjoint_left]
    intro e hQe hRe
    rcases (hmemQ e).1 hQe with ⟨i, hi, rfl⟩ | ⟨heU, heW⟩ <;>
      rcases (hmemR' v _).1 hRe with ⟨j, hj, -, hji⟩ | ⟨heR, heW'⟩
    · have := hκinj hji; subst this; exact hj hi
    · exact heW' (hκW i)
    · rw [← hji] at heW; exact heW (hκW j)
    · exact Finset.disjoint_left.1 (hUR1 v) heU heR
  · -- the union is unchanged
    show Q ∪ Finset.univ.biUnion R' = U ∪ Finset.univ.biUnion R1
    ext e
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro (hQe | ⟨v, hRe⟩)
      · rcases (hmemQ e).1 hQe with ⟨i, -, rfl⟩ | ⟨heU, -⟩
        · rcases Finset.mem_union.1 (hκP i) with h | h
          · exact Or.inl h
          · obtain ⟨v, -, hv⟩ := Finset.mem_biUnion.1 h; exact Or.inr ⟨v, hv⟩
        · exact Or.inl heU
      · rcases (hmemR' v e).1 hRe with ⟨i, -, -, rfl⟩ | ⟨heR, -⟩
        · rcases Finset.mem_union.1 (hκP i) with h | h
          · exact Or.inl h
          · obtain ⟨v, -, hv⟩ := Finset.mem_biUnion.1 h; exact Or.inr ⟨v, hv⟩
        · exact Or.inr ⟨v, heR⟩
    · intro he
      have heP : e ∈ P := by
        rcases he with he | ⟨v, hv⟩
        · exact Finset.mem_union_left _ he
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _, hv⟩)
      by_cases heW : inW e
      · obtain ⟨i, rfl⟩ := hκsurj _ (Finset.mem_filter.2 ⟨heP, heW⟩)
        by_cases hi : i ∈ QW
        · exact Or.inl ((hmemQ _).2 (Or.inl ⟨i, hi, rfl⟩))
        · exact Or.inr ⟨ι (D' i).1, (hmemR' _ _).2 (Or.inl ⟨i, hi, rfl, rfl⟩)⟩
      · rcases he with he | ⟨v, hv⟩
        · exact Or.inl ((hmemQ _).2 (Or.inr ⟨he, heW⟩))
        · exact Or.inr ⟨v, (hmemR' _ _).2 (Or.inr ⟨hv, heW⟩)⟩
  · -- reserve sizes
    intro v
    have hdisj : Disjoint (((Finset.univ \ QW).filter fun i => ι (D' i).1 = v).image κ)
        ((R1 v).filter fun e => ¬ inW e) := by
      rw [Finset.disjoint_left]; intro e he1 he2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 he1
      exact (Finset.mem_filter.1 he2).2 (hκW i)
    have hA1 : (((Finset.univ \ QW).filter fun i => ι (D' i).1 = v).image κ).card
        = ((R1 v).filter inW).card := by
      rw [Finset.card_image_of_injective _ hκinj]
      by_cases hv : v ∈ W
      · have hfil : ((Finset.univ \ QW).filter fun i => ι (D' i).1 = v)
            = (Finset.univ \ QW).filter fun i => (D' i).1 = gW v := by
          apply Finset.filter_congr
          intro i _
          constructor
          · intro h; rw [← h, hgι]
          · intro h; rw [h, hιg v hv]
        have := hdegQ (gW v)
        unfold outdegree at this
        rw [hfil, this, ← outdegree, hout, hιg v hv]
      · have h1 : ((Finset.univ \ QW).filter fun i => ι (D' i).1 = v) = ∅ := by
          apply Finset.filter_false_of_mem
          intro i _ h; exact hv (h ▸ hιW _)
        have h2 : (R1 v).filter inW = ∅ := by
          apply Finset.filter_false_of_mem
          intro e he h; exact hv (h v (hR1.1 v e he))
        rw [h1, h2, Finset.card_empty, Finset.card_empty]
    have := Finset.card_filter_add_card_filter_not (s := R1 v) inW
    show (R' v).card = _
    rw [hR', Finset.card_union_of_disjoint hdisj, hA1]
    exact this
  · -- diameter
    have hdistW : ∀ a ∈ W, ∀ b ∈ W, distance ends Q a b ≤ diameter endsW QW := by
      intro a ha b hb
      have := dist_tr ends endsW ι κ hιinj hends hQWsub (gW a) (gW b)
      rw [hιg a ha, hιg b hb] at this
      exact this.trans (le_iSup₂ (f := fun u v => distance endsW QW u v) (gW a) (gW b))
    have hstep : ∀ x v, ∃ x' ∈ W, distance ends Q x v ≤ distance ends Q x' v + 1 := by
      intro x v
      obtain ⟨x', hx', hxx⟩ := hproj x
      refine ⟨x', hx', ?_⟩
      rcases hxx with h | h
      · rw [h]; exact le_self_add
      · exact dist_adj ends Q h v
    unfold diameter
    refine iSup₂_le fun u v => ?_
    obtain ⟨u', hu', h1⟩ := hstep u v
    obtain ⟨v', hv', h2⟩ := hstep v u'
    rw [dist_symm ends Q v u'] at h2
    calc distance ends Q u v ≤ distance ends Q u' v + 1 := h1
      _ ≤ (distance ends Q v' u' + 1) + 1 := by gcongr
      _ ≤ (diameter endsW QW + 1) + 1 := by gcongr; exact hdistW v' hv' u' hu'
      _ = diameter endsW QW + 2 := by rw [add_assoc, one_add_one_eq_two]
      _ ≤ _ := by gcongr
  · -- internal vertices lie in the core
    intro x hx
    by_contra hxW
    rw [internal, Finset.mem_filter] at hx
    obtain ⟨f, -, -, -, -, huniq⟩ := hpend x hxW
    have key : ∀ g, g ∈ Q → x ∈ ends g → g = f := by
      intro g hg hxg
      rcases (hmemQ g).1 hg with ⟨i, -, rfl⟩ | ⟨hgU, -⟩
      · exact absurd (hκW i x hxg) hxW
      · exact huniq g hgU hxg
    have : degIn ends Q x ≤ 1 := by
      unfold degIn
      apply Finset.card_le_one.2
      intro e he e' he'
      rw [Finset.mem_filter] at he he'
      rw [key e he.1 he.2, key e' he'.1 he'.2]
    omega

end LowDiameterNashWilliams.Main.Dev.L41
end

section
/-!
# Lemma 4.1 (shortening one receiving tree), as a reduction to Lemma 4.2

Only the existential first conjunct of `lemma_4_2` is used (`Shortens C_D`). Constant:
`C := 4 C_D + 2`. Write `a = |A|`, `b = |B|`, `x = b + a/d`, `P = E(T) ∪ ⋃_v R_v`.

**Merging forest (L41C `exists_maxF`).** Among the sets `F` of reserve edges such that
(i) every `f ∈ F` lies in `R_v` for an owner `v` and joins `v` to a vertex of `A`,
(ii) every vertex owns at most one edge of `F`, and (iii) some height `h : V → ℕ` satisfies
`h(other end) < h(owner)` for every `f ∈ F`, take one of maximum size. Maximality: if `r`
owns no edge of `F` and `e ∈ R_r` joins `r` to `a ∈ A`, then `F` connects `r` and `a`
(otherwise `F + e` satisfies (i)–(iii): lift the heights of the component of `r` by
`h(a) + 1`).

**Counting.** Along a path of `F` starting at a non-owner each edge is owned by its far end
(`path_owner`), so two non-owners are never connected by `F` (`nonowner_not_rch`). The
`A`-neighbourhoods `Nb(r)` (at least `d` vertices, by simplicity, `nb_card`) of the
non-owners `r ∉ B` are therefore pairwise disjoint subsets of `A`, so the number `c` of
non-owners satisfies `d c ≤ d b + a`, and `|F| = n − c` (`card_F_add`). Every vertex outside
`A ∪ B` owns an edge of `F` (its reserve has an `A`-neighbour, which `F` reaches).

**Exchanges (L41B `insert_all`).** Insert `F` into `T` edge by edge, always the edge of a
highest owner `v` (whose only `F`-edge is then its own): add it, delete the first edge `g` at
`v` of the tree path to its other end (`tree_exchange`) and put `g` into `R_v`. This keeps a
spanning tree, every `|R_v|`, the union `P`, and `R_v ∖ F ⊆ R'_v`; `F ⊆ U` at the end.

**Core (L41C `prepare`).** `D` = ends of the `c − 1` edges of `U ∖ F`, `W = A ∪ B ∪ D`,
so `|W ∖ (A ∪ B)| ≤ 2c − 2`. A vertex outside `W` is a leaf of `U` whose edge (its own
`F`-edge) goes to `A`. Each `v ∈ W ∖ B` keeps `≥ d − 1` reserve edges to `A`, all inside `W`.

**Shortening (L41D `core_step`).** Transport the multigraph `(W, P[W])` to `Fin N`,
`Fin m'` (`N = |W|`). The core tree `U[W]` is a forest with `N − 1` edges, hence a spanning
tree; orient each core reserve edge away from its owner. Lemma 4.2 with `X = B`,
`d' = d − 1` gives `Q_W` and `D'` with equal outdegrees and
`diam(Q_W) ≤ C_D (b + N/(d − 1))`. Put `Q = Q_W ∪ (pendant edges)`, `R'_v` = core non-tree
edges with tail `v` plus `R1_v ∖ P[W]`. Pendant vertices add at most `2` to distances, and
every internal vertex of `Q` lies in `W`.

**Arithmetic.** `c ≤ b + a/d`, `N ≤ a + b + 2c ≤ a + 3b + 2a/d`, and
`N ≤ (3b + 4a/d)(d − 1)` because `3(b + a/d)(d − 2) ≥ 0`, so
`diam(Q) ≤ C_D (4b + 4a/d) + 2 ≤ (4 C_D + 2) x` using `x ≥ 1` (if `B = ∅`, any vertex has `d`
distinct reserve neighbours in `A`, so `a ≥ d`); and `|int(Q) ∖ (A ∪ B)| ≤ 2c − 2 ≤ 2x`.
-/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main
open LowDiameterNashWilliams.Main.Dev.L41 in
theorem chk_lemma_4_1 :
  ∃ C : ℝ, 0 < C ∧ ∀ n m d : ℕ, 2 ≤ n → 2 ≤ d →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Edges m) (R : Fin n → Edges m)
    (A B : Finset (Fin n)), Simple ends → IsSpanningTree ends T →
  OwnerReserves ends R → (∀ v, Disjoint T (R v)) →
  (∀ v, v ∉ B → d ≤ reserveNeighbors ends R v A) →
  ∃ (Q : Edges m) (R' : Fin n → Edges m), IsSpanningTree ends Q ∧
    OwnerReserves ends R' ∧ (∀ v, Disjoint Q (R' v)) ∧
    Q ∪ Finset.univ.biUnion R' = T ∪ Finset.univ.biUnion R ∧
    (∀ v, (R' v).card = (R v).card) ∧
    diameter ends Q ≤ ENNReal.ofReal (C * (B.card + (A.card : ℝ) / d)) ∧
    (((internal ends Q \ (A ∪ B)).card : ℕ) : ℝ) ≤ 2 * (B.card + (A.card : ℝ) / d) := by
  obtain ⟨C_D, C_T, hCD, -, c, -, P, h42⟩ := lemma_4_2
  have H42 : Shortens C_D := fun N m' d' hN hd' endsW T X D hs hT hD hout =>
    (h42 N m' d' hN hd' endsW T X D hs hT hD hout).1
  refine ⟨4 * C_D + 2, by positivity, ?_⟩
  intro n m d hn hd ends T R A B hs hT hR hTR hN
  obtain ⟨U, R1, W, c0, hU, hR1, hUR1, hun, hcard, hABW, hpend, hres, hWsize, hcount⟩ :=
    prepare ends hs T R hT hR hTR A B d (by omega) hN
  -- if `B = ∅` then `|A| ≥ d`
  have hAd : B = ∅ → d ≤ A.card := by
    intro hB
    have h1 := (hN ⟨0, by omega⟩ (by simp [hB])).trans (nb_card ends hs R A _)
    exact h1.trans (Finset.card_le_card (nb_sub ends R A _))
  have hWne : W.Nonempty := by
    rcases B.eq_empty_or_nonempty with hB | ⟨b, hb⟩
    · obtain ⟨a, ha⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) (hAd hB))
      exact ⟨a, hABW (Finset.mem_union_left _ ha)⟩
    · exact ⟨b, hABW (Finset.mem_union_right _ hb)⟩
  obtain ⟨Q, R', hQ, hR', hQR', hun', hcard', hdiam, hint⟩ :=
    core_step C_D H42 ends hs U R1 W B (d - 1) (by omega) hU hR1 hUR1
      (fun x hx => hABW (Finset.mem_union_right _ hx)) hWne hpend hres
  refine ⟨Q, R', hQ, hR', hQR', hun'.trans hun, fun v => (hcard' v).trans (hcard v), ?_, ?_⟩
  -- arithmetic
  all_goals
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
    have hd2 : (2 : ℝ) ≤ d := Nat.ofNat_le_cast.2 hd
    set q : ℝ := (A.card : ℝ) / d with hq
    have hqa : (A.card : ℝ) = q * d := by rw [hq, div_mul_cancel₀ _ hdpos.ne']
    have hq0 : 0 ≤ q := div_nonneg (Nat.cast_nonneg _) hdpos.le
    have hb0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
    have hc0 : (c0 : ℝ) ≤ B.card + q := by
      have h1 : (d : ℝ) * c0 ≤ d * B.card + A.card := by exact_mod_cast hcount
      rw [hqa] at h1
      nlinarith
    have hWs : ((W \ (A ∪ B)).card : ℝ) + 2 ≤ 2 * c0 := by exact_mod_cast hWsize
    have hx1 : (1 : ℝ) ≤ B.card + q := by
      rcases B.eq_empty_or_nonempty with hB | hB
      · have h1 : (d : ℝ) ≤ A.card := by exact_mod_cast hAd hB
        rw [hqa] at h1
        have : (1 : ℝ) ≤ q := by nlinarith
        linarith
      · have : (1 : ℝ) ≤ B.card := by exact_mod_cast Finset.card_pos.2 hB
        linarith
  · -- diameter
    have hWc : (W.card : ℝ) ≤ A.card + B.card + (W \ (A ∪ B)).card := by
      have h1 : W.card ≤ (W \ (A ∪ B)).card + (A ∪ B).card :=
        Finset.card_le_card_sdiff_add_card
      have h2 := Finset.card_union_le A B
      have : W.card ≤ A.card + B.card + (W \ (A ∪ B)).card := by omega
      exact_mod_cast this
    have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hkey : (W.card : ℝ) / ((d - 1 : ℕ) : ℝ) ≤ 3 * B.card + 4 * q := by
      rw [hd1, div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ d - 2 by linarith) (add_nonneg hb0 hq0)]
    have hy0 : 0 ≤ C_D * (B.card + (W.card : ℝ) / ((d - 1 : ℕ) : ℝ)) :=
      mul_nonneg hCD.le (add_nonneg hb0 (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    refine hdiam.trans ?_
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_add hy0 (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have : C_D * (B.card + (W.card : ℝ) / ((d - 1 : ℕ) : ℝ)) ≤ C_D * (4 * (B.card + q)) :=
      mul_le_mul_of_nonneg_left (by linarith) hCD.le
    nlinarith
  · -- internal vertices
    have h1 : internal ends Q \ (A ∪ B) ⊆ W \ (A ∪ B) := Finset.sdiff_subset_sdiff hint le_rfl
    have h2 : ((internal ends Q \ (A ∪ B)).card : ℝ) ≤ (W \ (A ∪ B)).card := by
      exact_mod_cast Finset.card_le_card h1
    linarith

end LowDiameterNashWilliams.Main
end

theorem solution : type_of% @LowDiameterNashWilliams.Main.chk_lemma_4_1 := @LowDiameterNashWilliams.Main.chk_lemma_4_1
