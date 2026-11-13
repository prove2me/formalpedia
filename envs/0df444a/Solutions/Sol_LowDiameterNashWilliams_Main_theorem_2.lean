-- Prove2me | solution 1 for LowDiameterNashWilliams.Main.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T19:47:26.837642+00:00
-- url     : https://prove2.me/submissions/30fcc21e-0636-412f-b6a7-309ac0f74d83

import Mathlib
import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Definitions.Def_LowDiameterNashWilliams_Main_Geometry
import Definitions.Def_LowDiameterNashWilliams_Main_Reserves
import Definitions.Def_LowDiameterNashWilliams_Main_Sampling
import Definitions.Def_LowDiameterNashWilliams_Main_Computation
import Theorems.Thm_LowDiameterNashWilliams_Main_lemma_3_1

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
/-! Theorem 2, part A: every spanning tree has an orientation toward a given root, and the
transport of spanning trees, degrees and orientations along an embedding `Fin m' ↪ Fin m`
of the edge identities (used to apply Lemma 3.1 to the subgraph of remaining edges). -/

set_option autoImplicit false
open Classical
open scoped BigOperators
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.T2
open LowDiameterNashWilliams.Main
open LowDiameterNashWilliams.Main.Dev.L33

variable {n m : ℕ}

/-! ### Orientation toward a root -/

/-- a chosen ordered pair of ends of `e` -/
noncomputable def endsPair (ends : Fin m → Sym2 (Fin n)) (e : Fin m) : Fin n × Fin n :=
  (Classical.choose (exists_ends ends e),
    Classical.choose (Classical.choose_spec (exists_ends ends e)))

theorem endsPair_spec (ends : Fin m → Sym2 (Fin n)) (e : Fin m) :
    ends e = s((endsPair ends e).1, (endsPair ends e).2) :=
  Classical.choose_spec (Classical.choose_spec (exists_ends ends e))

/-- orient every edge away from the end farther from `r` (ties: first chosen end) -/
noncomputable def orientTo (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) (r : Fin n) :
    Direction n m := fun e =>
  if (edgeGraph ends F).dist (endsPair ends e).2 r ≤ (edgeGraph ends F).dist (endsPair ends e).1 r
  then ((endsPair ends e).1, (endsPair ends e).2)
  else ((endsPair ends e).2, (endsPair ends e).1)

theorem orientTo_orients (ends : Fin m → Sym2 (Fin n)) (F : Finset (Fin m)) (r : Fin n) :
    Orients ends F (orientTo ends F r) := by
  intro e _
  unfold orientTo
  split_ifs
  · exact endsPair_spec ends e
  · rw [endsPair_spec ends e]; exact Sym2.eq_swap

theorem outdegree_sum (F : Finset (Fin m)) (D : Direction n m) :
    ∑ v, outdegree F D v = F.card := by
  unfold outdegree
  exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ ((D x).1))).symm

theorem exists_toward (ends : Fin m → Sym2 (Fin n)) {F : Finset (Fin m)}
    (hF : IsSpanningTree ends F) (r : Fin n) : ∃ D, Toward ends F D r := by
  set G := edgeGraph ends F with hG
  have hreach : ∀ a b, G.Reachable a b := fun a b => connected_of_tree ends hF a b
  have hfor : IsForest ends F := hF.2.2.2.1
  set D := orientTo ends F r with hD
  have hr0 : outdegree F D r = 0 := by
    unfold outdegree
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he htail
    have hnd := LowDiameterNashWilliams.Dev.Forest.forest_nondiag ends hfor e he
    have hsp := endsPair_spec ends e
    simp only [hD, orientTo] at htail
    split_ifs at htail with h
    · simp only at htail
      rw [htail] at h
      simp only [SimpleGraph.dist_self, nonpos_iff_eq_zero] at h
      rw [(hreach _ _).dist_eq_zero_iff] at h
      apply hnd; rw [hsp, h, htail]; simp
    · simp only at htail
      rw [htail] at h
      simp at h
  have hpos : ∀ v, v ≠ r → 1 ≤ outdegree F D v := by
    intro v hv
    obtain ⟨p, hp⟩ := (hreach v r).exists_walk_length_eq_dist
    cases p with
    | nil => exact absurd rfl hv
    | @cons _ u _ hadj q =>
      obtain ⟨⟨e, he, heq⟩, -⟩ := (adj_iff ends F v u).1 hadj
      have hlen : G.dist u r < G.dist v r := by
        have := SimpleGraph.dist_le q
        simp only [SimpleGraph.Walk.length_cons] at hp
        omega
      unfold outdegree
      apply Finset.card_pos.2
      refine ⟨e, Finset.mem_filter.2 ⟨he, ?_⟩⟩
      have hsp := endsPair_spec ends e
      rw [heq, Sym2.eq_iff] at hsp
      simp only [hD, orientTo]
      rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_pos (by rw [← h1, ← h2]; exact hlen.le)]; exact h1.symm
      · rw [if_neg (by rw [← h1, ← h2]; exact not_le.2 hlen)]; exact h1.symm
  refine ⟨D, orientTo_orients ends F r, hr0, ?_⟩
  have hsum := outdegree_sum F D
  have hcard := tree_card ends hF
  have hsplit := Finset.add_sum_erase Finset.univ (outdegree F D) (Finset.mem_univ r)
  rw [hsum, hr0, zero_add] at hsplit
  have hc : (Finset.univ.erase r).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  intro v hv
  by_contra hne
  have h2 : 1 < outdegree F D v := by have := hpos v hv; omega
  have hlt : ∑ w ∈ Finset.univ.erase r, (1 : ℕ) < ∑ w ∈ Finset.univ.erase r, outdegree F D w :=
    Finset.sum_lt_sum (fun w hw => hpos w (Finset.ne_of_mem_erase hw))
      ⟨v, Finset.mem_erase.2 ⟨hv, Finset.mem_univ _⟩, h2⟩
  rw [Finset.sum_const, smul_eq_mul, mul_one, hc, hsplit] at hlt
  omega

/-! ### Transport along an embedding of edge identities -/

section Transport

variable {m' : ℕ} (ends : Fin m → Sym2 (Fin n)) (emb : Fin m' ↪ Fin m)

theorem edgeGraph_comp (F : Finset (Fin m')) :
    edgeGraph (ends ∘ emb) F = edgeGraph ends (F.map emb) := by
  unfold edgeGraph
  congr 1
  rw [Finset.coe_map, Set.image_comp]

theorem isForest_comp_iff (F : Finset (Fin m')) :
    IsForest (ends ∘ emb) F ↔ IsForest ends (F.map emb) := by
  constructor
  · intro h e he u v huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 he
    have := h x hx u v huv
    rwa [edgeGraph_comp, Finset.map_erase] at this
  · intro h x hx u v huv
    have := h (emb x) (Finset.mem_map_of_mem _ hx) u v huv
    rwa [edgeGraph_comp, Finset.map_erase]

theorem isSpanningTree_comp_iff (F : Finset (Fin m')) :
    IsSpanningTree (ends ∘ emb) F ↔ IsSpanningTree ends (F.map emb) := by
  unfold IsSpanningTree IsSpanningTreeOn IsTreeOn
  rw [isForest_comp_iff, edgeGraph_comp]
  simp

theorem degIn_comp (F : Finset (Fin m')) (v : Fin n) :
    degIn (ends ∘ emb) F v = degIn ends (F.map emb) v := by
  unfold degIn
  rw [Finset.filter_map, Finset.card_map]
  rfl

theorem internal_comp (F : Finset (Fin m')) :
    internal (ends ∘ emb) F = internal ends (F.map emb) := by
  unfold internal
  simp only [degIn_comp]

theorem card_filter_map (F : Finset (Fin m')) (p : Fin m → Prop) :
    ((F.map emb).filter p).card = (F.filter (fun x => p (emb x))).card := by
  rw [Finset.filter_map, Finset.card_map]
  rfl

/-- pull back an edge set along `emb` -/
noncomputable def pull (F : Finset (Fin m)) : Finset (Fin m') :=
  F.preimage emb (emb.injective.injOn)

theorem mem_pull (F : Finset (Fin m)) (x : Fin m') : x ∈ pull emb F ↔ emb x ∈ F := by
  unfold pull; simp

theorem map_pull {F R : Finset (Fin m)} (hR : ∀ e ∈ R, ∃ x, emb x = e) (hF : F ⊆ R) :
    (pull emb F).map emb = F := by
  ext e
  simp only [Finset.mem_map, mem_pull]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro he
    obtain ⟨x, rfl⟩ := hR e (hF he)
    exact ⟨x, he, rfl⟩

theorem simple_comp (hs : Simple ends) : Simple (ends ∘ emb) :=
  ⟨hs.1.comp emb.injective, fun e => hs.2 (emb e)⟩

end Transport

/-! ### Degrees in spanning trees -/

theorem deg_pos (ends : Fin m → Sym2 (Fin n)) (hn : 2 ≤ n) (Q : Edges m)
    (hQ : IsSpanningTree ends Q) (v : Fin n) : 1 ≤ degIn ends Q v := by
  obtain ⟨u, hu⟩ : ∃ u : Fin n, u ≠ v := by
    by_cases h : v = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h h'.symm⟩
  obtain ⟨p⟩ := hQ.2.2.2.2 v (Finset.mem_univ _) u (Finset.mem_univ _)
  cases p with
  | nil => exact absurd rfl hu
  | cons h _ =>
    obtain ⟨⟨e, he, heq⟩, -⟩ := (adj_iff ends Q _ _).1 h
    unfold degIn
    exact Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨he, by rw [heq]; simp⟩⟩

/-! ### A tree partition gives an extractable tree -/

theorem extractable_of_partition (ends : Fin m → Sym2 (Fin n)) {t : ℕ} (ht : 1 ≤ t)
    (T : Trees t m) (hT : TreePartition ends T) : Extractable ends t (T ⟨0, ht⟩) := by
  refine ⟨hT.1.1 _, fun l => T ⟨l.val + 1, by omega⟩, fun l => hT.1.1 _, ?_, ?_⟩
  · intro a b hab
    apply hT.1.2
    intro h; apply hab; ext; simp [Fin.ext_iff] at h; omega
  · ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · rintro ⟨l, hl⟩
      refine fun h0 => Finset.disjoint_left.1 (hT.1.2 ⟨l.val + 1, by omega⟩ ⟨0, ht⟩
        (by simp [Fin.ext_iff])) hl h0
    · intro h0
      have : e ∈ Finset.univ.biUnion T := by rw [hT.2]; exact Finset.mem_univ _
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 this
      have hj0 : j.val ≠ 0 := by
        intro h; apply h0; have : j = ⟨0, ht⟩ := Fin.ext h; rwa [← this]
      refine ⟨⟨j.val - 1, by omega⟩, ?_⟩
      have : (⟨j.val - 1 + 1, by omega⟩ : Fin t) = j := Fin.ext (by simp; omega)
      rw [this]; exact hj

end LowDiameterNashWilliams.Main.Dev.T2
end

section
/-! Theorem 2, part B: one extraction round.  The trees in slots `≥ i` of a tree partition `W`
are pulled back to the subgraph of remaining edges, Lemma 3.1 is applied there to the set
`L = A \ (heads of bad vertices)`, and the extracted tree is spliced back into slot `i`. -/

set_option autoImplicit false
open Classical
open scoped BigOperators
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.T2
open LowDiameterNashWilliams.Main
open LowDiameterNashWilliams.Main.Dev.L33

/-- the statement of Lemma 3.1 with constant `C` -/
def L31Stmt (C : ℝ) : Prop :=
  ∀ n m k : ℕ, 2 ≤ n → 1 ≤ k →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Trees k m)
    (D : Fin k → Direction n m) (r : Fin n) (L : Finset (Fin n)) (Q : Edges m),
  Simple ends → TreePartition ends T → (∀ i, Toward ends (T i) (D i) r) →
  (∀ v, (outgoingTo T D v L : ℝ) ≤ (k : ℝ) / 8) →
  Extractable ends k Q →
  (∀ U : Edges m, Extractable ends k U →
    weight (incidenceWeight ends L) Q ≤ weight (incidenceWeight ends L) U) →
    (((internal ends Q ∩ L).card : ℕ) : ℝ) ≤ C * ((n : ℝ) / k)

variable {n m k : ℕ}

/-! ### Extractable trees and partitions -/

theorem partition_of_extractable (ends : Fin m → Sym2 (Fin n)) {t : ℕ} (ht : 1 ≤ t)
    {Q : Edges m} (hQ : Extractable ends t Q) :
    ∃ V : Trees t m, TreePartition ends V ∧ V ⟨0, ht⟩ = Q := by
  obtain ⟨hQs, U, hUs, hUd, hUc⟩ := hQ
  have hU : ∀ l e, e ∈ U l → e ∉ Q := by
    intro l e he
    have : e ∈ Finset.univ.biUnion U := Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, he⟩
    rw [hUc] at this
    exact (Finset.mem_sdiff.1 this).2
  refine ⟨fun l => if h : l.val = 0 then Q else U ⟨l.val - 1, by omega⟩, ⟨⟨?_, ?_⟩, ?_⟩, by simp⟩
  · intro l
    by_cases h : l.val = 0
    · simp only [h, dite_true]; exact hQs
    · simp only [h, dite_false]; exact hUs _
  · intro a b hab
    by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
    · exact absurd (Fin.ext (ha.trans hb.symm)) hab
    · simp only [ha, hb, dite_true, dite_false]
      exact Finset.disjoint_left.2 fun e he he' => hU _ e he' he
    · simp only [ha, hb, dite_true, dite_false]
      exact Finset.disjoint_left.2 fun e he he' => hU _ e he he'
    · simp only [ha, hb, dite_false]
      apply hUd
      intro h; apply hab; ext; simp [Fin.ext_iff] at h; omega
  · ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
    by_cases he : e ∈ Q
    · exact ⟨⟨0, ht⟩, by simpa using he⟩
    · have : e ∈ Finset.univ.biUnion U := by rw [hUc]; simp [he]
      obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.1 this
      refine ⟨⟨l.val + 1, by omega⟩, ?_⟩
      simp only [Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]
      exact hl

/-! ### Splicing a partition of the remaining edges into the slots `≥ i` -/

section Splice

variable (ends : Fin m → Sym2 (Fin n)) (i : ℕ) {m' : ℕ} (emb : Fin m' ↪ Fin m)

/-- the edges in slots `≥ i` -/
noncomputable def rest (W : Trees k m) : Finset (Fin m) :=
  Finset.univ.filter fun e => ∃ j : Fin k, i ≤ j.val ∧ e ∈ W j

noncomputable def splice (W : Trees k m) {t : ℕ} (ht : t = k - i) (V : Trees t m') :
    Trees k m := fun j =>
  if h : j.val < i then W j else (V ⟨j.val - i, by omega⟩).map emb

theorem splice_lt (W : Trees k m) {t : ℕ} (ht : t = k - i) (V : Trees t m') (j : Fin k)
    (hj : j.val < i) : splice i emb W ht V j = W j := by
  simp [splice, hj]

theorem splice_eq (W : Trees k m) {t : ℕ} (ht : t = k - i) (V : Trees t m') (hi : i < k)
    (h0 : 0 < t) : splice i emb W ht V ⟨i, hi⟩ = (V ⟨0, h0⟩).map emb := by
  simp [splice]

theorem splice_partition {W : Trees k m} (hW : TreePartition ends W) {t : ℕ} (ht : t = k - i)
    {V : Trees t m'} (hV : TreePartition (ends ∘ emb) V)
    (hR : ∀ e, e ∈ rest i W ↔ ∃ x, emb x = e) :
    TreePartition ends (splice i emb W ht V) := by
  have hrest : ∀ x, ∃ j : Fin k, i ≤ j.val ∧ emb x ∈ W j := by
    intro x
    have := (hR (emb x)).2 ⟨x, rfl⟩
    simpa [rest] using this
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j
    by_cases h : j.val < i
    · rw [splice_lt _ _ _ _ _ _ h]; exact hW.1.1 j
    · simp only [splice, h, dite_false]
      exact (isSpanningTree_comp_iff ends emb _).1 (hV.1.1 _)
  · intro a b hab
    have key : ∀ a b : Fin k, a.val < i → ¬ b.val < i →
        Disjoint (splice i emb W ht V a) (splice i emb W ht V b) := by
      intro a b ha hb
      rw [splice_lt _ _ _ _ _ _ ha]
      simp only [splice, hb, dite_false]
      apply Finset.disjoint_left.2
      intro e he he'
      obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 he'
      obtain ⟨j, hj, hxj⟩ := hrest x
      have hja : j ≠ a := by intro h; subst h; omega
      exact Finset.disjoint_left.1 (hW.1.2 j a hja) hxj he
    by_cases ha : a.val < i <;> by_cases hb : b.val < i
    · rw [splice_lt _ _ _ _ _ _ ha, splice_lt _ _ _ _ _ _ hb]; exact hW.1.2 a b hab
    · exact key a b ha hb
    · exact (key b a hb ha).symm
    · simp only [splice, ha, hb, dite_false]
      rw [Finset.disjoint_map]
      apply hV.1.2
      intro h; apply hab; ext; simp [Fin.ext_iff] at h; omega
  · ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
    by_cases he : e ∈ rest i W
    · obtain ⟨x, rfl⟩ := (hR e).1 he
      have : x ∈ Finset.univ.biUnion V := by rw [hV.2]; exact Finset.mem_univ _
      obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.1 this
      refine ⟨⟨i + l.val, by omega⟩, ?_⟩
      simp only [splice, show ¬ (i + l.val < i) by omega, dite_false]
      apply Finset.mem_map_of_mem
      have : (⟨i + l.val - i, by omega⟩ : Fin t) = l := Fin.ext (by simp)
      rw [this]; exact hl
    · have : e ∈ Finset.univ.biUnion W := by rw [hW.2]; exact Finset.mem_univ _
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 this
      have hji : j.val < i := by
        by_contra h; apply he; simp only [rest, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨j, by omega, hj⟩
      exact ⟨j, by rw [splice_lt _ _ _ _ _ _ hji]; exact hj⟩

end Splice

/-! ### Orientations, arcs, heads and bad vertices -/

section Heads

variable (ends : Fin m → Sym2 (Fin n)) (r : Fin n)

noncomputable def orient (F : Edges m) : Direction n m :=
  if h : ∃ D, Toward ends F D r then h.choose else fun _ => (r, r)

theorem orient_toward {F : Edges m} (hF : IsSpanningTree ends F) :
    Toward ends F (orient ends r F) r := by
  have h := exists_toward ends hF r
  simp only [orient, h, dite_true]
  exact h.choose_spec

/-- the arcs out of `v` with head in `A`, in the slots `≥ i` -/
noncomputable def arcsTo (W : Trees k m) (i : ℕ) (v : Fin n) (A : Finset (Fin n)) :
    Finset (Σ _ : Fin k, Fin m) :=
  (Finset.univ.filter fun j : Fin k => i ≤ j.val).sigma fun j =>
    (W j).filter fun e => (orient ends r (W j) e).1 = v ∧ (orient ends r (W j) e).2 ∈ A

noncomputable def heads (W : Trees k m) (i : ℕ) (v : Fin n) : Finset (Fin n) :=
  (arcsTo ends r W i v Finset.univ).image fun p => (orient ends r (W p.1) p.2).2

noncomputable def bad (W : Trees k m) (i : ℕ) (A : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => k - i < 8 * (heads ends r W i v ∩ A).card

noncomputable def Lset (W : Trees k m) (i : ℕ) (A : Finset (Fin n)) : Finset (Fin n) :=
  A \ (bad ends r W i A).biUnion (heads ends r W i)

theorem heads_inter (W : Trees k m) (i : ℕ) (v : Fin n) (A : Finset (Fin n)) :
    heads ends r W i v ∩ A =
      (arcsTo ends r W i v A).image fun p => (orient ends r (W p.1) p.2).2 := by
  ext u
  simp only [heads, arcsTo, Finset.mem_inter, Finset.mem_image, Finset.mem_sigma,
    Finset.mem_filter, Finset.mem_univ, true_and, and_true]
  constructor
  · rintro ⟨⟨p, ⟨h1, h2, h3⟩, rfl⟩, hA⟩; exact ⟨p, ⟨h1, h2, h3, hA⟩, rfl⟩
  · rintro ⟨p, ⟨h1, h2, h3, hA⟩, rfl⟩; exact ⟨⟨p, ⟨h1, h2, h3⟩, rfl⟩, hA⟩

theorem card_heads_inter (hs : Simple ends) {W : Trees k m} (hW : TreePartition ends W)
    (i : ℕ) (v : Fin n) (A : Finset (Fin n)) :
    (heads ends r W i v ∩ A).card = (arcsTo ends r W i v A).card := by
  rw [heads_inter]
  apply Finset.card_image_of_injOn
  rintro ⟨j, e⟩ hp ⟨j', e'⟩ hp' heq
  simp only [arcsTo, Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ,
    true_and] at hp hp' heq
  have ho := (orient_toward ends r (hW.1.1 j)).1 e hp.2.1
  have ho' := (orient_toward ends r (hW.1.1 j')).1 e' hp'.2.1
  rw [hp.2.2.1, heq] at ho
  rw [hp'.2.2.1] at ho'
  have hee : e = e' := hs.1 (ho.trans ho'.symm)
  subst hee
  have hjj : j = j' := by
    by_contra h
    exact Finset.disjoint_left.1 (hW.1.2 j j' h) hp.2.1 hp'.2.1
  subst hjj
  rfl

theorem card_slots (i : ℕ) : (Finset.univ.filter fun j : Fin k => i ≤ j.val).card = k - i := by
  have : (Finset.univ.filter fun j : Fin k => i ≤ j.val) =
      (Finset.Ico i k).attachFin (fun a ha => (Finset.mem_Ico.1 ha).2) := by
    ext j; simp
  rw [this, Finset.card_attachFin, Nat.card_Ico]

theorem card_heads_le (hs : Simple ends) {W : Trees k m} (hW : TreePartition ends W)
    (i : ℕ) (v : Fin n) : (heads ends r W i v).card ≤ k - i := by
  have h := card_heads_inter ends r hs hW i v Finset.univ
  rw [Finset.inter_univ] at h
  rw [h, arcsTo, Finset.card_sigma, ← card_slots (k := k) i, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  have hT := orient_toward ends r (hW.1.1 j)
  have : outdegree (W j) (orient ends r (W j)) v ≤ 1 := by
    by_cases hv : v = r
    · rw [hv, hT.2.1]; omega
    · rw [hT.2.2 v hv]
  unfold outdegree at this
  refine le_trans (Finset.card_le_card ?_) this
  intro e he
  simp only [Finset.mem_filter, Finset.mem_univ, and_true] at he ⊢
  exact ⟨he.1, he.2⟩

end Heads

/-! ### One round -/

theorem round (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (hn : 2 ≤ n) (r : Fin n)
    {C₁ : ℝ} (h31 : L31Stmt C₁) {W : Trees k m} (hW : TreePartition ends W) (i : ℕ)
    (hi : i < k) (A : Finset (Fin n)) :
    ∃ W' : Trees k m, TreePartition ends W' ∧ (∀ j : Fin k, j.val < i → W' j = W j) ∧
      ((A ∩ internal ends (W' ⟨i, hi⟩)).card : ℝ) ≤
        C₁ * ((n : ℝ) / ((k - i : ℕ) : ℝ)) + ((k - i : ℕ) : ℝ) * (bad ends r W i A).card := by
  set t := k - i with ht_def
  have ht : 1 ≤ t := by omega
  set R := rest i W with hR_def
  set emb : Fin R.card ↪ Fin m := (R.orderEmbOfFin rfl).toEmbedding with hemb_def
  have hR : ∀ e, e ∈ R ↔ ∃ x, emb x = e := by
    intro e
    have := congrArg (e ∈ ·) (R.range_orderEmbOfFin rfl)
    simp only [Set.mem_range, Finset.mem_coe] at this
    rw [← this]; rfl
  set ends' := ends ∘ emb with hends'
  let idx : Fin t → Fin k := fun l => ⟨i + l.val, by omega⟩
  have hsub : ∀ l, W (idx l) ⊆ R := by
    intro l e he
    simp only [hR_def, rest, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨idx l, by simp [idx], he⟩
  have hR' : ∀ e ∈ R, ∃ x, emb x = e := fun e he => (hR e).1 he
  set T' : Trees t R.card := fun l => pull emb (W (idx l)) with hT'_def
  have hT'map : ∀ l, (T' l).map emb = W (idx l) := fun l => map_pull emb hR' (hsub l)
  set D' : Fin t → Direction n R.card := fun l => orient ends r (W (idx l)) ∘ emb with hD'_def
  -- the pulled-back trees partition the remaining edges
  have hT' : TreePartition ends' T' := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro l
      rw [hends', isSpanningTree_comp_iff, hT'map]
      exact hW.1.1 _
    · intro a b hab
      rw [← Finset.disjoint_map emb, hT'map, hT'map]
      apply hW.1.2
      intro h; apply hab; ext; simp [idx, Fin.ext_iff] at h; omega
    · ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
      obtain ⟨j, hj, hxj⟩ : ∃ j : Fin k, i ≤ j.val ∧ emb x ∈ W j := by
        have := (hR (emb x)).2 ⟨x, rfl⟩
        simpa [hR_def, rest] using this
      refine ⟨⟨j.val - i, by omega⟩, ?_⟩
      rw [hT'_def, mem_pull]
      have : idx ⟨j.val - i, by omega⟩ = j := Fin.ext (by simp [idx]; omega)
      rw [this]; exact hxj
  have houtdeg : ∀ l v, outdegree (T' l) (D' l) v = outdegree (W (idx l)) (orient ends r (W (idx l))) v := by
    intro l v
    unfold outdegree
    have := card_filter_map emb (T' l) (fun e => (orient ends r (W (idx l)) e).1 = v)
    rw [hT'map] at this
    convert this.symm using 2 <;> (ext x; simp [hD'_def])
  have htoward : ∀ l, Toward ends' (T' l) (D' l) r := by
    intro l
    have h := orient_toward ends r (hW.1.1 (idx l))
    refine ⟨?_, by rw [houtdeg]; exact h.2.1, fun v hv => by rw [houtdeg]; exact h.2.2 v hv⟩
    intro x hx
    rw [hT'_def, mem_pull] at hx
    exact h.1 (emb x) hx
  -- outgoing arcs counted through heads
  have hout_eq : ∀ v B, outgoingTo T' D' v B = (arcsTo ends r W i v B).card := by
    intro v B
    unfold outgoingTo
    rw [arcsTo, Finset.card_sigma]
    have h1 : ∀ l : Fin t, ((T' l).filter fun e => (D' l e).1 = v ∧ (D' l e).2 ∈ B).card =
        ((W (idx l)).filter fun e => (orient ends r (W (idx l)) e).1 = v ∧
          (orient ends r (W (idx l)) e).2 ∈ B).card := by
      intro l
      have := card_filter_map emb (T' l) (fun e => (orient ends r (W (idx l)) e).1 = v ∧
        (orient ends r (W (idx l)) e).2 ∈ B)
      rw [hT'map] at this
      convert this.symm using 2 <;> (ext x; simp [hD'_def])
    refine (Finset.sum_congr rfl (fun l _ => h1 l)).trans ?_
    apply Finset.sum_bij (fun l _ => idx l)
    · intro l _; simp [idx]
    · intro a _ b _ h; ext; simp [idx, Fin.ext_iff] at h; omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact ⟨⟨j.val - i, by omega⟩, Finset.mem_univ _, Fin.ext (by simp [idx]; omega)⟩
    · intro l _; rfl
  set L := Lset ends r W i A with hL_def
  have hout : ∀ v, (outgoingTo T' D' v L : ℝ) ≤ (t : ℝ) / 8 := by
    intro v
    rw [hout_eq, ← card_heads_inter ends r hs hW]
    by_cases hb : v ∈ bad ends r W i A
    · have : heads ends r W i v ∩ L = ∅ := by
        ext u
        simp only [Finset.mem_inter, hL_def, Lset, Finset.mem_sdiff, Finset.mem_biUnion,
          Finset.notMem_empty, iff_false, not_and, not_not]
        intro hu _
        exact ⟨v, hb, hu⟩
      rw [this]; simp; positivity
    · simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hb
      have hle : (heads ends r W i v ∩ L).card ≤ (heads ends r W i v ∩ A).card :=
        Finset.card_le_card (Finset.inter_subset_inter_left Finset.sdiff_subset)
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      exact_mod_cast (by omega : (heads ends r W i v ∩ L).card * 8 ≤ t)
  -- the minimal extractable tree
  have hext0 : Extractable ends' t (T' ⟨0, ht⟩) := extractable_of_partition ends' ht T' hT'
  obtain ⟨Q', hQ'mem, hQ'min⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Finset (Fin R.card))).filter (Extractable ends' t))
    (weight (incidenceWeight ends' L)) ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hext0⟩⟩
  have hQ'ext : Extractable ends' t Q' := (Finset.mem_filter.1 hQ'mem).2
  have hbound := h31 n R.card t hn ht ends' T' D' r L Q' (simple_comp ends emb hs) hT' htoward
    hout hQ'ext (fun U hU => hQ'min U (Finset.mem_filter.2 ⟨Finset.mem_univ _, hU⟩))
  obtain ⟨V, hV, hV0⟩ := partition_of_extractable ends' ht hQ'ext
  have hRrest : ∀ e, e ∈ rest i W ↔ ∃ x, emb x = e := hR
  refine ⟨splice i emb W ht_def V, splice_partition ends i emb hW ht_def hV hRrest,
    fun j hj => splice_lt i emb W ht_def V j hj, ?_⟩
  rw [splice_eq i emb W ht_def V hi (by omega), hV0, ← internal_comp]
  -- |A ∩ int| ≤ |L ∩ int| + |A \ L|
  have hsplit : (A ∩ internal ends' Q').card ≤
      (internal ends' Q' ∩ L).card + ((bad ends r W i A).biUnion (heads ends r W i)).card := by
    calc (A ∩ internal ends' Q').card
        ≤ (internal ends' Q' ∩ L ∪ (bad ends r W i A).biUnion (heads ends r W i)).card := by
          apply Finset.card_le_card
          intro u hu
          rw [Finset.mem_inter] at hu
          rw [Finset.mem_union]
          by_cases h : u ∈ (bad ends r W i A).biUnion (heads ends r W i)
          · exact Or.inr h
          · left
            refine Finset.mem_inter.2 ⟨hu.2, ?_⟩
            rw [hL_def, Lset, Finset.mem_sdiff]
            exact ⟨hu.1, h⟩
      _ ≤ _ := Finset.card_union_le _ _
  have hbu : ((bad ends r W i A).biUnion (heads ends r W i)).card ≤
      (bad ends r W i A).card * t := by
    refine le_trans Finset.card_biUnion_le ?_
    rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
    exact Finset.sum_le_sum fun v _ => card_heads_le ends r hs hW i v
  have hsplitR : ((A ∩ internal ends' Q').card : ℝ) ≤
      ((internal ends' Q' ∩ L).card : ℝ) + ((bad ends r W i A).card : ℝ) * t := by
    have := le_trans hsplit (Nat.add_le_add_left hbu _)
    exact_mod_cast this
  calc ((A ∩ internal ends' Q').card : ℝ)
      ≤ ((internal ends' Q' ∩ L).card : ℝ) + ((bad ends r W i A).card : ℝ) * t := hsplitR
    _ ≤ C₁ * ((n : ℝ) / (t : ℝ)) + (t : ℝ) * (bad ends r W i A).card := by
        rw [mul_comm ((bad ends r W i A).card : ℝ)]
        linarith [hbound]

end LowDiameterNashWilliams.Main.Dev.T2
end

section
/-! Theorem 2, part C: counting over the finite label spaces `ι → Fin 16`.  Exponential-moment
bounds for the number of labelled vertices (upper tail, for bad vertices; lower tail, for the
number of rounds in which a vertex is sampled), an averaging lemma for one coordinate of a
sequence of labellings, and two geometric-sum bounds. -/

set_option autoImplicit false
open Classical
open scoped BigOperators

namespace LowDiameterNashWilliams.Main.Dev.T2

/-! ### Exponential moments -/

theorem sum_pow_card {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Finset ι) (b : ℝ) :
    ∑ y : ι → Fin 16, b ^ (H.filter fun v => y v = 0).card =
      (15 + b) ^ H.card * 16 ^ Hᶜ.card := by
  let G : ι → Fin 16 → ℝ := fun v c => if v ∈ H then (if c = 0 then b else 1) else 1
  have h1 : ∀ y : ι → Fin 16, b ^ (H.filter fun v => y v = 0).card = ∏ v, G v (y v) := by
    intro y
    simp only [G]
    rw [Finset.prod_ite_mem, Finset.univ_inter, ← Finset.prod_filter, Finset.prod_const]
  have h3 : ∀ v, ∑ c : Fin 16, G v c = if v ∈ H then 15 + b else 16 := by
    intro v
    by_cases hv : v ∈ H
    · simp only [G, hv, if_true]
      rw [Fin.sum_univ_succ]
      simp only [if_true, Fin.succ_ne_zero, if_false, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin]
      norm_num; ring
    · simp [G, hv]
  calc ∑ y : ι → Fin 16, b ^ (H.filter fun v => y v = 0).card
      = ∑ y : ι → Fin 16, ∏ v, G v (y v) := Finset.sum_congr rfl fun y _ => h1 y
    _ = ∏ v, ∑ c, G v c := (Fintype.prod_sum G).symm
    _ = ∏ v, (if v ∈ H then 15 + b else 16) := Finset.prod_congr rfl fun v _ => h3 v
    _ = (15 + b) ^ H.card * 16 ^ Hᶜ.card := by
      rw [Finset.prod_ite]
      have hf : Finset.univ.filter (fun v => v ∈ H) = H := by ext; simp
      have hf' : Finset.univ.filter (fun v => v ∉ H) = Hᶜ := by ext; simp
      rw [hf, hf', Finset.prod_const, Finset.prod_const]

/-- Upper tail: at most `16^n ρ_B^t` labellings put more than `t/8` vertices of `H` (with
`|H| ≤ t`) into the sample `{y = 0}`, where `ρ_B = (15 + d^8)/(16 d)`, `d = 11/10`. -/
noncomputable def rhoB : ℝ := (15 + (11 / 10 : ℝ) ^ 8) / (16 * (11 / 10))

theorem rhoB_pos : 0 < rhoB := by unfold rhoB; norm_num

theorem rhoB_lt : rhoB < 1 := by unfold rhoB; norm_num

theorem upper_tail {n : ℕ} (H : Finset (Fin n)) (t : ℕ) (hH : H.card ≤ t) :
    ((Finset.univ.filter fun y : Fin n → Fin 16 =>
        t < 8 * (H.filter fun v => y v = 0).card).card : ℝ) ≤ 16 ^ n * rhoB ^ t := by
  set d : ℝ := 11 / 10 with hd
  have hd1 : 1 ≤ d := by rw [hd]; norm_num
  have hdpos : 0 < d := by linarith
  rw [← Finset.sum_boole]
  have hpt : ∀ y : Fin n → Fin 16,
      (if t < 8 * (H.filter fun v => y v = 0).card then (1 : ℝ) else 0) ≤
        (d ^ 8) ^ (H.filter fun v => y v = 0).card / d ^ t := by
    intro y
    split_ifs with h
    · rw [le_div_iff₀ (pow_pos hdpos _), one_mul, ← pow_mul]
      exact pow_le_pow_right₀ hd1 (by omega)
    · positivity
  refine le_trans (Finset.sum_le_sum fun y _ => hpt y) ?_
  rw [← Finset.sum_div, sum_pow_card]
  have hc : Hᶜ.card + H.card = n := by
    rw [Finset.card_compl_add_card, Fintype.card_fin]
  have ha : 1 ≤ (15 + d ^ 8) / 16 := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith [one_le_pow₀ (n := 8) hd1]
  have : (15 + d ^ 8) ^ H.card * 16 ^ Hᶜ.card = (16 : ℝ) ^ n * ((15 + d ^ 8) / 16) ^ H.card := by
    rw [div_pow, show (16 : ℝ) ^ n = 16 ^ Hᶜ.card * 16 ^ H.card by rw [← pow_add, hc]]
    field_simp
    rw [← mul_pow]; congr 1; ring
  rw [this, div_le_iff₀ (pow_pos hdpos _), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ((15 + d ^ 8) / 16) ^ H.card ≤ ((15 + d ^ 8) / 16) ^ t := pow_le_pow_right₀ ha hH
    _ = rhoB ^ t * d ^ t := by
        rw [← mul_pow]; congr 1; rw [rhoB, ← hd]; field_simp

/-- Lower tail for the number `Z` of rounds `i < M` with `Y i v = 0`:
`ρ_Z = d^2 (15 + d^{-64}) / 16`, `d = 101/100`. -/
noncomputable def rhoZ : ℝ := (101 / 100 : ℝ) ^ 2 * (15 + ((101 / 100 : ℝ) ^ 64)⁻¹) / 16

theorem rhoZ_pos : 0 < rhoZ := by unfold rhoZ; positivity

theorem rhoZ_lt : rhoZ < 1 := by unfold rhoZ; norm_num

theorem lower_tail {n M : ℕ} (v : Fin n) (k : ℕ) (hk : k ≤ 2 * M) :
    ((Finset.univ.filter fun Y : Fin M → Fin n → Fin 16 =>
        k > 64 * (Finset.univ.filter fun i => Y i v = 0).card).card : ℝ) ≤
      16 ^ (n * M) * rhoZ ^ M := by
  set d : ℝ := 101 / 100 with hd
  have hd1 : 1 ≤ d := by rw [hd]; norm_num
  have hdpos : 0 < d := by linarith
  set b : ℝ := (d ^ 64)⁻¹ with hb
  rw [← Finset.sum_boole]
  have hpt : ∀ Y : Fin M → Fin n → Fin 16,
      (if k > 64 * (Finset.univ.filter fun i => Y i v = 0).card then (1 : ℝ) else 0) ≤
        d ^ k * b ^ (Finset.univ.filter fun i => Y i v = 0).card := by
    intro Y
    split_ifs with h
    · rw [hb, inv_pow, ← pow_mul, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hdpos _), one_mul]
      exact pow_le_pow_right₀ hd1 (by omega)
    · positivity
  refine le_trans (Finset.sum_le_sum fun Y _ => hpt Y) ?_
  rw [← Finset.mul_sum]
  let G : Fin M → (Fin n → Fin 16) → ℝ := fun _ y =>
    b ^ (({v} : Finset (Fin n)).filter fun w => y w = 0).card
  have hprod : ∀ Y : Fin M → Fin n → Fin 16, b ^ (Finset.univ.filter fun i => Y i v = 0).card =
      ∏ i, G i (Y i) := by
    intro Y
    simp only [G, Finset.filter_singleton]
    rw [← Finset.prod_const, Finset.prod_filter]
    exact Finset.prod_congr rfl fun i _ => by split_ifs <;> simp
  have hsum : ∑ Y : Fin M → Fin n → Fin 16, b ^ (Finset.univ.filter fun i => Y i v = 0).card =
      ((15 + b) * 16 ^ ({v}ᶜ : Finset (Fin n)).card) ^ M := by
    calc _ = ∑ Y : Fin M → Fin n → Fin 16, ∏ i, G i (Y i) := Finset.sum_congr rfl fun Y _ => hprod Y
      _ = ∏ i, ∑ y, G i y := (Fintype.prod_sum G).symm
      _ = _ := by
        simp only [G, sum_pow_card, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.card_singleton, pow_one]
  rw [hsum]
  have hc : ({v}ᶜ : Finset (Fin n)).card = n - 1 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  rw [hc]
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (fun h => by subst h; exact v.elim0)
  calc d ^ k * ((15 + b) * 16 ^ (n - 1)) ^ M ≤ d ^ (2 * M) * ((15 + b) * 16 ^ (n - 1)) ^ M :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 hk) (by positivity)
    _ = 16 ^ (n * M) * rhoZ ^ M := by
        rw [rhoZ, ← hd, ← hb, pow_mul, ← mul_pow]
        have h16 : (16 : ℝ) ^ (n * M) = (16 ^ (n - 1) * 16) ^ M := by
          rw [← pow_succ, ← pow_mul]; congr 2; omega
        rw [h16, ← mul_pow]
        congr 1
        field_simp

/-! ### Averaging over one coordinate -/

theorem avg_coord {n M : ℕ} {σ : Type*} (j : Fin M) (G : (Fin M → Fin n → Fin 16) → σ)
    (hG : ∀ Y a, G (Function.update Y j a) = G Y) (Inv : σ → Prop) (hInv : ∀ Y, Inv (G Y))
    (P : σ → (Fin n → Fin 16) → Prop) (B : ℝ)
    (hB : ∀ s, Inv s → ((Finset.univ.filter (P s)).card : ℝ) ≤ B) :
    (16 : ℝ) ^ n * ((Finset.univ.filter fun Y => P (G Y) (Y j)).card : ℝ) ≤
      16 ^ (n * M) * B := by
  set e := Equiv.piSplitAt j (fun _ : Fin M => Fin n → Fin 16) with he
  have hupd : ∀ (a a0 : Fin n → Fin 16) (rest : ∀ i : {i // i ≠ j}, Fin n → Fin 16),
      e.symm (a, rest) = Function.update (e.symm (a0, rest)) j a := by
    intro a a0 rest
    funext i
    by_cases h : i = j
    · subst h; simp [he, Equiv.piSplitAt_symm_apply]
    · simp [he, Equiv.piSplitAt_symm_apply, h]
  have hj : ∀ (a : Fin n → Fin 16) rest, (e.symm (a, rest)) j = a := by
    intro a rest; simp [he, Equiv.piSplitAt_symm_apply]
  rw [← Finset.sum_boole]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type_right]
  have hin : ∀ rest : ∀ i : {i // i ≠ j}, Fin n → Fin 16,
      ∑ a : Fin n → Fin 16, (if P (G (e.symm (a, rest))) ((e.symm (a, rest)) j) then (1 : ℝ) else 0)
        ≤ B := by
    intro rest
    set a0 : Fin n → Fin 16 := fun _ => 0
    have : ∀ a, (if P (G (e.symm (a, rest))) ((e.symm (a, rest)) j) then (1 : ℝ) else 0) =
        if P (G (e.symm (a0, rest))) a then 1 else 0 := by
      intro a; rw [hj, hupd a a0 rest, hG]
    simp only [this]
    rw [Finset.sum_boole]
    exact hB _ (hInv _)
  have hcard : (16 : ℝ) ^ n * (Fintype.card (∀ i : {i // i ≠ j}, Fin n → Fin 16) : ℝ) =
      16 ^ (n * M) := by
    have h1 := Fintype.card_congr e
    rw [Fintype.card_prod] at h1
    have h2 : Fintype.card (Fin M → Fin n → Fin 16) = 16 ^ (n * M) := by
      simp [← pow_mul]
    have h3 : Fintype.card (Fin n → Fin 16) = 16 ^ n := by simp
    rw [h2, h3] at h1
    exact_mod_cast h1.symm
  calc (16 : ℝ) ^ n * ∑ rest, ∑ a, _ ≤ (16 : ℝ) ^ n * ∑ _rest : (∀ i : {i // i ≠ j}, Fin n → Fin 16), B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun rest _ => hin rest) (by positivity)
    _ = 16 ^ (n * M) * B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hcard]

/-! ### Geometric sums -/

theorem sum_mul_geom_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (k M : ℕ) (hM : M ≤ k) :
    ∑ i ∈ Finset.range M, ((k - i : ℕ) : ℝ) * ρ ^ (k - i) ≤ ρ / (1 - ρ) ^ 2 := by
  have hinj : Set.InjOn (fun i => k - i) (Finset.range M : Set ℕ) := by
    intro a ha b hb h
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at h; omega
  rw [← Finset.sum_image (f := fun t : ℕ => (t : ℝ) * ρ ^ t) hinj]
  exact sum_le_hasSum _ (fun i _ => by positivity)
    (hasSum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1))

theorem mul_pow_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (M : ℕ) :
    (M : ℝ) * ρ ^ M ≤ 1 / (1 - ρ) := by
  have hs : ∑ i ∈ Finset.range M, ρ ^ i ≤ 1 / (1 - ρ) := by
    rw [one_div]
    exact sum_le_hasSum _ (fun i _ => by positivity) (hasSum_geometric_of_lt_one h0 h1)
  refine le_trans ?_ hs
  calc (M : ℝ) * ρ ^ M = ∑ _i ∈ Finset.range M, ρ ^ M := by simp
    _ ≤ _ := Finset.sum_le_sum fun i hi => pow_le_pow_of_le_one h0 h1.le
        (le_of_lt (Finset.mem_range.1 hi))

end LowDiameterNashWilliams.Main.Dev.T2
end

section
/-! Theorem 2, part D: the extraction process driven by a sequence of labellings
`Y : Fin M → Fin n → Fin 16`, and the averaged bounds over all such sequences. -/

set_option autoImplicit false
open Classical
open scoped BigOperators
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.T2
open LowDiameterNashWilliams.Main

variable {n m k : ℕ}

/-- the sample `Y_i = {v : y v = 0}` -/
noncomputable def sample (y : Fin n → Fin 16) : Finset (Fin n) :=
  Finset.univ.filter fun v => y v = 0

/-- `W'` is a valid outcome of round `i` from `W` with sample `A` -/
def Good (ends : Fin m → Sym2 (Fin n)) (r : Fin n) (C₁ : ℝ) (W : Trees k m) (i : ℕ)
    (A : Finset (Fin n)) (W' : Trees k m) : Prop :=
  TreePartition ends W' ∧ (∀ j : Fin k, j.val < i → W' j = W j) ∧
  ∀ hi : i < k, ((A ∩ internal ends (W' ⟨i, hi⟩)).card : ℝ) ≤
    C₁ * ((n : ℝ) / ((k - i : ℕ) : ℝ)) + ((k - i : ℕ) : ℝ) * (bad ends r W i A).card

noncomputable def step (ends : Fin m → Sym2 (Fin n)) (r : Fin n) (C₁ : ℝ) (i : ℕ)
    (A : Finset (Fin n)) (W : Trees k m) : Trees k m :=
  if h : ∃ W', Good ends r C₁ W i A W' then h.choose else W

noncomputable def proc (ends : Fin m → Sym2 (Fin n)) (r : Fin n) (C₁ : ℝ) (T0 : Trees k m)
    {M : ℕ} (Y : Fin M → Fin n → Fin 16) : ℕ → Trees k m
  | 0 => T0
  | i + 1 => step ends r C₁ i (if h : i < M then sample (Y ⟨i, h⟩) else ∅)
      (proc ends r C₁ T0 Y i)

section Process

variable (ends : Fin m → Sym2 (Fin n)) (r : Fin n) (C₁ : ℝ)

theorem step_tp {i : ℕ} {A : Finset (Fin n)} {W : Trees k m} (hW : TreePartition ends W) :
    TreePartition ends (step ends r C₁ i A W) := by
  unfold step; split_ifs with h
  · exact h.choose_spec.1
  · exact hW

theorem step_keep {i : ℕ} {A : Finset (Fin n)} {W : Trees k m} (j : Fin k) (hj : j.val < i) :
    step ends r C₁ i A W j = W j := by
  unfold step; split_ifs with h
  · exact h.choose_spec.2.1 j hj
  · rfl

theorem step_good (hs : Simple ends) (hn : 2 ≤ n) (h31 : L31Stmt C₁) {i : ℕ}
    {A : Finset (Fin n)} {W : Trees k m} (hW : TreePartition ends W) (hi : i < k) :
    Good ends r C₁ W i A (step ends r C₁ i A W) := by
  have hex : ∃ W', Good ends r C₁ W i A W' := by
    obtain ⟨W', h1, h2, h3⟩ := round ends hs hn r h31 hW i hi A
    exact ⟨W', h1, h2, fun _ => h3⟩
  unfold step; rw [dif_pos hex]; exact hex.choose_spec

variable {T0 : Trees k m} {M : ℕ}

theorem proc_tp (hT0 : TreePartition ends T0) (Y : Fin M → Fin n → Fin 16) (i : ℕ) :
    TreePartition ends (proc ends r C₁ T0 Y i) := by
  induction i with
  | zero => exact hT0
  | succ i ih => exact step_tp ends r C₁ ih

theorem proc_keep (Y : Fin M → Fin n → Fin 16) (j : Fin k) (i : ℕ) (hj : j.val < i) (d : ℕ) :
    proc ends r C₁ T0 Y (i + d) j = proc ends r C₁ T0 Y i j := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← ih, ← add_assoc]
    exact step_keep ends r C₁ j (by omega)

theorem proc_update (Y : Fin M → Fin n → Fin 16) (j : Fin M) (a : Fin n → Fin 16) (i : ℕ)
    (hi : i ≤ j.val) : proc ends r C₁ T0 (Function.update Y j a) i = proc ends r C₁ T0 Y i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [proc]
    rw [ih (by omega)]
    congr 2
    funext h
    rw [Function.update_of_ne]
    intro h'; rw [Fin.ext_iff] at h'; simp at h'; omega

theorem proc_round (hs : Simple ends) (hn : 2 ≤ n) (h31 : L31Stmt C₁)
    (hT0 : TreePartition ends T0) (hMk : M ≤ k) (Y : Fin M → Fin n → Fin 16) (i : Fin M) :
    ((sample (Y i) ∩ internal ends (proc ends r C₁ T0 Y M ⟨i.val, by omega⟩)).card : ℝ) ≤
      C₁ * ((n : ℝ) / ((k - i.val : ℕ) : ℝ)) + ((k - i.val : ℕ) : ℝ) *
        (bad ends r (proc ends r C₁ T0 Y i.val) i.val (sample (Y i))).card := by
  have hkeep := proc_keep ends r C₁ (T0 := T0) Y ⟨i.val, by omega⟩ (i.val + 1) (by simp)
    (M - (i.val + 1))
  have hM : i.val + 1 + (M - (i.val + 1)) = M := by omega
  rw [hM] at hkeep
  rw [hkeep]
  have hstep : proc ends r C₁ T0 Y (i.val + 1) = step ends r C₁ i.val (sample (Y i))
      (proc ends r C₁ T0 Y i.val) := by
    simp only [proc, dif_pos i.isLt]
  rw [hstep]
  exact (step_good ends r C₁ hs hn h31 (proc_tp ends r C₁ hT0 Y i.val) (by omega)).2.2 _

end Process

/-! ### Averages -/

section Averages

variable (ends : Fin m → Sym2 (Fin n)) (r : Fin n) (C₁ : ℝ)

theorem inter_sample (H : Finset (Fin n)) (y : Fin n → Fin 16) :
    H ∩ sample y = H.filter fun v => y v = 0 := by
  ext v; simp [sample]

/-- the expected number of bad vertices of round `i` -/
theorem sum_bad_le (hs : Simple ends) {T0 : Trees k m} (hT0 : TreePartition ends T0) {M : ℕ}
    (i : Fin M) :
    ∑ Y : Fin M → Fin n → Fin 16,
        ((bad ends r (proc ends r C₁ T0 Y i.val) i.val (sample (Y i))).card : ℝ) ≤
      (16 : ℝ) ^ (n * M) * (n * rhoB ^ (k - i.val)) := by
  have h1 : ∀ Y : Fin M → Fin n → Fin 16,
      ((bad ends r (proc ends r C₁ T0 Y i.val) i.val (sample (Y i))).card : ℝ) =
        ∑ v, (if v ∈ bad ends r (proc ends r C₁ T0 Y i.val) i.val (sample (Y i))
          then (1 : ℝ) else 0) := by
    intro Y
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ v : Fin n, ∑ Y : Fin M → Fin n → Fin 16,
      (if v ∈ bad ends r (proc ends r C₁ T0 Y i.val) i.val (sample (Y i)) then (1 : ℝ) else 0)
        ≤ (16 : ℝ) ^ (n * M) * rhoB ^ (k - i.val) := by
    intro v
    rw [Finset.sum_boole]
    have := avg_coord i (fun Y => proc ends r C₁ T0 Y i.val)
      (fun Y a => proc_update ends r C₁ Y i a i.val le_rfl) (TreePartition ends)
      (fun Y => proc_tp ends r C₁ hT0 Y i.val)
      (fun s a => v ∈ bad ends r s i.val (sample a)) ((16 : ℝ) ^ n * rhoB ^ (k - i.val)) ?_
    · have h16 : (0 : ℝ) < 16 ^ n := by positivity
      rw [show (16 : ℝ) ^ (n * M) * (16 ^ n * rhoB ^ (k - i.val)) =
        16 ^ n * (16 ^ (n * M) * rhoB ^ (k - i.val)) by ring] at this
      have h := (mul_le_mul_iff_of_pos_left h16).1 this
      refine le_trans (le_of_eq ?_) h
      congr 2
      ext Y; simp
    · intro s hsW
      have hH := card_heads_le ends r hs hsW i.val v
      have := upper_tail (heads ends r s i.val v) (k - i.val) hH
      refine le_trans (le_of_eq ?_) this
      congr 2
      ext a
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, inter_sample]
  calc ∑ v : Fin n, ∑ Y : Fin M → Fin n → Fin 16, _ ≤
        ∑ _v : Fin n, (16 : ℝ) ^ (n * M) * rhoB ^ (k - i.val) := Finset.sum_le_sum fun v _ => h2 v
    _ = _ := by simp; ring

theorem sum_inv_le {M : ℕ} (hM : M = (k + 1) / 2) :
    ∑ i : Fin M, (1 : ℝ) / ((k - i.val : ℕ) : ℝ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos M with h0 | hpos
  · subst h0; simp
  have h : ∀ i : Fin M, (1 : ℝ) / ((k - i.val : ℕ) : ℝ) ≤ 1 / (M : ℝ) := by
    intro i
    apply one_div_le_one_div_of_le (by exact_mod_cast hpos)
    exact_mod_cast (by omega : M ≤ k - i.val)
  calc _ ≤ ∑ _i : Fin M, 1 / (M : ℝ) := Finset.sum_le_sum fun i _ => h i
    _ = 1 := by simp; field_simp

/-- the expected total of sampled internal occurrences -/
theorem sum_F_le (hs : Simple ends) (hn : 2 ≤ n) (hC₁ : 0 ≤ C₁) (h31 : L31Stmt C₁)
    {T0 : Trees k m} (hT0 : TreePartition ends T0) {M : ℕ} (hM : M = (k + 1) / 2) (hk : 1 ≤ k) :
    ∑ Y : Fin M → Fin n → Fin 16, ∑ i : Fin M,
        ((sample (Y i) ∩ internal ends (proc ends r C₁ T0 Y M ⟨i.val, by omega⟩)).card : ℝ) ≤
      (16 : ℝ) ^ (n * M) * (n * (C₁ + rhoB / (1 - rhoB) ^ 2)) := by
  have hMk : M ≤ k := by omega
  set N : ℝ := (16 : ℝ) ^ (n * M)
  have hN : Fintype.card (Fin M → Fin n → Fin 16) = (16 : ℝ) ^ (n * M) := by
    simp [← pow_mul]
  calc _ ≤ ∑ Y : Fin M → Fin n → Fin 16, ∑ i : Fin M,
        (C₁ * ((n : ℝ) / ((k - i.val : ℕ) : ℝ)) + ((k - i.val : ℕ) : ℝ) *
          (bad ends r (proc ends r C₁ T0 Y i.val) i.val (sample (Y i))).card) :=
        Finset.sum_le_sum fun Y _ => Finset.sum_le_sum fun i _ =>
          proc_round ends r C₁ hs hn h31 hT0 hMk Y i
    _ = ∑ i : Fin M, (N * (C₁ * ((n : ℝ) / ((k - i.val : ℕ) : ℝ))) + ((k - i.val : ℕ) : ℝ) *
          ∑ Y : Fin M → Fin n → Fin 16,
            ((bad ends r (proc ends r C₁ T0 Y i.val) i.val (sample (Y i))).card : ℝ)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN,
          Finset.mul_sum]
    _ ≤ ∑ i : Fin M, (N * (C₁ * ((n : ℝ) / ((k - i.val : ℕ) : ℝ))) + ((k - i.val : ℕ) : ℝ) *
          (N * (n * rhoB ^ (k - i.val)))) :=
        Finset.sum_le_sum fun i _ => add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (sum_bad_le ends r C₁ hs hT0 i) (Nat.cast_nonneg _))
    _ = N * n * (C₁ * ∑ i : Fin M, (1 : ℝ) / ((k - i.val : ℕ) : ℝ) +
          ∑ i : Fin M, ((k - i.val : ℕ) : ℝ) * rhoB ^ (k - i.val)) := by
        simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ N * n * (C₁ * 1 + rhoB / (1 - rhoB) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [Fin.sum_univ_eq_sum_range (fun i => ((k - i : ℕ) : ℝ) * rhoB ^ (k - i))]
        exact add_le_add (mul_le_mul_of_nonneg_left (sum_inv_le hM) hC₁)
          (sum_mul_geom_le rhoB_pos.le rhoB_lt k M hMk)
    _ = _ := by ring

end Averages

/-! ### Leaves -/

section Leaves

variable (ends : Fin m → Sym2 (Fin n))

/-- pointwise: a vertex that is a leaf in fewer than `k/128` of the first `M` trees but is
sampled in at least `k/64` rounds is a sampled internal vertex in more than `k/128` rounds -/
theorem leaf_point (hn : 2 ≤ n) {U : Trees k m} (hU : TreePartition ends U) {M : ℕ}
    (hM : M = (k + 1) / 2) (Y : Fin M → Fin n → Fin 16) (v : Fin n) :
    (k : ℝ) * (if (leafCount ends U (firstHalf k) v : ℝ) < (k : ℝ) / 128 then 1 else 0) ≤
      (k : ℝ) * (if k > 64 * (Finset.univ.filter fun i : Fin M => Y i v = 0).card then 1 else 0)
        + 128 * ((Finset.univ.filter fun i : Fin M =>
          Y i v = 0 ∧ v ∈ internal ends (U ⟨i.val, by omega⟩)).card : ℝ) := by
  set Z := (Finset.univ.filter fun i : Fin M => Y i v = 0).card
  set Fv := (Finset.univ.filter fun i : Fin M =>
          Y i v = 0 ∧ v ∈ internal ends (U ⟨i.val, by omega⟩)).card
  set lf := leafCount ends U (firstHalf k) v
  have hZ : Z ≤ lf + Fv := by
    have h1 : (Finset.univ.filter fun i : Fin M => Y i v = 0) ⊆
        (Finset.univ.filter fun i : Fin M => degIn ends (U ⟨i.val, by omega⟩) v = 1) ∪
        (Finset.univ.filter fun i : Fin M =>
          Y i v = 0 ∧ v ∈ internal ends (U ⟨i.val, by omega⟩)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      have hd := deg_pos ends hn _ (hU.1.1 ⟨i.val, by omega⟩) v
      by_cases h : degIn ends (U ⟨i.val, by omega⟩) v = 1
      · exact Or.inl h
      · right; refine ⟨hi, ?_⟩
        simp only [internal, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
    have h2 : (Finset.univ.filter fun i : Fin M => degIn ends (U ⟨i.val, by omega⟩) v = 1).card
        ≤ lf := by
      apply Finset.card_le_card_of_injOn (fun i : Fin M => (⟨i.val, by omega⟩ : Fin k))
      · intro i hi
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi
        simp only [firstHalf, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq]
        exact ⟨by show i.val < (k + 1) / 2; omega, hi⟩
      · intro a _ b _ h
        simp only [Fin.mk.injEq] at h
        exact Fin.ext h
    have := Finset.card_le_card h1
    have := Finset.card_union_le
      (Finset.univ.filter fun i : Fin M => degIn ends (U ⟨i.val, by omega⟩) v = 1)
      (Finset.univ.filter fun i : Fin M =>
          Y i v = 0 ∧ v ∈ internal ends (U ⟨i.val, by omega⟩))
    omega
  have hZr : (Z : ℝ) ≤ lf + Fv := by exact_mod_cast hZ
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hF0 : (0 : ℝ) ≤ Fv := by positivity
  split_ifs with h1 h2 h2
  · linarith
  · push Not at h2
    have h2r : (k : ℝ) ≤ 64 * Z := by exact_mod_cast h2
    linarith
  · linarith
  · linarith

theorem sum_Fv (U : Trees k m) {M : ℕ} (hMk : M ≤ k) (Y : Fin M → Fin n → Fin 16) :
    ∑ v : Fin n, ((Finset.univ.filter fun i : Fin M =>
          Y i v = 0 ∧ v ∈ internal ends (U ⟨i.val, by omega⟩)).card : ℝ) =
      ∑ i : Fin M, ((sample (Y i) ∩ internal ends (U ⟨i.val, by omega⟩)).card : ℝ) := by
  simp only [← Finset.sum_boole]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_boole]
  congr 2
  ext v; simp [sample]

end Leaves

end LowDiameterNashWilliams.Main.Dev.T2
end

section
/-!
# Theorem 2 (supplying leaves)

Notation: `M = ⌈k/2⌉ = (k+1)/2`, labellings `Y : Fin M → Fin n → Fin 16` (all `N = 16^{nM}`
of them, uniform), sample `Y_i = {v : Y i v = 0}`, root `r = 0`, `C₁` the constant of
Lemma 3.1, `ρ_B = (15 + d^8)/(16 d)` with `d = 11/10` (`ρ_B < 0.975`),
`ρ_Z = d'^2 (15 + d'^{-64})/16` with `d' = 101/100` (`ρ_Z < 0.991`).

Process (`proc`, deterministic given `Y`).  The state is a tree partition `W` of all edges whose
slots `< i` hold the trees extracted so far.  Round `i < M` (`t = k - i ≥ (k+1)/2` trees left):
orient each tree in slots `≥ i` toward `r` (`exists_toward`); `heads(v)` = heads of the arcs out
of `v` in those slots (at most `t` of them, pairwise distinct since the graph is simple and the
trees are disjoint); `v` is bad if `8 |heads(v) ∩ Y_i| > t`; `L = Y_i \ ⋃_{bad v} heads(v)`.
Then every vertex has at most `t/8` outneighbours in `L` (bad vertices have none).  Transport the
remaining edges to `Fin m'` (`R.orderEmbOfFin`), apply Lemma 3.1 to the minimum-weight
extractable tree `Q` there, and splice `Q` into slot `i` and a partition of the rest into the
slots `> i` (`round`, `splice_partition`).  Pointwise:

  (1) `|Y_i ∩ int(T_i)| ≤ |L ∩ int(T_i)| + |Y_i \ L| ≤ C₁ n / t + t · #bad_i`.

Averages (sums over all `Y`, `N` = number of labellings).
  (2) For a fixed state and a set `H` with `|H| ≤ t`, the number of labellings `y` of one round
      with `8 |H ∩ {y = 0}| > t` is at most `16^n ρ_B^t` (Markov on `d^{8X}`, product formula
      `Σ_y d^{8X} = (15+d^8)^{|H|} 16^{n-|H|}`; `upper_tail`).  The state before round `i`
      does not depend on `Y i` (`proc_update`), so `Σ_Y #bad_i ≤ N n ρ_B^{k-i}` (`avg_coord`).
  (3) `Σ_Y F ≤ N n (C₁ Σ_{i<M} 1/(k-i) + Σ_{i<M} (k-i) ρ_B^{k-i}) ≤ N n (C₁ + ρ_B/(1-ρ_B)^2)`
      where `F = Σ_{i<M} |Y_i ∩ int(T_i)|`, since `k - i ≥ M` and `Σ_t t ρ^t = ρ/(1-ρ)^2`
      (`sum_F_le`).
  (4) `Z_v = #{i < M : Y i v = 0}`: `#{Y : 64 Z_v < k} ≤ N ρ_Z^M` (Markov on `d'^{k - 64 Z_v}`
      and `k ≤ 2M`; `lower_tail`), and `k ρ_Z^M ≤ 2 M ρ_Z^M ≤ 2/(1-ρ_Z)` (`mul_pow_le`).
  (5) Every tree has minimum degree `≥ 1` (`n ≥ 2`), so a sampled round of `v` is either a leaf
      round or an internal sampled occurrence: `Z_v ≤ leaf_v + F_v`.  With
      `S = {v : leaf_v < k/128}`: `k [v ∈ S] ≤ k [64 Z_v < k] + 128 F_v` (if `64 Z_v ≥ k` and
      `v ∈ S`, then `F_v ≥ Z_v - leaf_v > k/64 - k/128 = k/128`; `leaf_point`).
  Summing (5) over `v` and `Y`:
      `Σ_Y k |S(Y)| ≤ k n N ρ_Z^M + 128 N n (C₁ + ρ_B/(1-ρ_B)^2) ≤ N n C`,
  `C = 2/(1-ρ_Z) + 128 (C₁ + ρ_B/(1-ρ_B)^2)`; some `Y` has `k |S(Y)| ≤ n C`, i.e.
  `|S(Y)| ≤ C n / k`, and every `v ∉ S(Y)` is a leaf in at least `k/128` of the first `M`
  trees of the final partition `U = proc Y M`.
-/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.T2
open LowDiameterNashWilliams.Main

/-- the constant of Theorem 2 -/
noncomputable def Cst (C₁ : ℝ) : ℝ := 2 / (1 - rhoZ) + 128 * (C₁ + rhoB / (1 - rhoB) ^ 2)

theorem Cst_pos {C₁ : ℝ} (hC₁ : 0 < C₁) : 0 < Cst C₁ := by
  unfold Cst
  have h1 : 0 < 1 - rhoZ := by linarith [rhoZ_lt]
  have h2 : 0 ≤ rhoB / (1 - rhoB) ^ 2 := div_nonneg rhoB_pos.le (sq_nonneg _)
  positivity

theorem main_bound {C₁ : ℝ} (hC₁ : 0 < C₁) (h31 : L31Stmt C₁) :
    ∀ n m k : ℕ, 2 ≤ n → 1 ≤ k →
    ∀ ends : Fin m → Sym2 (Fin n), Simple ends →
    (∃ T : Trees k m, TreePartition ends T) →
    ∃ (U : Trees k m) (S : Finset (Fin n)), TreePartition ends U ∧
      (S.card : ℝ) ≤ Cst C₁ * ((n : ℝ) / k) ∧
      ∀ v, v ∉ S → (k : ℝ) / 128 ≤ leafCount ends U (firstHalf k) v := by
  intro n m k hn hk ends hs ⟨T0, hT0⟩
  set M := (k + 1) / 2 with hM
  have hMk : M ≤ k := by omega
  have hk2 : k ≤ 2 * M := by omega
  set r : Fin n := ⟨0, by omega⟩
  set N : ℝ := (16 : ℝ) ^ (n * M) with hN_def
  have hN : (Fintype.card (Fin M → Fin n → Fin 16) : ℝ) = N := by
    simp [hN_def, ← pow_mul]
  let U : (Fin M → Fin n → Fin 16) → Trees k m := fun Y => proc ends r C₁ T0 Y M
  let S : (Fin M → Fin n → Fin 16) → Finset (Fin n) := fun Y =>
    Finset.univ.filter fun v => (leafCount ends (U Y) (firstHalf k) v : ℝ) < (k : ℝ) / 128
  let Z : (Fin M → Fin n → Fin 16) → Fin n → ℕ := fun Y v =>
    (Finset.univ.filter fun i : Fin M => Y i v = 0).card
  let Fv : (Fin M → Fin n → Fin 16) → Fin n → ℝ := fun Y v =>
    ((Finset.univ.filter fun i : Fin M =>
      Y i v = 0 ∧ v ∈ internal ends (U Y ⟨i.val, by omega⟩)).card : ℝ)
  have hUtp : ∀ Y, TreePartition ends (U Y) := fun Y => proc_tp ends r C₁ hT0 Y M
  -- pointwise bound, summed over vertices
  have hpt : ∀ Y, (k : ℝ) * (S Y).card ≤
      ∑ v, ((k : ℝ) * (if k > 64 * Z Y v then 1 else 0) + 128 * Fv Y v) := by
    intro Y
    have : (k : ℝ) * (S Y).card = ∑ v, (k : ℝ) *
        (if (leafCount ends (U Y) (firstHalf k) v : ℝ) < (k : ℝ) / 128 then 1 else 0) := by
      rw [← Finset.mul_sum, Finset.sum_boole]
    rw [this]
    exact Finset.sum_le_sum fun v _ => leaf_point ends hn (hUtp Y) hM Y v
  -- the lower-tail part
  have hZsum : ∑ Y : Fin M → Fin n → Fin 16, ∑ v, (if k > 64 * Z Y v then (1 : ℝ) else 0) ≤
      n * (N * rhoZ ^ M) := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _v : Fin n, N * rhoZ ^ M := by
          refine Finset.sum_le_sum fun v _ => ?_
          rw [Finset.sum_boole]
          exact lower_tail v k hk2
      _ = _ := by simp
  -- the internal-occurrence part
  have hFsum : ∑ Y : Fin M → Fin n → Fin 16, ∑ v, Fv Y v ≤
      N * (n * (C₁ + rhoB / (1 - rhoB) ^ 2)) := by
    have : ∀ Y : Fin M → Fin n → Fin 16, ∑ v, Fv Y v = ∑ i : Fin M,
        ((sample (Y i) ∩ internal ends (proc ends r C₁ T0 Y M ⟨i.val, by omega⟩)).card : ℝ) :=
      fun Y => sum_Fv ends (U Y) hMk Y
    simp only [this]
    exact sum_F_le ends r C₁ hs hn hC₁.le h31 hT0 hM hk
  have hkZ : (k : ℝ) * rhoZ ^ M ≤ 2 / (1 - rhoZ) := by
    have h1 := mul_pow_le rhoZ_pos.le rhoZ_lt M
    have h2 : (k : ℝ) ≤ 2 * M := by exact_mod_cast hk2
    have h3 : 0 ≤ rhoZ ^ M := pow_nonneg rhoZ_pos.le _
    calc (k : ℝ) * rhoZ ^ M ≤ 2 * M * rhoZ ^ M := mul_le_mul_of_nonneg_right h2 h3
      _ = 2 * (M * rhoZ ^ M) := by ring
      _ ≤ 2 * (1 / (1 - rhoZ)) := by linarith
      _ = 2 / (1 - rhoZ) := by ring
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have htot : ∑ Y : Fin M → Fin n → Fin 16, (k : ℝ) * (S Y).card ≤
      ∑ _Y : Fin M → Fin n → Fin 16, (n : ℝ) * Cst C₁ := by
    calc ∑ Y : Fin M → Fin n → Fin 16, (k : ℝ) * (S Y).card
        ≤ ∑ Y : Fin M → Fin n → Fin 16,
            ∑ v, ((k : ℝ) * (if k > 64 * Z Y v then 1 else 0) + 128 * Fv Y v) :=
          Finset.sum_le_sum fun Y _ => hpt Y
      _ = (k : ℝ) * ∑ Y : Fin M → Fin n → Fin 16, ∑ v, (if k > 64 * Z Y v then (1 : ℝ) else 0)
            + 128 * ∑ Y : Fin M → Fin n → Fin 16, ∑ v, Fv Y v := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (k : ℝ) * (n * (N * rhoZ ^ M)) + 128 * (N * (n * (C₁ + rhoB / (1 - rhoB) ^ 2))) := by
          gcongr
      _ = N * n * ((k : ℝ) * rhoZ ^ M + 128 * (C₁ + rhoB / (1 - rhoB) ^ 2)) := by ring
      _ ≤ N * n * Cst C₁ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          unfold Cst; linarith
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]; ring
  obtain ⟨Y, -, hY⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty htot
  refine ⟨U Y, S Y, hUtp Y, ?_, ?_⟩
  · have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    rw [mul_div_assoc', le_div_iff₀ hkpos]
    linarith
  · intro v hv
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv
    exact hv

end LowDiameterNashWilliams.Main.Dev.T2

namespace LowDiameterNashWilliams.Main

open LowDiameterNashWilliams.Main.Dev.T2 in
theorem chk_theorem_2 :
  ∃ C : ℝ, 0 < C ∧ ∀ n m k : ℕ, 2 ≤ n → 1 ≤ k →
  ∀ ends : Fin m → Sym2 (Fin n), Simple ends →
  (∃ T : Trees k m, TreePartition ends T) →
  ∃ (U : Trees k m) (S : Finset (Fin n)), TreePartition ends U ∧
    (S.card : ℝ) ≤ C * ((n : ℝ) / k) ∧
    ∀ v, v ∉ S → (k : ℝ) / 128 ≤ leafCount ends U (firstHalf k) v := by
  obtain ⟨C₁, hC₁, h31⟩ := lemma_3_1
  exact ⟨Cst C₁, Cst_pos hC₁, main_bound hC₁ h31⟩

end LowDiameterNashWilliams.Main
end

theorem solution : type_of% @LowDiameterNashWilliams.Main.chk_theorem_2 := @LowDiameterNashWilliams.Main.chk_theorem_2
