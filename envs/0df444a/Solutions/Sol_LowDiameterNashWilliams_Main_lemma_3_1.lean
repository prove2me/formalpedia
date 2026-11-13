-- Prove2me | solution 1 for LowDiameterNashWilliams.Main.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T19:19:21.454622+00:00
-- url     : https://prove2.me/submissions/a1e4d6d1-d130-4ada-969b-dee9f3115213

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Geometry
import Definitions.Def_LowDiameterNashWilliams_Main_Reserves
import Definitions.Def_LowDiameterNashWilliams_Main_Sampling
import Definitions.Def_LowDiameterNashWilliams_Main_Computation
import Theorems.Thm_LowDiameterNashWilliams_Main_theorem_3
import Theorems.Thm_LowDiameterNashWilliams_Main_lemma_3_3

section
/-!
# Lemma 3.1 (the extraction lemma)

Objects.  `w := incidenceWeight ends L`, `weight f F = ∑ e ∈ F, f e`, `µ := maxTreeWeight ends`.
`C₃` is the constant of `lemma_3_3`; we take `C := 7 + C₃`.

* `k < 8`: `|int(Q) ∩ L| ≤ n ≤ 7 n / k ≤ C n / k`.
* `k ≥ 8` (write `k = K + 1`): ground set `Fin (K+1) × Fin m` (slot `i`, edge `e`).
  - `M₁ := Matroid.sum' (fun _ => graphic ends hs)`; its bases are the sets `B` all of whose
    slices `slice B i = {e | (i, e) ∈ B}` are spanning trees (`hM1`; the graph is connected since
    `T 0` is a spanning tree).
  - `M₂ := partitionM`; its bases are the `B` with `∀ e, ∃! i, (i, e) ∈ B` (`hM2`).
  - `assemble T` is a common base (tree partition).  `frank_fintype` transports `theorem_3` from
    `Fin (card α)` to any finite `α`.
  - `c (i, e) := if i = 0 then -w e else 0`.  `theorem_3` gives a common base `B` and
    `c = w₁ + w₂` with `B` `w₁`-optimal in `M₁` and `w₂`-optimal in `M₂`.
  - `slice B 0` is extractable (the other slices, reindexed by `Fin.succ`, partition the rest),
    so `w(Q) ≤ w(slice B 0) = -c(B) = -w₁(B) - w₂(B)` by the minimality of `Q`.
  - `q e := max_i w₂ (i, e)`, `p := -q`.  The transversal `A₂` picking an argmax in every block is
    an `M₂`-base, so `w₂(B) ≥ w₂(A₂) = ∑ q = -p(E)`.
  - With `T*` a spanning tree of maximum `(p - w)`-weight and `T'` one of maximum `p`-weight,
    `A₁ := assemble (if i = 0 then T* else T')` is an `M₁`-base, and `w₁ ≥ c - q` pointwise
    (because `w₂ ≤ q`), so `w₁(B) ≥ w₁(A₁) ≥ µ(p - w) + K µ(p)`.
  - Hence `w(Q) ≤ p(E) - (k-1) µ(p) - µ(p - w) ≤ |L| + C₃ n / k` (`lemma_3_3`, `key`).
* Finally `w(Q) = ∑_{v ∈ L} deg_Q v ≥ |L| + |int(Q) ∩ L|` since every vertex has degree `≥ 1` in
  a spanning tree on `n ≥ 2` vertices (`deg_sum`).
-/

/-!
## Part A (first half of this file): forests, the graphic matroid and a partition matroid

* `isForest_iff_acyclic`: for a simple `ends`, `IsForest ends F` iff `edgeGraph ends F` is acyclic.
* `insert_forest`: adding an edge whose ends are not joined by `F` keeps `F` a forest.
* `forest_aug`: the augmentation property for forests.  If no edge of `J` can be added to `I`, every
  edge of `J` lies inside one component `c` of `I`; inside `c`, `J` has fewer edges than `c` has
  vertices (`forest_inner_card_lt`) while `I` has at least `|c| - 1` (`conn_card_le`), so
  `|J| ≤ |I|`.
* `graphic`, `graphic_isBase_iff`: the graphic matroid on `Fin m`; when some spanning tree
  exists, its bases are exactly the spanning trees.
* `partitionM`, `partitionM_isBase_iff`: the partition matroid on `ι × β` taking at most one
  element of each block `ι × {b}`; bases pick exactly one element per block.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.L31

section Forest

variable {n m : ℕ}

theorem edgeGraph_adj (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (F : Finset (Fin m))
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

theorem edgeGraph_mono' (ends : Fin m → Sym2 (Fin n)) {F F' : Finset (Fin m)} (h : F ⊆ F') :
    edgeGraph ends F ≤ edgeGraph ends F' := by
  unfold edgeGraph
  apply SimpleGraph.fromEdgeSet_mono
  exact Set.image_mono (by exact_mod_cast h)

theorem isForest_mono' (ends : Fin m → Sym2 (Fin n)) {F F' : Finset (Fin m)} (h : F ⊆ F')
    (hF : IsForest ends F') : IsForest ends F := by
  intro e he u v huv hr
  exact hF e (h he) u v huv
    (hr.mono (edgeGraph_mono' ends (Finset.erase_subset_erase e h)))

theorem reach_transfer {V : Type*} {G H : SimpleGraph V}
    (h : ∀ x y, G.Adj x y → H.Reachable x y) {a b : V} (hab : G.Reachable a b) :
    H.Reachable a b := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

theorem edgeGraph_erase (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (F : Finset (Fin m))
    (e : Fin m) (u v : Fin n) (huv : ends e = s(u, v)) :
    edgeGraph ends (F.erase e) = (edgeGraph ends F).deleteEdges {s(u, v)} := by
  ext a b
  rw [SimpleGraph.deleteEdges_adj, edgeGraph_adj ends hs, edgeGraph_adj ends hs]
  constructor
  · rintro ⟨f, hf, hfab⟩
    rw [Finset.mem_erase] at hf
    refine ⟨⟨f, hf.2, hfab⟩, ?_⟩
    rw [Set.mem_singleton_iff, ← hfab, ← huv]
    exact fun h => hf.1 (hs.1 h)
  · rintro ⟨⟨f, hf, hfab⟩, hne⟩
    refine ⟨f, Finset.mem_erase.2 ⟨fun hfe => hne ?_, hf⟩, hfab⟩
    rw [Set.mem_singleton_iff, ← hfab, ← huv, hfe]

theorem isForest_iff_acyclic (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends)
    (F : Finset (Fin m)) : IsForest ends F ↔ (edgeGraph ends F).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  constructor
  · intro hF u v huv
    obtain ⟨e, he, heq⟩ := (edgeGraph_adj ends hs F u v).1 huv
    rw [SimpleGraph.isBridge_iff, ← edgeGraph_erase ends hs F e u v heq]
    exact hF e he u v heq
  · intro h e he u v heq
    have hadj : (edgeGraph ends F).Adj u v := (edgeGraph_adj ends hs F u v).2 ⟨e, he, heq⟩
    have := h hadj
    rw [SimpleGraph.isBridge_iff] at this
    rw [edgeGraph_erase ends hs F e u v heq]
    exact this

theorem insert_forest (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (I : Finset (Fin m))
    (hI : IsForest ends I) (e : Fin m) (u v : Fin n) (huv : ends e = s(u, v))
    (hnr : ¬ (edgeGraph ends I).Reachable u v) : IsForest ends (insert e I) := by
  rw [isForest_iff_acyclic ends hs] at hI ⊢
  have : edgeGraph ends (insert e I) = edgeGraph ends I ⊔ SimpleGraph.edge u v := by
    ext a b
    rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj, edgeGraph_adj ends hs, edgeGraph_adj ends hs]
    constructor
    · rintro ⟨f, hf, hfab⟩
      rw [Finset.mem_insert] at hf
      rcases hf with hfe | hf
      · right
        rw [hfe] at hfab
        have hnd := hs.2 e
        rw [hfab, Sym2.mk_isDiag_iff] at hnd
        have h2 := hfab.symm.trans huv
        rw [Sym2.eq_iff] at h2
        exact ⟨h2, hnd⟩
      · left
        exact ⟨f, hf, hfab⟩
    · rintro (⟨f, hf, hfab⟩ | ⟨h, -⟩)
      · exact ⟨f, Finset.mem_insert_of_mem hf, hfab⟩
      · refine ⟨e, Finset.mem_insert_self _ _, ?_⟩
        rw [huv]
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
  rw [this]
  exact hI.sup_edge_of_not_reachable hnr

theorem forest_nondiag' (ends : Fin m → Sym2 (Fin n)) {F : Finset (Fin m)}
    (hF : IsForest ends F) : ∀ e ∈ F, ¬ (ends e).IsDiag := by
  intro e he hd
  obtain ⟨u, v, huv⟩ : ∃ u v, ends e = s(u, v) := by
    induction h' : ends e using Sym2.ind with
    | _ u v => exact ⟨u, v, rfl⟩
  rw [huv, Sym2.mk_isDiag_iff] at hd
  subst hd
  exact hF e he u u huv (SimpleGraph.Reachable.refl _)

theorem forest_inj' (ends : Fin m → Sym2 (Fin n)) {F : Finset (Fin m)}
    (hF : IsForest ends F) : Set.InjOn ends (F : Set (Fin m)) := by
  intro e he e' he' h
  by_contra hne
  have hnd := forest_nondiag' ends hF e he
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

theorem acyc_card' {V : Type*} [Fintype V] [Nonempty V] (H : SimpleGraph V) [Fintype H.edgeSet]
    (hH : H.IsAcyclic) : H.edgeFinset.card + 1 ≤ Fintype.card V := by
  obtain ⟨F, hle, -, hT⟩ :=
    (SimpleGraph.connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic (le_top : H ≤ ⊤) hH
  have := hT.card_edgeFinset
  have : H.edgeFinset.card ≤ F.edgeFinset.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [SimpleGraph.mem_edgeFinset] at hx ⊢
    exact SimpleGraph.edgeSet_mono ‹H ≤ F› hx
  omega

/-- A forest has fewer edges inside a nonempty vertex set than the set has vertices. -/
theorem forest_inner_card_lt (ends : Fin m → Sym2 (Fin n)) (T : Finset (Fin m))
    (hTf : IsForest ends T) (A : Finset (Fin n)) (hA : A.Nonempty) :
    (T.filter fun e => ∀ v ∈ ends e, v ∈ A).card < A.card := by
  set F := T.filter fun e => ∀ v ∈ ends e, v ∈ A with hFdef
  have hF : IsForest ends F := isForest_mono' ends (Finset.filter_subset _ _) hTf
  have hnd := forest_nondiag' ends hF
  have hinj := forest_inj' ends hF
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
  have := acyc_card' _ hac2
  have hc : Fintype.card (A : Set (Fin n)) = A.card := Fintype.card_coe A
  rw [← hcard]
  rw [hc] at this
  have h5 : G.edgeFinset.card + 1 ≤ A.card := by
    convert this using 2
    convert hind.symm
  omega

/-- If `I` restricted to the vertex set `S` is connected and `I` has all ends in `S`, then
`|S| ≤ |I| + 1`. -/
theorem conn_card_le (ends : Fin m → Sym2 (Fin n)) (I : Finset (Fin m)) (S : Finset (Fin n))
    (hsupp : ∀ e ∈ I, ∀ v ∈ ends e, v ∈ S)
    (hconn : ((edgeGraph ends I).induce (S : Set (Fin n))).Connected) :
    S.card ≤ I.card + 1 := by
  set G := edgeGraph ends I with hG
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  have hsup : G.support ⊆ (S : Set (Fin n)) := by
    rintro v ⟨w, hvw⟩
    have hvw : G.Adj v w := hvw
    rw [hG, edgeGraph, SimpleGraph.fromEdgeSet_adj] at hvw
    obtain ⟨⟨f, hf, hfe⟩, -⟩ := hvw
    exact hsupp f hf v (by rw [hfe]; simp)
  have hind := SimpleGraph.card_edgeFinset_induce_of_support_subset hsup
  have h2 : G.edgeFinset.card ≤ I.card := by
    calc G.edgeFinset.card ≤ (I.image ends).card := by
          apply Finset.card_le_card
          intro x hx
          rw [SimpleGraph.mem_edgeFinset, hG, edgeGraph, SimpleGraph.edgeSet_fromEdgeSet] at hx
          obtain ⟨⟨e, he, rfl⟩, -⟩ := hx
          exact Finset.mem_image_of_mem _ he
      _ ≤ I.card := Finset.card_image_le
  have h3 : Nat.card (S : Set (Fin n)) = S.card := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.card_coe S
  have h4 : Nat.card ((G.induce (S : Set (Fin n))).edgeSet) =
      (G.induce (S : Set (Fin n))).edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
  rw [h3, h4] at h1
  have h5 : (G.induce (S : Set (Fin n))).edgeFinset.card = G.edgeFinset.card := by
    convert hind
  omega

theorem comp_eq_of_mem {V : Type*} (G : SimpleGraph V) (z : Sym2 V)
    (hz : ∀ u v, z = s(u, v) → G.Reachable u v) (x y : V) (hx : x ∈ z) (hy : y ∈ z) :
    G.connectedComponentMk x = G.connectedComponentMk y := by
  induction z using Sym2.ind with
  | _ u v =>
    have h := hz u v rfl
    rw [Sym2.mem_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals first
      | rfl
      | exact SimpleGraph.ConnectedComponent.sound h
      | exact (SimpleGraph.ConnectedComponent.sound h).symm

/-- The augmentation property for forests. -/
theorem forest_aug (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (I J : Finset (Fin m))
    (hI : IsForest ends I) (hJ : IsForest ends J) (hlt : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ IsForest ends (insert e I) := by
  by_contra hcon
  push Not at hcon
  set G := edgeGraph ends I with hG
  have hreachJ : ∀ e ∈ J, ∀ u v, ends e = s(u, v) → G.Reachable u v := by
    intro e he u v huv
    by_cases heI : e ∈ I
    · exact ((edgeGraph_adj ends hs I u v).2 ⟨e, heI, huv⟩).reachable
    · by_contra hnr
      exact hcon e he heI (insert_forest ends hs I hI e u v huv hnr)
  have hreachI : ∀ e ∈ I, ∀ u v, ends e = s(u, v) → G.Reachable u v := by
    intro e he u v huv
    exact ((edgeGraph_adj ends hs I u v).2 ⟨e, he, huv⟩).reachable
  let ψ : Fin m → G.ConnectedComponent := fun e => G.connectedComponentMk (ends e).out.1
  have hψI : ∀ e ∈ I, ∀ x ∈ ends e, G.connectedComponentMk x = ψ e := fun e he x hx =>
    comp_eq_of_mem G (ends e) (fun u v h => hreachI e he u v h) x _ hx (Sym2.out_fst_mem _)
  have hψJ : ∀ e ∈ J, ∀ x ∈ ends e, G.connectedComponentMk x = ψ e := fun e he x hx =>
    comp_eq_of_mem G (ends e) (fun u v h => hreachJ e he u v h) x _ hx (Sym2.out_fst_mem _)
  have key : ∀ c, (J.filter (fun e => ψ e = c)).card ≤ (I.filter (fun e => ψ e = c)).card := by
    intro c
    by_cases hne : (J.filter (fun e => ψ e = c)).Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp
    set S : Finset (Fin n) := Finset.univ.filter (fun v => G.connectedComponentMk v = c) with hS
    have hsub : J.filter (fun e => ψ e = c) ⊆ J.filter (fun e => ∀ v ∈ ends e, v ∈ S) := by
      intro e he
      rw [Finset.mem_filter] at he ⊢
      refine ⟨he.1, fun v hv => ?_⟩
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (hψJ e he.1 v hv).trans he.2⟩
    have hSne : S.Nonempty := by
      obtain ⟨e, he⟩ := hne
      rw [Finset.mem_filter] at he
      exact ⟨(ends e).out.1, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, he.2⟩⟩
    have hlt' := forest_inner_card_lt ends J hJ S hSne
    have hle1 := Finset.card_le_card hsub
    set Ic := I.filter (fun e => ψ e = c) with hIc
    have hSset : (S : Set (Fin n)) = c.supp := by
      ext v
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hS]
      simp
    have hindeq : (edgeGraph ends Ic).induce (S : Set (Fin n)) = G.induce (S : Set (Fin n)) := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      show (edgeGraph ends Ic).Adj a b ↔ G.Adj a b
      constructor
      · intro h
        exact edgeGraph_mono' ends (Finset.filter_subset _ _) h
      · intro h
        obtain ⟨f, hf, hfab⟩ := (edgeGraph_adj ends hs I a b).1 h
        refine (edgeGraph_adj ends hs Ic a b).2 ⟨f, ?_, hfab⟩
        rw [hIc, Finset.mem_filter]
        refine ⟨hf, ?_⟩
        rw [← hψI f hf a (by rw [hfab]; simp)]
        have ha' : a ∈ S := ha
        rw [hS, Finset.mem_filter] at ha'
        exact ha'.2
    have hconn : ((edgeGraph ends Ic).induce (S : Set (Fin n))).Connected := by
      rw [hindeq, hSset]
      exact c.connected_toSimpleGraph
    have hsupp : ∀ e ∈ Ic, ∀ v ∈ ends e, v ∈ S := by
      intro e he v hv
      rw [hIc, Finset.mem_filter] at he
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (hψI e he.1 v hv).trans he.2⟩
    have hle2 := conn_card_le ends Ic S hsupp hconn
    omega
  have hJsum := Finset.card_eq_sum_card_fiberwise (f := ψ) (s := J) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  have hIsum := Finset.card_eq_sum_card_fiberwise (f := ψ) (s := I) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  have : J.card ≤ I.card := by
    rw [hJsum, hIsum]
    exact Finset.sum_le_sum fun c _ => key c
  omega

end Forest

section FinMatroid

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A matroid on a finite type with ground set `univ`, from a finset independence predicate. -/
noncomputable def finMatroid (Indep : Finset α → Prop) (h0 : Indep ∅)
    (hsub : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (haug : ∀ ⦃I J⦄, Indep I → Indep J → I.card < J.card → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I)) :
    Matroid α :=
  (IndepMatroid.ofFinset Set.univ Indep h0 hsub haug (fun _ _ => Set.subset_univ _)).matroid

theorem finMatroid_indep (Indep : Finset α → Prop) (h0 hsub haug) (I : Set α) :
    (finMatroid Indep h0 hsub haug).Indep I ↔ ∀ J : Finset α, (J : Set α) ⊆ I → Indep J := by
  unfold finMatroid
  rw [IndepMatroid.matroid_indep_iff, IndepMatroid.ofFinset_indep']

theorem finMatroid_isBase (Indep : Finset α → Prop) (h0 hsub haug) (B : Finset α) :
    (finMatroid Indep h0 hsub haug).IsBase (B : Set α) ↔
      Indep B ∧ ∀ e, e ∉ B → ¬ Indep (insert e B) := by
  constructor
  · intro hB
    have hBi := (finMatroid_indep Indep h0 hsub haug _).1 hB.indep B subset_rfl
    refine ⟨hBi, fun e he hins => he ?_⟩
    have hI : (finMatroid Indep h0 hsub haug).Indep ((insert e B : Finset α) : Set α) := by
      rw [finMatroid_indep]
      intro J hJ
      exact hsub hins (by exact_mod_cast hJ)
    have := hB.eq_of_subset_indep hI (by simp)
    have hmem : e ∈ ((insert e B : Finset α) : Set α) := by simp
    rw [← this] at hmem
    exact_mod_cast hmem
  · rintro ⟨hBi, hmax⟩
    have hI : (finMatroid Indep h0 hsub haug).Indep (B : Set α) := by
      rw [finMatroid_indep]
      intro J hJ
      exact hsub hBi (by exact_mod_cast hJ)
    refine hI.isBase_of_maximal fun J hJ hBJ => ?_
    apply le_antisymm hBJ
    intro x hx
    by_contra hxB
    have hxB' : x ∉ B := by exact_mod_cast hxB
    apply hmax x hxB'
    rw [finMatroid_indep] at hJ
    apply hJ
    intro y hy
    rw [Finset.coe_insert] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact hBJ hy

end FinMatroid

section Graphic

variable {n m : ℕ}

theorem isForest_empty (ends : Fin m → Sym2 (Fin n)) : IsForest ends ∅ :=
  fun e he => absurd he (Finset.notMem_empty e)

/-- The graphic matroid of a simple graph: independent sets are forests. -/
noncomputable def graphic (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) : Matroid (Fin m) :=
  finMatroid (IsForest ends) (isForest_empty ends)
    (fun _ _ hJ hIJ => isForest_mono' ends hIJ hJ)
    (fun I J hI hJ hlt => forest_aug ends hs I J hI hJ hlt)

theorem graphic_E (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) :
    (graphic ends hs).E = Set.univ := rfl

theorem graphic_isBase_iff (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends)
    (hconn : ∃ T0, IsSpanningTree ends T0) (B : Finset (Fin m)) :
    (graphic ends hs).IsBase (B : Set (Fin m)) ↔ IsSpanningTree ends B := by
  unfold graphic
  rw [finMatroid_isBase]
  constructor
  · rintro ⟨hF, hmax⟩
    obtain ⟨T0, hT0⟩ := hconn
    refine ⟨Finset.subset_univ _, hT0.2.1, fun _ _ _ _ => Finset.mem_univ _, hF, ?_⟩
    intro u _ v _
    have hr := hT0.2.2.2.2 u (Finset.mem_univ _) v (Finset.mem_univ _)
    refine reach_transfer (fun x y hxy => ?_) hr
    obtain ⟨e, -, he⟩ := (edgeGraph_adj ends hs T0 x y).1 hxy
    by_cases heB : e ∈ B
    · exact ((edgeGraph_adj ends hs B x y).2 ⟨e, heB, he⟩).reachable
    · by_contra hnr
      exact hmax e heB (insert_forest ends hs B hF e x y he hnr)
  · intro hT
    refine ⟨hT.2.2.2.1, fun e he hins => ?_⟩
    obtain ⟨u, v, huv⟩ : ∃ u v, ends e = s(u, v) := by
      induction h' : ends e using Sym2.ind with
      | _ u v => exact ⟨u, v, rfl⟩
    apply hins e (Finset.mem_insert_self _ _) u v huv
    rw [Finset.erase_insert he]
    exact hT.2.2.2.2 u (Finset.mem_univ _) v (Finset.mem_univ _)

end Graphic

section Partition

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

/-- Independence in the partition matroid: at most one element of each block `ι × {b}`. -/
def PIndep (F : Finset (ι × β)) : Prop := ∀ b, (F.filter (fun x => x.2 = b)).card ≤ 1

theorem pindep_insert (F : Finset (ι × β)) (hF : PIndep F) (x : ι × β)
    (hx : (F.filter (fun y => y.2 = x.2)).card = 0) : PIndep (insert x F) := by
  intro b
  rw [Finset.filter_insert]
  split_ifs with hb
  · calc (insert x (F.filter (fun y => y.2 = b))).card
          ≤ (F.filter (fun y => y.2 = b)).card + 1 := Finset.card_insert_le _ _
      _ ≤ 1 := by rw [← hb, hx]
  · exact hF b

theorem pindep_aug (I J : Finset (ι × β)) (hI : PIndep I) (hJ : PIndep J)
    (hlt : I.card < J.card) : ∃ e ∈ J, e ∉ I ∧ PIndep (insert e I) := by
  obtain ⟨b, hb⟩ : ∃ b, (I.filter (fun x => x.2 = b)).card < (J.filter (fun x => x.2 = b)).card := by
    by_contra h
    push Not at h
    have hJs := Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := J) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    have hIs := Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := I) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    have : J.card ≤ I.card := by
      rw [hJs, hIs]
      exact Finset.sum_le_sum fun c _ => h c
    omega
  have hI0 : (I.filter (fun x => x.2 = b)).card = 0 := by
    have := hJ b; omega
  obtain ⟨x, hx⟩ : (J.filter (fun x => x.2 = b)).Nonempty := by
    rw [← Finset.card_pos]; omega
  rw [Finset.mem_filter] at hx
  refine ⟨x, hx.1, fun hxI => ?_, pindep_insert I hI x (by rw [hx.2]; exact hI0)⟩
  have : x ∈ I.filter (fun x => x.2 = b) := Finset.mem_filter.2 ⟨hxI, hx.2⟩
  rw [Finset.card_eq_zero] at hI0
  rw [hI0] at this
  exact Finset.notMem_empty _ this

theorem pindep_subset : ∀ ⦃I J : Finset (ι × β)⦄, PIndep J → I ⊆ J → PIndep I :=
  fun _ _ hJ hIJ b => le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hIJ)) (hJ b)

theorem pindep_empty : PIndep (∅ : Finset (ι × β)) := fun b => by simp

/-- The partition matroid on `ι × β` with blocks `ι × {b}`, capacity one. -/
noncomputable def partitionM (ι β : Type*) [Fintype ι] [DecidableEq ι] [Fintype β]
    [DecidableEq β] : Matroid (ι × β) :=
  finMatroid PIndep pindep_empty pindep_subset
    (fun I J hI hJ hlt => pindep_aug I J hI hJ hlt)

theorem partitionM_E : (partitionM ι β).E = Set.univ := rfl

theorem partitionM_isBase_iff [Nonempty ι] (B : Finset (ι × β)) :
    (partitionM ι β).IsBase (B : Set (ι × β)) ↔ ∀ b, ∃! i, (i, b) ∈ B := by
  unfold partitionM
  rw [finMatroid_isBase]
  constructor
  · rintro ⟨hBi, hmax⟩ b
    have hex : ∃ i, (i, b) ∈ B := by
      by_contra h
      push Not at h
      obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
      apply hmax (i0, b) (h i0)
      apply pindep_insert B hBi
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨j, c⟩ hjc hc
      simp only at hc
      subst hc
      exact h j hjc
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, hi, fun j hj => ?_⟩
    have := Finset.card_le_one.1 (hBi b) (j, b) (Finset.mem_filter.2 ⟨hj, rfl⟩) (i, b)
      (Finset.mem_filter.2 ⟨hi, rfl⟩)
    exact congrArg Prod.fst this
  · intro h
    refine ⟨fun b => ?_, fun x hx hins => ?_⟩
    · rw [Finset.card_le_one]
      intro x hx y hy
      rw [Finset.mem_filter] at hx hy
      obtain ⟨i, -, hu⟩ := h b
      have h1 := hu x.1 (by rw [← hx.2]; exact hx.1)
      have h2 := hu y.1 (by rw [← hy.2]; exact hy.1)
      exact Prod.ext (h1.trans h2.symm) (hx.2.trans hy.2.symm)
    · obtain ⟨j, hj, -⟩ := h x.2
      have := Finset.card_le_one.1 (hins x.2) x
        (Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, rfl⟩) (j, x.2)
        (Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem hj, rfl⟩)
      rw [this] at hx
      exact hx hj

end Partition

end LowDiameterNashWilliams.Main.Dev.L31

namespace LowDiameterNashWilliams.Main.Dev.L31

/-- `theorem_3` on an arbitrary finite ground type. -/
theorem frank_fintype {α : Type*} [Fintype α] [DecidableEq α] (M₁ M₂ : Matroid α)
    (h1 : M₁.E = Set.univ) (h2 : M₂.E = Set.univ)
    (hB : ∃ B : Finset α, M₁.IsBase (B : Set α) ∧ M₂.IsBase (B : Set α)) (w : α → ℤ) :
    ∃ (B : Finset α) (w₁ w₂ : α → ℤ), M₁.IsBase (B : Set α) ∧ M₂.IsBase (B : Set α) ∧
      w = w₁ + w₂ ∧
      (∀ A : Finset α, M₁.IsBase (A : Set α) → ∑ x ∈ A, w₁ x ≤ ∑ x ∈ B, w₁ x) ∧
      (∀ A : Finset α, M₂.IsBase (A : Set α) → ∑ x ∈ A, w₂ x ≤ ∑ x ∈ B, w₂ x) := by
  set φ := Fintype.equivFin α with hφ
  have hb : ∀ (M : Matroid α) (A : Finset (Fin (Fintype.card α))),
      (M.mapEquiv φ).IsBase (A : Set _) ↔
        M.IsBase ((A.map φ.symm.toEmbedding : Finset α) : Set α) := by
    intro M A
    rw [Matroid.mapEquiv_isBase_iff, Finset.coe_map]
    rfl
  have hb' : ∀ (M : Matroid α) (A : Finset α),
      (M.mapEquiv φ).IsBase ((A.map φ.toEmbedding : Finset _) : Set _) ↔ M.IsBase (A : Set α) := by
    intro M A
    have : (A.map φ.toEmbedding).map φ.symm.toEmbedding = A := by
      ext x; simp
    rw [hb, this]
  have hg : ∀ (M : Matroid α), M.E = Set.univ → (M.mapEquiv φ).E = Set.univ := by
    intro M hM
    rw [Matroid.mapEquiv_ground_eq, hM, Set.image_univ, Equiv.range_eq_univ]
  obtain ⟨B₀, hB₀1, hB₀2⟩ := hB
  obtain ⟨B, w₁, w₂, hB1, hB2, hw, ho1, ho2⟩ := LowDiameterNashWilliams.Main.theorem_3
    (Fintype.card α) (M₁.mapEquiv φ) (M₂.mapEquiv φ) (hg M₁ h1) (hg M₂ h2)
    ⟨B₀.map φ.toEmbedding, (hb' M₁ B₀).2 hB₀1, (hb' M₂ B₀).2 hB₀2⟩ (fun y => w (φ.symm y))
  have hsum : ∀ (g : Fin (Fintype.card α) → ℤ) (A : Finset (Fin (Fintype.card α))),
      weight g A = ∑ x ∈ A.map φ.symm.toEmbedding, g (φ x) := by
    intro g A
    unfold weight
    rw [Finset.sum_map]
    simp
  have hsum' : ∀ (g : Fin (Fintype.card α) → ℤ) (A : Finset α),
      weight g (A.map φ.toEmbedding) = ∑ x ∈ A, g (φ x) := by
    intro g A
    unfold weight
    rw [Finset.sum_map]
    rfl
  refine ⟨B.map φ.symm.toEmbedding, fun x => w₁ (φ x), fun x => w₂ (φ x), (hb M₁ B).1 hB1,
    (hb M₂ B).1 hB2, ?_, ?_, ?_⟩
  · funext x
    have := congrFun hw (φ x)
    simpa using this
  · intro A hA
    have := ho1 (A.map φ.toEmbedding) ((hb' M₁ A).2 hA)
    rw [hsum', hsum] at this
    exact this
  · intro A hA
    have := ho2 (A.map φ.toEmbedding) ((hb' M₂ A).2 hA)
    rw [hsum', hsum] at this
    exact this

section Slices

variable {n m : ℕ}

/-- The slot-`i` slice of a set of pairs. -/
def slice {K : ℕ} (B : Finset (Fin K × Fin m)) (i : Fin K) : Finset (Fin m) :=
  Finset.univ.filter fun e => (i, e) ∈ B

/-- The set of pairs whose slot-`i` slice is `S i`. -/
def assemble {K : ℕ} (S : Fin K → Finset (Fin m)) : Finset (Fin K × Fin m) :=
  Finset.univ.filter fun x => x.2 ∈ S x.1

theorem mem_slice {K : ℕ} (B : Finset (Fin K × Fin m)) (i : Fin K) (e : Fin m) :
    e ∈ slice B i ↔ (i, e) ∈ B := by simp [slice]

theorem mem_assemble {K : ℕ} (S : Fin K → Finset (Fin m)) (x : Fin K × Fin m) :
    x ∈ assemble S ↔ x.2 ∈ S x.1 := by simp [assemble]

theorem slice_assemble {K : ℕ} (S : Fin K → Finset (Fin m)) (i : Fin K) :
    slice (assemble S) i = S i := by
  ext e; simp [slice, assemble]

theorem sum_slices {K : ℕ} (B : Finset (Fin K × Fin m)) (g : Fin K × Fin m → ℤ) :
    ∑ x ∈ B, g x = ∑ i, ∑ e ∈ slice B i, g (i, e) := by
  calc ∑ x ∈ B, g x = ∑ x, if x ∈ B then g x else 0 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ i, ∑ e, if (i, e) ∈ B then g (i, e) else 0 := Fintype.sum_prod_type _
    _ = _ := by simp only [slice, Finset.sum_filter]

theorem maxTree_attained (ends : Fin m → Sym2 (Fin n)) (hconn : ∃ T0, IsSpanningTree ends T0)
    (f : Fin m → ℤ) : ∃ T, IsSpanningTree ends T ∧ weight f T = maxTreeWeight ends f := by
  obtain ⟨T0, hT0⟩ := hconn
  simp only [maxTreeWeight]
  have hne : (((Finset.univ : Edges m).powerset.filter (IsSpanningTree ends)).image
      (weight f)).Nonempty :=
    ⟨weight f T0, Finset.mem_image_of_mem _ (by simp [hT0])⟩
  rw [dif_pos hne]
  obtain ⟨T, hT, heq⟩ := Finset.mem_image.1 (Finset.max'_mem _ hne)
  exact ⟨T, (Finset.mem_filter.1 hT).2, heq⟩

end Slices

section Key

variable {n m : ℕ}

/-- The weight-splitting step: the minimum extractable weight is at most
`p(E) - (k - 1) µ(p) - µ(p - w)` for some integral `p`. -/
theorem key (ends : Fin m → Sym2 (Fin n)) (k : ℕ) (hk : 1 ≤ k) (T : Trees k m)
    (hs : Simple ends) (hTP : TreePartition ends T) (w : Fin m → ℤ) (Q : Edges m)
    (hmin : ∀ U : Edges m, Extractable ends k U → weight w Q ≤ weight w U) :
    ∃ p : Fin m → ℤ, weight w Q ≤ weight p Finset.univ - ((k : ℤ) - 1) * maxTreeWeight ends p -
      maxTreeWeight ends (fun e => p e - w e) := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  have hconn : ∃ T0, IsSpanningTree ends T0 := ⟨T 0, hTP.1.1 0⟩
  set M₁ : Matroid (Fin (K + 1) × Fin m) := Matroid.sum' (fun _ => graphic ends hs) with hM₁
  set M₂ : Matroid (Fin (K + 1) × Fin m) := partitionM (Fin (K + 1)) (Fin m) with hM₂
  have hM1 : ∀ B : Finset (Fin (K + 1) × Fin m),
      M₁.IsBase (B : Set _) ↔ ∀ i, IsSpanningTree ends (slice B i) := by
    intro B
    rw [hM₁, Matroid.sum'_isBase_iff]
    apply forall_congr'
    intro i
    rw [← graphic_isBase_iff ends hs hconn]
    have : Prod.mk i ⁻¹' (B : Set (Fin (K + 1) × Fin m)) = ((slice B i : Finset _) : Set _) := by
      ext e; simp [slice]
    rw [this]
  have hM2 : ∀ B : Finset (Fin (K + 1) × Fin m),
      M₂.IsBase (B : Set _) ↔ ∀ e, ∃! i, (i, e) ∈ B := fun B => partitionM_isBase_iff B
  have hE1 : M₁.E = Set.univ := by
    rw [hM₁, Matroid.sum'_ground_eq]
    ext ⟨i, e⟩
    simp [graphic_E]
  have hE2 : M₂.E = Set.univ := partitionM_E
  have hcommon : ∃ B : Finset (Fin (K + 1) × Fin m),
      M₁.IsBase (B : Set (Fin (K + 1) × Fin m)) ∧ M₂.IsBase (B : Set (Fin (K + 1) × Fin m)) := by
    refine ⟨assemble T, (hM1 _).2 fun i => by rw [slice_assemble]; exact hTP.1.1 i,
      (hM2 _).2 fun e => ?_⟩
    have he : e ∈ Finset.univ.biUnion T := by rw [hTP.2]; exact Finset.mem_univ e
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 he
    refine ⟨i, by simp only [mem_assemble]; exact hi, fun j hj => ?_⟩
    simp only [mem_assemble] at hj
    by_contra hne
    exact Finset.disjoint_left.1 (hTP.1.2 j i hne) hj hi
  set c : Fin (K + 1) × Fin m → ℤ := fun x => if x.1 = 0 then -w x.2 else 0 with hc
  obtain ⟨B, w₁, w₂, hB1, hB2, hcw, ho1, ho2⟩ := frank_fintype M₁ M₂ hE1 hE2 hcommon c
  have hBsl := (hM1 B).1 hB1
  have hBun := (hM2 B).1 hB2
  -- the slot-0 tree of `B` is extractable
  have hext : Extractable ends (K + 1) (slice B 0) := by
    refine ⟨hBsl 0, fun j => slice B (Fin.succ (Fin.cast (by omega) j)), fun j => hBsl _, ?_, ?_⟩
    · intro j j' hjj'
      rw [Finset.disjoint_left]
      intro e h1 h2
      rw [mem_slice] at h1 h2
      obtain ⟨i, -, hu⟩ := hBun e
      have h3 := (hu _ h1).trans (hu _ h2).symm
      apply hjj'
      ext
      have h4 := congrArg Fin.val h3
      simp at h4
      omega
    · ext e
      rw [Finset.mem_biUnion, Finset.mem_sdiff, mem_slice]
      obtain ⟨i, hi, hu⟩ := hBun e
      constructor
      · rintro ⟨j, -, hj⟩
        rw [mem_slice] at hj
        refine ⟨Finset.mem_univ _, fun h0 => ?_⟩
        have := (hu _ hj).trans (hu _ h0).symm
        exact Fin.succ_ne_zero _ this
      · rintro ⟨-, h0⟩
        have hi0 : i ≠ 0 := fun h => h0 (h ▸ hi)
        obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi0
        refine ⟨Fin.cast (by omega) i', Finset.mem_univ _, ?_⟩
        rw [mem_slice]
        simpa using hi
  have hQ := hmin _ hext
  have hcB : ∑ x ∈ B, c x = - weight w (slice B 0) := by
    rw [sum_slices, Fin.sum_univ_succ]
    simp [hc, weight, Fin.succ_ne_zero, Finset.sum_neg_distrib]
  have hsplit : ∑ x ∈ B, c x = ∑ x ∈ B, w₁ x + ∑ x ∈ B, w₂ x := by
    rw [← Finset.sum_add_distrib, hcw]
    rfl
  -- the `M₂` side
  set q : Fin m → ℤ := fun e => Finset.univ.sup' Finset.univ_nonempty (fun i => w₂ (i, e))
    with hq
  have hq_le : ∀ i e, w₂ (i, e) ≤ q e := fun i e =>
    Finset.le_sup' (fun i => w₂ (i, e)) (Finset.mem_univ i)
  choose ie hie using fun e =>
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (K + 1))) (fun i => w₂ (i, e))
  set A₂ : Finset (Fin (K + 1) × Fin m) := assemble (fun i => Finset.univ.filter fun e => ie e = i) with hA₂def
  have hA₂ : M₂.IsBase (A₂ : Set _) := by
    refine (hM2 _).2 fun e => ⟨ie e, ?_, fun j hj => ?_⟩
    · simp [hA₂def, mem_assemble]
    · simp [hA₂def, mem_assemble] at hj; exact hj.symm
  have hw2 : ∑ e, q e ≤ ∑ x ∈ B, w₂ x := by
    refine le_trans (le_of_eq ?_) (ho2 A₂ hA₂)
    rw [sum_slices]
    simp_rw [hA₂def, slice_assemble]
    rw [← Finset.sum_fiberwise Finset.univ ie q]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_filter] at he
    rw [← he.2]
    exact (hie e).2
  -- the `M₁` side
  set p : Fin m → ℤ := fun e => -q e with hp
  obtain ⟨Tst, hTst, hTstw⟩ := maxTree_attained ends hconn (fun e => p e - w e)
  obtain ⟨Tp, hTp, hTpw⟩ := maxTree_attained ends hconn p
  set A₁ : Finset (Fin (K + 1) × Fin m) := assemble (fun i => if i = 0 then Tst else Tp)
    with hA₁def
  have hA₁ : M₁.IsBase (A₁ : Set _) := by
    refine (hM1 _).2 fun i => ?_
    rw [hA₁def, slice_assemble]
    split_ifs
    · exact hTst
    · exact hTp
  have hw1 : weight (fun e => p e - w e) Tst + (K : ℤ) * weight p Tp ≤ ∑ x ∈ B, w₁ x := by
    refine le_trans ?_ (ho1 A₁ hA₁)
    rw [sum_slices]
    simp_rw [hA₁def, slice_assemble]
    rw [Fin.sum_univ_succ]
    simp only [if_true, Fin.succ_ne_zero, if_false]
    have h0 : weight (fun e => p e - w e) Tst ≤ ∑ e ∈ Tst, w₁ (0, e) := by
      unfold weight
      apply Finset.sum_le_sum
      intro e _
      have h1 := congrFun hcw (0, e)
      have h2 := hq_le 0 e
      simp only [hc, Pi.add_apply, if_true] at h1
      simp only [hp]
      linarith
    have hs' : (K : ℤ) * weight p Tp ≤ ∑ i : Fin K, ∑ e ∈ Tp, w₁ (i.succ, e) := by
      have : ∀ i : Fin K, weight p Tp ≤ ∑ e ∈ Tp, w₁ (i.succ, e) := by
        intro i
        unfold weight
        apply Finset.sum_le_sum
        intro e _
        have h1 := congrFun hcw (i.succ, e)
        have h2 := hq_le i.succ e
        simp only [hc, Pi.add_apply, Fin.succ_ne_zero, if_false] at h1
        simp only [hp]
        linarith
      calc (K : ℤ) * weight p Tp = ∑ _i : Fin K, weight p Tp := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => this i
    linarith
  refine ⟨p, ?_⟩
  have hwu : weight p Finset.univ = - ∑ e, q e := by
    simp [weight, hp, Finset.sum_neg_distrib]
  rw [← hTstw, ← hTpw]
  have hK : ((K + 1 : ℕ) : ℤ) - 1 = K := by push_cast; ring
  rw [hK]
  linarith

end Key

section Degrees

variable {n m : ℕ}

theorem weight_incidence (ends : Fin m → Sym2 (Fin n)) (L : Finset (Fin n)) (Q : Edges m) :
    weight (incidenceWeight ends L) Q = ∑ v ∈ L, (degIn ends Q v : ℤ) := by
  unfold weight incidenceWeight degIn
  simp only [Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]

theorem deg_pos (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (hn : 2 ≤ n) (Q : Edges m)
    (hQ : IsSpanningTree ends Q) (v : Fin n) : 1 ≤ degIn ends Q v := by
  obtain ⟨u, hu⟩ : ∃ u : Fin n, u ≠ v := by
    by_cases h : v = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h h'.symm⟩
  obtain ⟨p⟩ := hQ.2.2.2.2 v (Finset.mem_univ _) u (Finset.mem_univ _)
  cases p with
  | nil => exact absurd rfl hu
  | cons h _ =>
    obtain ⟨e, he, heq⟩ := (edgeGraph_adj ends hs Q _ _).1 h
    unfold degIn
    exact Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨he, by rw [heq]; simp⟩⟩

theorem deg_sum (ends : Fin m → Sym2 (Fin n)) (hs : Simple ends) (hn : 2 ≤ n) (Q : Edges m)
    (hQ : IsSpanningTree ends Q) (L : Finset (Fin n)) :
    (L.card : ℤ) + ((internal ends Q ∩ L).card : ℤ) ≤ weight (incidenceWeight ends L) Q := by
  rw [weight_incidence]
  have h : ∀ v ∈ L, (1 : ℤ) + (if v ∈ internal ends Q then 1 else 0) ≤ degIn ends Q v := by
    intro v _
    split_ifs with h
    · unfold internal at h
      rw [Finset.mem_filter] at h
      have := h.2
      omega
    · have := deg_pos ends hs hn Q hQ v
      omega
  have hcard : (internal ends Q ∩ L) = L.filter (fun v => v ∈ internal ends Q) := by
    ext v; simp [and_comm]
  calc (L.card : ℤ) + ((internal ends Q ∩ L).card : ℤ)
        = ∑ v ∈ L, ((1 : ℤ) + if v ∈ internal ends Q then 1 else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_boole, hcard]
          simp
    _ ≤ _ := Finset.sum_le_sum h

end Degrees

end LowDiameterNashWilliams.Main.Dev.L31

namespace LowDiameterNashWilliams.Main

open LowDiameterNashWilliams.Main.Dev.L31 in
theorem chk_lemma_3_1 :
  ∃ C : ℝ, 0 < C ∧ ∀ n m k : ℕ, 2 ≤ n → 1 ≤ k →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Trees k m)
    (D : Fin k → Direction n m) (r : Fin n) (L : Finset (Fin n)) (Q : Edges m),
  Simple ends → TreePartition ends T → (∀ i, Toward ends (T i) (D i) r) →
  (∀ v, (outgoingTo T D v L : ℝ) ≤ (k : ℝ) / 8) →
  Extractable ends k Q →
  (∀ U : Edges m, Extractable ends k U →
    weight (incidenceWeight ends L) Q ≤ weight (incidenceWeight ends L) U) →
    (((internal ends Q ∩ L).card : ℕ) : ℝ) ≤ C * ((n : ℝ) / k) := by
  obtain ⟨C₃, hC₃pos, hC₃⟩ := lemma_3_3
  refine ⟨7 + C₃, by linarith, ?_⟩
  intro n m k hn hk ends T D r L Q hs hTP hTow hout hQ hmin
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  have hnk : (0 : ℝ) ≤ (n : ℝ) / k := div_nonneg (Nat.cast_nonneg _) hkpos.le
  by_cases hk8 : k < 8
  · have h1 : (internal ends Q ∩ L).card ≤ n := by
      calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
        _ = n := by simp
    have h2 : (n : ℝ) ≤ 7 * ((n : ℝ) / k) := by
      rw [mul_div_assoc', le_div_iff₀ hkpos]
      have : (k : ℝ) ≤ 7 := by exact_mod_cast (by omega : k ≤ 7)
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h3 : (((internal ends Q ∩ L).card : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
    nlinarith [mul_nonneg hC₃pos.le hnk]
  · have hk8' : 8 ≤ k := by omega
    obtain ⟨p, hp⟩ := key ends k hk T hs hTP (incidenceWeight ends L) Q hmin
    have h33 := hC₃ n m k hn hk8' ends T D r L hs hTP hTow hout p
    have hdeg := deg_sum ends hs hn Q hQ.1 L
    have hp' : ((weight (incidenceWeight ends L) Q : ℤ) : ℝ) ≤
        ((weight p Finset.univ - ((k : ℤ) - 1) * maxTreeWeight ends p -
          maxTreeWeight ends (fun e => p e - incidenceWeight ends L e) : ℤ) : ℝ) := by
      exact_mod_cast hp
    have hdeg' : ((L.card : ℤ) : ℝ) + (((internal ends Q ∩ L).card : ℤ) : ℝ) ≤
        ((weight (incidenceWeight ends L) Q : ℤ) : ℝ) := by
      exact_mod_cast hdeg
    simp only [Int.cast_natCast] at hdeg'
    have : (((internal ends Q ∩ L).card : ℕ) : ℝ) ≤ C₃ * ((n : ℝ) / k) := by linarith
    nlinarith

end LowDiameterNashWilliams.Main
end

theorem solution : type_of% @LowDiameterNashWilliams.Main.chk_lemma_3_1 := @LowDiameterNashWilliams.Main.chk_lemma_3_1
