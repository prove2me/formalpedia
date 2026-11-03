-- Prove2me | solution 1 for LX.Core.ZeroGap.opposite_moving_neighbor_step
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:34:57.49121+00:00
-- url     : https://prove2.me/submissions/bdb8c681-58b2-4a5b-a316-a4b4914cc2d6

/-
Adapted from https://github.com/snow-ghost/glushkov-lx-lean at 8cddcd222b591673dc63475d9d45b9ed5c6eb92c.
MIT License

Copyright (c) 2026 S. Uskov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Mathlib
import Definitions.Def_LX_AffineCrossings
import Definitions.Def_LX_ExtremeEventBranch
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ShallowNeighborSplice
import Definitions.Def_LX_TwoMovingNeighborStep
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapComponentSize
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Theorems.Thm_LX_Core_ZeroGap_component_selected_size
import Theorems.Thm_LX_Core_ZeroGap_event_product_fixed
import Theorems.Thm_LX_Core_ZeroGap_graph_edges_le_events
import Theorems.Thm_LX_Core_ZeroGap_head_branch_minimal
import Theorems.Thm_LX_Core_ZeroGap_head_component_union
import Theorems.Thm_LX_Core_ZeroGap_head_components_cover
import Theorems.Thm_LX_Core_ZeroGap_head_rank_adjacent
import Theorems.Thm_LX_Core_ZeroGap_opposite_branch_interval
import Theorems.Thm_LX_Core_ZeroGap_selected_product_agrees
import Theorems.Thm_LX_Core_ZeroGap_two_vertex_neighbor_avoids_target

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

section
/-!
The L/R/X Cayley graph on `Equiv.Perm (Fin n)`. Right multiplication acts
on positions: `L` rotates the list to the left, `R` to the right, and `X`
exchanges its first two entries. The extended diameter avoids the convention
that a disconnected graph has natural-valued diameter zero.
-/
namespace LX.Core



















@[simp] theorem eval_nil {n : ℕ} [NeZero n] : eval (n := n) [] = 1 := rfl

@[simp] theorem eval_cons {n : ℕ} [NeZero n] (a : Letter) (w : List Letter) :
    eval (n := n) (a :: w) = a.eval * eval w := by simp [eval]

@[simp] theorem eval_append {n : ℕ} [NeZero n] (u v : List Letter) :
    eval (n := n) (u ++ v) = eval u * eval v := by simp [eval]






end LX.Core

end

section
/-! Signed affine crossing data obtained from an actual balanced phase lift.
The row-sum identity is proved from bijectivity of endpoint residues. -/
namespace LX.Core.AffineLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]






















@[simp] theorem crossing_self (d : Fin n → ℤ) (i : Fin n) : crossing d i i = 0 := by
  simp [crossing, crossingNumerator]









end LX.Core.AffineLift

end

section
/-! Physical positions, a paid cursor, and literal L/R/X words.
Every physical operation is proved to induce the same visible generator.
A realized balanced lift ends at the original target in its exact orientation. -/
namespace LX.Core.PhysicalModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open AffineLift



variable {n : ℕ} [NeZero n]















@[simp] theorem visible_initial : visible (initial (n := n)) = 1 := by
  simp [visible, initial]


end LX.Core.PhysicalModel

end

section
/-! Connected components of the event graph contain the cycles of the
original permutation and are invariant under it. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]







theorem event_reaches_symm (events : List (Event n)) {i j : Fin n} (h : EventReaches events i j) :
    EventReaches events j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih => exact (Relation.ReflTransGen.single (event_edge_symm events he)).trans ih















end LX.Core.ZeroGap

end

section
/-! Every connected component of the event graph uses at least one fewer
exchange events than its number of vertices. -/
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]





theorem component_root_path (events : List (Event n)) (root : Fin n) {j : Fin n}
    (hp : EventReaches events root j) :
    (componentGraph events root).Reachable (rootVertex events root)
      ⟨j,(mem_eventComponent events root j).mpr hp⟩ := by
  induction hp with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail u v hp he ih =>
    by_cases huv : u=v
    · subst v
      exact ih
    · have ha : (componentGraph events root).Adj
          ⟨u,(mem_eventComponent events root u).mpr hp⟩
          ⟨v,(mem_eventComponent events root v).mpr (hp.tail he)⟩ :=
        ⟨fun h => huv (congrArg Subtype.val h),he⟩
      exact ih.trans ha.reachable

theorem component_graph_connected (events : List (Event n)) (root : Fin n) :
    (componentGraph events root).Connected := by
  letI : Nonempty {i : Fin n // i ∈ eventComponent events root} := ⟨rootVertex events root⟩
  constructor
  intro i j
  have hi := component_root_path events root ((mem_eventComponent events root i.val).mp i.property)
  have hj := component_root_path events root ((mem_eventComponent events root j.val).mp j.property)
  exact hi.symm.trans hj

theorem event_component_size (events : List (Event n)) (root : Fin n) :
    (eventComponent events root).card ≤ events.length+1 := by
  classical
  let G := componentGraph events root
  have hvertices := (component_graph_connected events root).card_vert_le_card_edgeSet_add_one
  have hedges := graph_edges_le_events G events Subtype.val Subtype.val_injective (fun i j h => h.2)
  have hcard : Nat.card {i : Fin n // i ∈ eventComponent events root}=(eventComponent events root).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe _
  change Nat.card {i : Fin n // i ∈ eventComponent events root} ≤ Nat.card G.edgeSet+1 at hvertices
  rw [hcard] at hvertices
  omega



end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]



/-- Minimal event count forces the first event to join different tail
components. This avoids assuming the graph is a tree as a new premise. -/
theorem head_endpoints_disconnected (e : Event n) (events : List (Event n))
    (hminimal : (e::events).length+1=(eventComponent (e::events) e.1).card) :
    ¬EventReaches events e.1 e.2 := by
  intro hab
  have hsub : eventComponent (e::events) e.1 ⊆ eventComponent events e.1 := by
    intro i hi
    apply (mem_eventComponent events e.1 i).mpr
    have h := head_components_cover e events ((mem_eventComponent (e::events) e.1 i).mp hi)
    exact h.elim id (fun h => hab.trans h)
  have hcard := Finset.card_le_card hsub
  have htail := event_component_size events e.1
  simp only [List.length_cons] at hminimal
  omega






end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]







theorem component_edge_selected {events : List (Event n)} {root i j : Fin n}
    (hi : EventReaches events root i) (he : EventEdge events i j) :
    EventEdge (componentEvents events root) i j := by
  classical
  obtain ⟨e,he,h⟩ := he
  have hr : EventReaches events root e.1 := by
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hi
    · exact hi.tail ⟨e,he,Or.inr ⟨rfl,rfl⟩⟩
  exact ⟨e,by simp [componentEvents,he,hr],h⟩





@[simp] theorem mem_endpoints (events : List (Event n)) (i : Fin n) :
    i ∈ endpoints events ↔ ∃ e ∈ events, i=e.1 ∨ i=e.2 := by
  simp [endpoints]






end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem event_reaches_mono {xs ys : List (Event n)} (hsub : ∀ e ∈ xs, e ∈ ys)
    {a b : Fin n} (hp : EventReaches xs a b) : EventReaches ys a b := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih =>
    obtain ⟨e,he,h⟩ := he
    exact ih.tail ⟨e,hsub e he,h⟩










end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem selected_reaches_iff (events : List (Event n)) (root i : Fin n) :
    EventReaches (componentEvents events root) root i ↔ EventReaches events root i := by
  classical
  constructor
  · apply event_reaches_mono
    intro e he
    exact (List.mem_filter.mp he).1
  · intro hp
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail hp he ih => exact ih.tail (component_edge_selected hp he)

theorem selected_component_eq (events : List (Event n)) (root : Fin n) :
    eventComponent (componentEvents events root) root=eventComponent events root := by
  ext i
  simp only [mem_eventComponent,selected_reaches_iff]





end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ}





theorem rank_adjacent_of_interval {T S : Finset (Fin n)} (hT : CarrierInterval T S)
    {x y : Fin n} (hxy : RankAdjacent T x y) : RankAdjacent S x y := by
  refine ⟨hT.1 hxy.1,hT.1 hxy.2.1,hxy.2.2.1,?_⟩
  intro z hz hz'
  exact hxy.2.2.2 z (hT.2 x hxy.1 y hxy.2.1 z hz hz'.1 hz'.2) hz'







/-- A neighboring arrow in an interval branch survives restoration of a
head exchange, provided its target avoids the attachment vertex. The
excluded outer vertex is absent from both ends of the resulting arrow. -/
theorem splice_neighbor_from_interval (q : State n) (T S : Finset (Fin n))
    (hT : CarrierInterval T S) (a b excluded : Fin n)
    (ha : a ∉ T) (hexcluded : excluded ∉ T)
    (hneighbor : ∃ x y : Fin n, RankAdjacent T x y ∧ q x=y ∧ y ≠ b) :
    ∃ x y : Fin n, RankAdjacent S x y ∧ (Equiv.swap a b*q) x=y ∧
      x ≠ excluded ∧ y ≠ excluded := by
  obtain ⟨x,y,hxy,hq,hyb⟩ := hneighbor
  have hya : y ≠ a := fun h => ha (h ▸ hxy.2.1)
  refine ⟨x,y,rank_adjacent_of_interval hT hxy,?_,?_,?_⟩
  · rw [Equiv.Perm.mul_apply,hq,Equiv.swap_apply_of_ne_of_ne hya hyb]
  · intro h
    exact hexcluded (h ▸ hxy.1)
  · intro h
    exact hexcluded (h ▸ hxy.2.1)





end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]



theorem minimal_events_reachable (events : List (Event n)) (root : Fin n)
    (hmin : events.length+1=(eventComponent events root).card) :
    ∀ e ∈ events, EventReaches events root e.1 := by
  classical
  have hc := component_selected_size events root
  have hl : (componentEvents events root).length ≤ events.length := List.length_filter_le _ _
  have heq : (componentEvents events root).length=events.length := by omega
  have h := List.length_filter_eq_length_iff.mp heq
  intro e he
  exact of_decide_eq_true (h e he)

theorem minimal_product_support_subset (events : List (Event n)) (root : Fin n)
    (hmin : events.length+1=(eventComponent events root).card) :
    (events.map eventSwap).prod.support ⊆ eventComponent events root := by
  classical
  intro i hi
  by_contra hnot
  have hne : i ∉ endpoints events := by
    intro hm
    obtain ⟨e,he,hor⟩ := (mem_endpoints events i).mp hm
    have hroot := minimal_events_reachable events root hmin e he
    apply hnot
    apply (mem_eventComponent events root i).mpr
    rcases hor with rfl | rfl
    · exact hroot
    · exact hroot.tail ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
  exact (Equiv.Perm.mem_support.mp hi) (event_product_fixed events i hne)

theorem minimal_two_vertex_support (events : List (Event n)) (root : Fin n)
    (hmin : events.length+1=(eventComponent events root).card)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val)
    (hcard : (eventComponent events root).card=2) :
    (events.map eventSwap).prod.support=eventComponent events root := by
  classical
  have hlen : events.length=1 := by omega
  have hp : (events.map eventSwap).prod.support.card=2 := by
    obtain ⟨e,rfl⟩ := List.length_eq_one_iff.mp hlen
    have he := hlinear e (by simp)
    have hne : e.1 ≠ e.2 := by intro h; have := congrArg Fin.val h; omega
    simpa [eventSwap] using Equiv.Perm.card_support_swap hne
  exact Finset.eq_of_subset_of_card_le (minimal_product_support_subset events root hmin) (by omega)

theorem minimal_two_vertex_neighbor (events : List (Event n)) (root : Fin n)
    (hmin : events.length+1=(eventComponent events root).card)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val)
    (hcard : (eventComponent events root).card=2)
    (r : Fin n) (hr : r ∈ eventComponent events root) :
    ∃ x y, RankAdjacent (eventComponent events root) x y ∧
      (events.map eventSwap).prod x=y ∧ y ≠ r := by
  have hs := minimal_two_vertex_support events root hmin hlinear hcard
  obtain ⟨x,y,hxy,hp,hy⟩ := two_vertex_neighbor_avoids_target
    (events.map eventSwap).prod (by rw [hs]; exact hcard) r (by rwa [hs])
  exact ⟨x,y,by rwa [hs] at hxy,hp,hy⟩



end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]



theorem rank_adjacent_symm {S : Finset (Fin n)} {a b : Fin n}
    (h : RankAdjacent S a b) : RankAdjacent S b a := by
  refine ⟨h.2.1,h.1,Ne.symm h.2.2.1,?_⟩
  intro i hi
  simpa only [min_comm,max_comm] using h.2.2.2 i hi




end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]



theorem minimal_tree_safe_neighbor (events : List (Event n)) (root r : Fin n)
    (hmin : events.length+1=(eventComponent events root).card)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val)
    (hcard : 2 ≤ (eventComponent events root).card) (hr : r ∈ eventComponent events root)
    (ih : 3 ≤ (eventComponent events root).card → NeighborAway events root r) :
    ∃ x y, RankAdjacent (eventComponent events root) x y ∧
      (events.map eventSwap).prod x=y ∧ y ≠ r := by
  by_cases htwo : (eventComponent events root).card=2
  · exact minimal_two_vertex_neighbor events root hmin hlinear htwo r hr
  · obtain ⟨x,y,hxy,hp,_,hy⟩ := ih (by omega)
    exact ⟨x,y,hxy,hp,hy⟩




end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- The complete two-moving-branches step. The only inductive inputs are
neighbor statements for smaller, already selected branches. -/
theorem solution (e : Event n) (events : List (Event n))
    (hlinear : ∀ f ∈ e::events, f.1.val < f.2.val)
    (hsep : (e::events).Pairwise LaterOutside)
    (hmin : (e::events).length+1=(eventComponent (e::events) e.1).card)
    (r : Fin n)
    (ha : EventReaches events e.2 r → 2 ≤ (eventComponent events e.1).card)
    (hb : EventReaches events e.1 r → 2 ≤ (eventComponent events e.2).card)
    (ih : ∀ b ∈ [e.1,e.2], 3 ≤ (eventComponent events b).card →
      IsExtreme (eventComponent events b) b → NeighborAway (componentEvents events b) b b)
    (hr : r ∈ eventComponent (e::events) e.1)
    (hext : IsExtreme (eventComponent (e::events) e.1) r) :
    NeighborAway (e::events) e.1 r := by
  classical
  let S := eventComponent (e::events) e.1
  have hab := head_endpoints_disconnected e events hmin
  have hba : ¬EventReaches events e.2 e.1 := fun h => hab (event_reaches_symm events h)
  have hm := head_branch_minimal e events hmin
  have hl : ∀ f ∈ events, f.1.val < f.2.val := fun f hf => hlinear f (List.mem_cons_of_mem e hf)
  have hs := (List.pairwise_cons.mp hsep).2
  have hgap := head_rank_adjacent e events (hlinear e (by simp)) hsep
  have hcover (i : Fin n) (hi : i ∈ S) :
      EventReaches events e.1 i ∨ EventReaches events e.2 i :=
    head_components_cover e events ((mem_eventComponent _ _ _).mp hi)
  have hsubA : eventComponent events e.1 ⊆ S := by
    dsimp [S]; rw [head_component_union]; exact Finset.subset_union_left
  have hsubB : eventComponent events e.2 ⊆ S := by
    dsimp [S]; rw [head_component_union]; exact Finset.subset_union_right
  have safe (b : Fin n) (hbm : b ∈ [e.1,e.2])
      (hmb : (componentEvents events b).length+1=(eventComponent events b).card)
      (hcb : 2 ≤ (eventComponent events b).card) (hxb : IsExtreme (eventComponent events b) b) :
      ∃ x y, RankAdjacent (eventComponent events b) x y ∧
        (events.map eventSwap).prod x=y ∧ y ≠ b := by
    have hlin : ∀ f ∈ componentEvents events b, f.1.val < f.2.val :=
      fun f hf => hl f (List.mem_filter.mp hf).1
    obtain ⟨x,y,hxy,hp,hy⟩ := minimal_tree_safe_neighbor (componentEvents events b) b b
      (by rwa [selected_component_eq]) hlin (by rwa [selected_component_eq])
      ((mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl)
      (fun h => ih b hbm (by rwa [selected_component_eq] at h) hxb)
    rw [selected_component_eq] at hxy
    have hx := (mem_eventComponent events b x).mp hxy.1
    exact ⟨x,y,hxy,(selected_product_agrees events b x hx).symm.trans hp,hy⟩
  rcases hcover r hr with har | hbr
  · obtain ⟨hinterval,hboundary⟩ := opposite_branch_interval events hl hs S e.1 e.2 r
      hab har hsubB hcover hext hgap
    have hna : e.1 ∉ eventComponent events e.2 := fun h => hba ((mem_eventComponent _ _ _).mp h)
    have hnr : r ∉ eventComponent events e.2 := fun h =>
      hab (har.trans (event_reaches_symm events ((mem_eventComponent _ _ _).mp h)))
    obtain ⟨x,y,hxy,hp,hxr,hyr⟩ := splice_neighbor_from_interval (events.map eventSwap).prod
      (eventComponent events e.2) S hinterval e.1 e.2 r hna hnr (safe e.2 (by simp) hm.2 (hb har) hboundary)
    exact ⟨x,y,hxy,by simpa only [List.map_cons,List.prod_cons,eventSwap] using hp,hxr,hyr⟩
  · obtain ⟨hinterval,hboundary⟩ := opposite_branch_interval events hl hs S e.2 e.1 r
      hba hbr hsubA (fun i hi => (hcover i hi).symm) hext (rank_adjacent_symm hgap)
    have hna : e.2 ∉ eventComponent events e.1 := fun h => hab ((mem_eventComponent _ _ _).mp h)
    have hnr : r ∉ eventComponent events e.1 := fun h =>
      hba (hbr.trans (event_reaches_symm events ((mem_eventComponent _ _ _).mp h)))
    obtain ⟨x,y,hxy,hp,hxr,hyr⟩ := splice_neighbor_from_interval (events.map eventSwap).prod
      (eventComponent events e.1) S hinterval e.2 e.1 r hna hnr (safe e.1 (by simp) hm.1 (ha hbr) hboundary)
    exact ⟨x,y,hxy,by simpa only [List.map_cons,List.prod_cons,eventSwap,Equiv.swap_comm e.2 e.1] using hp,hxr,hyr⟩
