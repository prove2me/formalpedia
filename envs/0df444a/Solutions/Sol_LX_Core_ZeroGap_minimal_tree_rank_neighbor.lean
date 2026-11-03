-- Prove2me | solution 1 for LX.Core.ZeroGap.minimal_tree_rank_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:41:20.164451+00:00
-- url     : https://prove2.me/submissions/9a4c43ad-8470-4025-85ee-7c181bc43c90

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
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Theorems.Thm_LX_Core_ZeroGap_component_selected_size
import Theorems.Thm_LX_Core_ZeroGap_event_product_fixed
import Theorems.Thm_LX_Core_ZeroGap_minimal_tree_neighbor_away
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
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]













@[simp] theorem mem_endpoints (events : List (Event n)) (i : Fin n) :
    i ∈ endpoints events ↔ ∃ e ∈ events, i=e.1 ∨ i=e.2 := by
  simp [endpoints]






end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem event_component_reroot (events : List (Event n)) {a b : Fin n}
    (hab : EventReaches events a b) : eventComponent events a=eventComponent events b := by
  ext i
  simp only [mem_eventComponent]
  exact ⟨fun h => (event_reaches_symm events hab).trans h,fun h => hab.trans h⟩

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

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- Existence of an actual arrow between adjacent carrier ranks, including
the two-vertex case. No neighboring-arrow premise remains. -/
theorem solution (events : List (Event n)) (root : Fin n)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (hmin : events.length+1=(eventComponent events root).card)
    (hcard : 2 ≤ (eventComponent events root).card) :
    ∃ x y, RankAdjacent (eventComponent events root) x y ∧ (events.map eventSwap).prod x=y := by
  classical
  let S := eventComponent events root
  change 2 ≤ S.card at hcard
  have hne : S.Nonempty := ⟨root,(mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl⟩
  let a := S.min' hne
  have ha : a ∈ S := Finset.min'_mem S hne
  have hr := (mem_eventComponent events root a).mp ha
  have heq := event_component_reroot events hr
  by_cases hc2 : S.card=2
  · obtain ⟨x,y,hxy,hp,_⟩ := minimal_two_vertex_neighbor events root hmin hlinear hc2 root
      ((mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl)
    exact ⟨x,y,hxy,hp⟩
  · have h3 : 3 ≤ (eventComponent events a).card := by rw [← heq]; change 3 ≤ S.card; omega
    have hx : IsExtreme (eventComponent events a) a := by
      left
      intro i hi
      rw [← heq] at hi
      exact Finset.min'_le S i hi
    obtain ⟨x,y,hxy,hp,_,_⟩ := minimal_tree_neighbor_away events a hlinear hsep
      (by rwa [← heq]) h3 hx
    exact ⟨x,y,by rwa [← heq] at hxy,hp⟩
