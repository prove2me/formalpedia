-- Prove2me | solution 1 for LX.Core.ZeroGap.root_cover_count
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:36:54.458606+00:00
-- url     : https://prove2.me/submissions/60648ba2-1b1e-41ea-9155-a60960747f70

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ZeroGapComponentSize
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Definitions.Def_LX_ZeroGapRootCoverCount
import Theorems.Thm_LX_Core_ZeroGap_graph_edges_le_events

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
/-! If a list of roots meets every event component, the number of vertices
is at most the number of exchange events plus the number of roots. -/
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]





theorem event_edge_lift {events : List (Event n)} (roots : List (Fin n))
    {i j : Fin n} (he : EventEdge events i j) :
    EventEdge (rootedEvents events roots) i.succ j.succ := by
  obtain ⟨e,he,h⟩ := he
  refine ⟨liftEvent e,List.mem_append_left _ (List.mem_map.mpr ⟨e,he,rfl⟩),?_⟩
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩

theorem event_reaches_lift {events : List (Event n)} (roots : List (Fin n))
    {i j : Fin n} (hp : EventReaches events i j) :
    EventReaches (rootedEvents events roots) i.succ j.succ := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih => exact ih.tail (event_edge_lift roots he)




end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem solution (events : List (Event n)) (roots : List (Fin n))
    (hcover : ∀ i : Fin n, ∃ r ∈ roots, EventReaches events r i) :
    n ≤ events.length+roots.length := by
  classical
  have hreach : ∀ i : Fin (n+1), EventReaches (rootedEvents events roots) 0 i := by
    intro i
    refine Fin.cases Relation.ReflTransGen.refl (fun j => ?_) i
    obtain ⟨r,hr,hp⟩ := hcover j
    have hedge : EventEdge (rootedEvents events roots) 0 r.succ :=
      ⟨(0,r.succ),List.mem_append_right _ (List.mem_map.mpr ⟨r,hr,rfl⟩),Or.inl ⟨rfl,rfl⟩⟩
    exact (Relation.ReflTransGen.single hedge).trans (event_reaches_lift roots hp)
  have hfull : eventComponent (rootedEvents events roots) 0=Finset.univ := by
    ext i
    simp only [mem_eventComponent,Finset.mem_univ,iff_true]
    exact hreach i
  have hsize := event_component_size (rootedEvents events roots) 0
  rw [hfull] at hsize
  simp only [Finset.card_univ,Fintype.card_fin,rootedEvents,List.length_append,List.length_map] at hsize
  omega
