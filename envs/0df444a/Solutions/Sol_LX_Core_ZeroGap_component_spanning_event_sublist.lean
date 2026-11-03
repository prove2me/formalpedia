-- Prove2me | solution 1 for LX.Core.ZeroGap.component_spanning_event_sublist
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:28:29.929521+00:00
-- url     : https://prove2.me/submissions/ffe3da1a-4f7d-4f90-aeb6-92de043f0787

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
import Definitions.Def_LX_SelectedEventEdges
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapComponentSize
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Theorems.Thm_LX_Core_ZeroGap_select_event_edges

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
variable {n : ℕ}





theorem event_edge_key_iff (events : List (Event n)) (i j : Fin n) :
    Sym2.mk i j ∈ (events.map eventEdgeKey).toFinset ↔ EventEdge events i j := by
  classical
  simp only [List.mem_toFinset,List.mem_map,eventEdgeKey,Sym2.eq_iff,EventEdge]
  constructor
  · rintro ⟨e,he,⟨hi,hj⟩ | ⟨hi,hj⟩⟩
    · exact ⟨e,he,Or.inl ⟨hi.symm,hj.symm⟩⟩
    · exact ⟨e,he,Or.inr ⟨hj.symm,hi.symm⟩⟩
  · rintro ⟨e,he,⟨hi,hj⟩ | ⟨hi,hj⟩⟩
    · exact ⟨e,he,Or.inl ⟨hi.symm,hj.symm⟩⟩
    · exact ⟨e,he,Or.inr ⟨hj.symm,hi.symm⟩⟩


end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- An actual event component admits an order-preserving spanning tree subsequence. -/
theorem solution (events : List (Event n)) (root : Fin n) :
    ∃ part : List (Event n), part.Sublist events ∧
      eventComponent part root = eventComponent events root ∧
      part.length+1 = (eventComponent events root).card ∧
      (∀ e ∈ part, e.1 ≠ e.2) ∧ (part.map eventEdgeKey).Nodup := by
  classical
  let C := {i : Fin n // i ∈ eventComponent events root}
  obtain ⟨T,hTG,hTree⟩ := (component_graph_connected events root).exists_isTree_le
  letI : Fintype T.edgeSet := Fintype.ofFinite _
  let keys : Finset (Sym2 (Fin n)) := T.edgeFinset.image (Sym2.map (Subtype.val : C → Fin n))
  have hsubkeys : keys ⊆ (events.map eventEdgeKey).toFinset := by
    intro q hq
    obtain ⟨edge,hedge,rfl⟩ := Finset.mem_image.mp hq
    revert hedge
    refine Sym2.inductionOn edge ?_
    intro a b hab
    have ha : T.Adj a b := T.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp hab)
    have he : EventEdge events a.val b.val := (hTG ha).2
    exact (event_edge_key_iff events a.val b.val).mpr he
  obtain ⟨part,hpart,hnodup,hkeys,hlen⟩ := select_event_edges events keys hsubkeys
  have hstep {a b : C} (hab : T.Adj a b) : EventEdge part a.val b.val := by
    apply (event_edge_key_iff part _ _).mp
    rw [hkeys]
    apply Finset.mem_image.mpr
    exact ⟨Sym2.mk a b,SimpleGraph.mem_edgeFinset.mpr (T.mem_edgeSet.mpr hab),rfl⟩
  have hreach {a b : C} (hab : T.Reachable a b) : EventReaches part a.val b.val := by
    have hh := (T.reachable_iff_reflTransGen a b).mp hab
    clear hab
    induction hh with
    | refl => exact Relation.ReflTransGen.refl
    | tail hp he ih => exact ih.tail (hstep he)
  have hcomp : eventComponent part root = eventComponent events root := by
    ext i
    constructor
    · intro hi
      exact (mem_eventComponent _ _ _).mpr
        (event_reaches_mono (fun e he => hpart.subset he) ((mem_eventComponent _ _ _).mp hi))
    · intro hi
      exact (mem_eventComponent _ _ _).mpr
        (hreach (hTree.connected.preconnected (rootVertex events root) ⟨i,hi⟩))
  have hcard : keys.card = T.edgeFinset.card :=
    Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
  have hsize := hTree.card_edgeFinset
  have hC : Fintype.card C = (eventComponent events root).card := Fintype.card_coe _
  change T.edgeFinset.card+1 = Fintype.card C at hsize
  rw [hC] at hsize
  have hneq : ∀ e ∈ part, e.1 ≠ e.2 := by
    intro e he hsame
    have hk : eventEdgeKey e ∈ keys := by
      rw [← hkeys]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,he,rfl⟩)
    obtain ⟨edge,hedge,heq⟩ := Finset.mem_image.mp hk
    revert hedge heq
    refine Sym2.inductionOn edge ?_
    intro a b hab heq
    have ha : T.Adj a b := T.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp hab)
    have hh : a.val = b.val := by
      simp only [Sym2.map_mk,eventEdgeKey,Sym2.eq_iff] at heq
      rcases heq with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> simp_all
    exact ha.ne (Subtype.ext hh)
  refine ⟨part,hpart,hcomp,?_,hneq,hnodup⟩
  omega
