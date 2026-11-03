-- Prove2me | solution 1 for LX.Core.ZeroGap.minimal_tree_neighbor_away
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:39:26.915374+00:00
-- url     : https://prove2.me/submissions/b58fc841-aa7e-454f-9b30-b934bac70b55

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
import Theorems.Thm_LX_Core_ZeroGap_event_neighbor_induction_step
import Theorems.Thm_LX_Core_ZeroGap_head_branch_minimal

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









end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- A minimal linear event tree on at least three vertices has a neighboring
arrow avoiding any prescribed extreme vertex of its carrier. -/
theorem solution (events : List (Event n)) (root : Fin n)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (hmin : events.length+1=(eventComponent events root).card)
    (hcard : 3 ≤ (eventComponent events root).card)
    (hext : IsExtreme (eventComponent events root) root) : NeighborAway events root root := by
  classical
  have main : ∀ m : ℕ, ∀ (xs : List (Event n)) (r : Fin n), xs.length=m →
      (∀ e ∈ xs, e.1.val < e.2.val) → xs.Pairwise LaterOutside →
      xs.length+1=(eventComponent xs r).card → 3 ≤ (eventComponent xs r).card →
      IsExtreme (eventComponent xs r) r → NeighborAway xs r r := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro xs r hlen hl hs hm hc hx
      cases xs with
      | nil => simp only [List.length_nil] at hm; omega
      | cons e rest =>
        have hrhead := minimal_events_reachable (e::rest) r hm e (by simp)
        have hcarrier := event_component_reroot (e::rest) hrhead
        have hm' : (e::rest).length+1=(eventComponent (e::rest) e.1).card := by rwa [← hcarrier]
        have hc' : 3 ≤ (eventComponent (e::rest) e.1).card := by rwa [← hcarrier]
        have hx' : IsExtreme (eventComponent (e::rest) e.1) r := by rwa [← hcarrier]
        have hr' : r ∈ eventComponent (e::rest) e.1 :=
          (mem_eventComponent _ _ _).mpr (event_reaches_symm (e::rest) hrhead)
        have branches := head_branch_minimal e rest hm'
        have ih' : ∀ b ∈ [e.1,e.2], 3 ≤ (eventComponent rest b).card →
            IsExtreme (eventComponent rest b) b → NeighborAway (componentEvents rest b) b b := by
          intro b hb hcb hxb
          have hle : (componentEvents rest b).length ≤ rest.length := List.length_filter_le _ _
          have hlt : (componentEvents rest b).length < m := by simp only [List.length_cons] at hlen; omega
          have hlin : ∀ f ∈ componentEvents rest b, f.1.val < f.2.val := by
            intro f hf
            exact hl f (List.mem_cons_of_mem e (List.mem_filter.mp hf).1)
          have hsep' : (componentEvents rest b).Pairwise LaterOutside := (List.pairwise_cons.mp hs).2.filter _
          have hmin' : (componentEvents rest b).length+1=(eventComponent (componentEvents rest b) b).card := by
            rw [selected_component_eq]
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
            rcases hb with rfl | rfl
            · exact branches.1
            · exact branches.2
          exact ih (componentEvents rest b).length hlt (componentEvents rest b) b rfl
            hlin hsep' hmin' (by rwa [selected_component_eq]) (by rwa [selected_component_eq])
        have hres := event_neighbor_induction_step e rest hl hs hm' hc' ih' r hr' hx'
        simpa only [NeighborAway,← hcarrier] using hres
  exact main events.length events root rfl hlinear hsep hmin hcard hext
