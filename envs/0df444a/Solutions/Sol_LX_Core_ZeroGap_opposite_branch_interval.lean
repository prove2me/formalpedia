-- Prove2me | solution 1 for LX.Core.ZeroGap.opposite_branch_interval
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:33:34.312884+00:00
-- url     : https://prove2.me/submissions/49289abb-c8fe-4f6c-a20a-7cb8bef440e0

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
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Theorems.Thm_LX_Core_ZeroGap_adjacent_attachment_boundary
import Theorems.Thm_LX_Core_ZeroGap_component_inside_hull

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
/-! Separation of components in a finite, linearly oriented event forest.
The linear-orientation hypothesis is explicit; a circular trace needs an
appropriate zero-load cut before these statements can be applied. -/
namespace LX.Core.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]







/-- A different component with a vertex outside a component hull cannot
have a vertex strictly inside that hull. -/
theorem component_cannot_enter_hull (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (lo hi root : Fin n) (hlohi : EventReaches events lo hi)
    (hbound : ∀ i, EventReaches events lo i → lo.val ≤ i.val ∧ i.val ≤ hi.val)
    (havoid : ¬EventReaches events lo root)
    (hout : root.val < lo.val ∨ hi.val < root.val)
    (j : Fin n) (hrj : EventReaches events root j) :
    ¬(lo.val < j.val ∧ j.val < hi.val) := by
  intro hj
  have hnot : ¬EventReaches events lo j := by
    intro h
    exact havoid (h.trans (event_reaches_symm events hrj))
  have h := component_inside_hull events hlinear hsep lo j hi hj.1 hj.2
    hlohi hnot lo.val hi.val hbound root (event_reaches_symm events hrj)
  omega







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
variable {n : ℕ}









theorem component_interval_of_two_cover [NeZero n] (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (lo hi root : Fin n) (hlohi : EventReaches events lo hi)
    (hbound : ∀ i, EventReaches events lo i → lo.val ≤ i.val ∧ i.val ≤ hi.val)
    (havoid : ¬EventReaches events lo root)
    (hout : root.val < lo.val ∨ hi.val < root.val)
    (S : Finset (Fin n)) (hsub : eventComponent events lo ⊆ S)
    (hcover : ∀ i ∈ S, EventReaches events lo i ∨ EventReaches events root i) :
    CarrierInterval (eventComponent events lo) S := by
  refine ⟨hsub,?_⟩
  intro x hx y hy z hz hzx hzy
  have hxb := hbound x ((mem_eventComponent events lo x).mp hx)
  have hyb := hbound y ((mem_eventComponent events lo y).mp hy)
  rcases hcover z hz with h | h
  · exact (mem_eventComponent events lo z).mpr h
  · have hnot := component_cannot_enter_hull events hlinear hsep lo hi root
      hlohi hbound havoid hout z h
    exact False.elim (hnot (by omega))









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











end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- The branch opposite an excluded extreme is an interval, and its
attachment vertex is an extreme of that branch. All geometric conditions
needed for the smaller induction are derived here. -/
theorem solution (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (S : Finset (Fin n)) (a b r : Fin n)
    (hab : ¬EventReaches events a b) (har : EventReaches events a r)
    (hsub : eventComponent events b ⊆ S)
    (hcover : ∀ i ∈ S, EventReaches events a i ∨ EventReaches events b i)
    (hext : IsExtreme S r) (hgap : RankAdjacent S a b) :
    CarrierInterval (eventComponent events b) S ∧ IsExtreme (eventComponent events b) b := by
  classical
  let T := eventComponent events b
  have hne : T.Nonempty := ⟨b,(mem_eventComponent events b b).mpr Relation.ReflTransGen.refl⟩
  let lo := T.min' hne
  let hi := T.max' hne
  have hlo : lo ∈ T := Finset.min'_mem T hne
  have hhi : hi ∈ T := Finset.max'_mem T hne
  have hb_lo := (mem_eventComponent events b lo).mp hlo
  have hb_hi := (mem_eventComponent events b hi).mp hhi
  have heq : T=eventComponent events lo := event_component_reroot events hb_lo
  have hbound (i : Fin n) (hip : EventReaches events lo i) : lo.val ≤ i.val ∧ i.val ≤ hi.val := by
    have him : i ∈ T := (mem_eventComponent events b i).mpr (hb_lo.trans hip)
    exact ⟨Finset.min'_le T i him,Finset.le_max' T i him⟩
  have hnot : ¬EventReaches events lo r := by
    intro h
    exact hab ((har.trans (event_reaches_symm events h)).trans (event_reaches_symm events hb_lo))
  have hrlo : r ≠ lo := by intro h; subst r; exact hnot Relation.ReflTransGen.refl
  have hrhi : r ≠ hi := by intro h; subst r; exact hnot ((event_reaches_symm events hb_lo).trans hb_hi)
  have hout : r.val < lo.val ∨ hi.val < r.val := by
    have hnlo : r.val ≠ lo.val := fun h => hrlo (Fin.ext h)
    have hnhi : r.val ≠ hi.val := fun h => hrhi (Fin.ext h)
    rcases hext with h | h
    · have := h lo (hsub hlo); left; omega
    · have := h hi (hsub hhi); right; omega
  have hlh : EventReaches events lo hi := (event_reaches_symm events hb_lo).trans hb_hi
  have hc : ∀ i ∈ S, EventReaches events lo i ∨ EventReaches events r i := by
    intro i him
    rcases hcover i him with h | h
    · exact Or.inr ((event_reaches_symm events har).trans h)
    · exact Or.inl ((event_reaches_symm events hb_lo).trans h)
  have hinterval := component_interval_of_two_cover events hlinear hsep lo hi r hlh hbound hnot hout S
    (by rw [← heq]; exact hsub) hc
  have hboundary := adjacent_attachment_boundary events hlinear hsep lo hi r a b hlh hbound hnot hout
    (event_reaches_symm events har) (event_reaches_symm events hb_lo)
    (fun i hip => hgap.2.2.2 i (hsub ((mem_eventComponent events b i).mpr (hb_lo.trans hip))))
  refine ⟨?_,?_⟩
  · simpa only [← heq] using hinterval
  · rcases hboundary with hb | hb
    · left
      intro i him
      rw [hb]
      exact (hbound i ((event_reaches_symm events hb_lo).trans ((mem_eventComponent events b i).mp him))).1
    · right
      intro i him
      rw [hb]
      exact (hbound i ((event_reaches_symm events hb_lo).trans ((mem_eventComponent events b i).mp him))).2
