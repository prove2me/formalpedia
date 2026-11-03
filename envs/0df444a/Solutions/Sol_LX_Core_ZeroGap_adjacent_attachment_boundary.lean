-- Prove2me | solution 1 for LX.Core.ZeroGap.adjacent_attachment_boundary
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:32:08.961823+00:00
-- url     : https://prove2.me/submissions/b8024a79-ad59-4d9f-9ae8-e2b5af2baf33

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
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
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

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- When an edge joins consecutive support vertices, its endpoint in an
interval component must be an extreme vertex of that component. -/
theorem solution (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (lo hi root a b : Fin n) (hlohi : EventReaches events lo hi)
    (hbound : ∀ i, EventReaches events lo i → lo.val ≤ i.val ∧ i.val ≤ hi.val)
    (havoid : ¬EventReaches events lo root)
    (hout : root.val < lo.val ∨ hi.val < root.val)
    (hra : EventReaches events root a) (hlob : EventReaches events lo b)
    (hgap : ∀ i, EventReaches events lo i →
      ¬(min a.val b.val < i.val ∧ i.val < max a.val b.val)) : b=lo ∨ b=hi := by
  have hna := component_cannot_enter_hull events hlinear hsep lo hi root hlohi hbound havoid hout a hra
  have ha0 : a ≠ lo := by
    intro he
    subst a
    exact havoid (event_reaches_symm events hra)
  have ha1 : a ≠ hi := by
    intro he
    subst a
    exact havoid (hlohi.trans (event_reaches_symm events hra))
  have hv0 : a.val ≠ lo.val := fun h => ha0 (Fin.ext h)
  have hv1 : a.val ≠ hi.val := fun h => ha1 (Fin.ext h)
  have hb := hbound b hlob
  have hg0 := hgap lo Relation.ReflTransGen.refl
  have hg1 := hgap hi hlohi
  by_cases hleft : a.val < lo.val
  · left
    apply Fin.ext
    omega
  · right
    apply Fin.ext
    omega
