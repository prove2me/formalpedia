-- Prove2me | solution 1 for LX.Core.ZeroGap.component_inside_hull
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:30:30.553934+00:00
-- url     : https://prove2.me/submissions/69675589-64b2-4d05-8e59-e3d24cec8ac5

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
import Definitions.Def_LX_ZeroGapPair
import Theorems.Thm_LX_Core_ZeroGap_event_pair_order
import Theorems.Thm_LX_Core_ZeroGap_event_path_straddles
import Theorems.Thm_LX_Core_ZeroGap_inside_linear_iff

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
/-! Every nonzero balanced displacement vector has an oppositely signed pair
with no nonzero displacement in the open forward arc between its endpoints. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem distance_split (u v j : Fin n) (hj : distance u j ≤ distance u v) :
    distance j v=distance u v-distance u j := by
  have he : v-j=(v-u)-(j-u) := by ring
  unfold distance at *
  rw [he,Fin.sub_val_of_le (show j-u ≤ v-u from hj)]




end LX.Core.ZeroGap

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
/-! The ordered event condition gives a barrier: a different event component
cannot cross either endpoint of a chosen open event arc. -/
namespace LX.Core.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem distance_right_injective (a : Fin n) : Function.Injective (distance a) := by
  intro b c h
  exact sub_left_inj.mp (Fin.ext h)

theorem distance_pos (a b : Fin n) (h : b ≠ a) : 0 < distance a b := by
  by_contra hn
  have he : b-a=0 := Fin.ext (by change distance a b=0; omega)
  exact h (sub_eq_zero.mp he)

theorem distance_wrap (a b j : Fin n) (h : distance a b < distance a j) :
    distance j b=n+distance a b-distance a j := by
  have he : b-j=(b-a)-(j-a) := by ring
  unfold distance at *
  rw [he]
  exact Fin.coe_sub_iff_lt.mpr h

theorem crossing_visits_right (e f : Event n) (hfirst : Inside e f.1) (hlast : ¬Inside e f.2)
    (h0 : f.2 ≠ e.1) (h1 : f.2 ≠ e.2) : Inside f e.2 := by
  obtain ⟨hlo,hhi⟩ := hfirst
  have hc := distance_pos e.1 f.2 h0
  have hne : distance e.1 f.2 ≠ distance e.1 e.2 := fun h => h1 (distance_right_injective e.1 h)
  have hout : distance e.1 e.2 < distance e.1 f.2 := by unfold Inside at hlast; omega
  have hleft := distance_split e.1 e.2 f.1 (by omega)
  have hright := distance_split e.1 f.2 f.1 (by omega)
  exact ⟨by omega,by omega⟩

theorem crossing_visits_left (e f : Event n) (hlast : Inside e f.2) (hfirst : ¬Inside e f.1)
    (h0 : f.1 ≠ e.1) (h1 : f.1 ≠ e.2) : Inside f e.1 := by
  obtain ⟨hlo,hhi⟩ := hlast
  have hc := distance_pos e.1 f.1 h0
  have hne : distance e.1 f.1 ≠ distance e.1 e.2 := fun h => h1 (distance_right_injective e.1 h)
  have hout : distance e.1 e.2 < distance e.1 f.1 := by unfold Inside at hfirst; omega
  have hself : distance e.1 e.1=0 := by simp [distance]
  have hleft := distance_wrap e.1 e.1 f.1 (by rw [hself]; exact hc)
  rw [hself,Nat.add_zero] at hleft
  have hright := distance_wrap e.1 f.2 f.1 (by omega)
  have hn : distance e.1 f.1 < n := (f.1-e.1).isLt
  exact ⟨by omega,by omega⟩



theorem event_arc_side (events : List (Event n)) (hsep : events.Pairwise LaterOutside)
    {e f : Event n} (he : e ∈ events) (hf : f ∈ events)
    (h10 : f.1 ≠ e.1) (h11 : f.1 ≠ e.2) (h20 : f.2 ≠ e.1) (h21 : f.2 ≠ e.2) :
    Inside e f.1 ↔ Inside e f.2 := by
  rcases event_pair_order events hsep he hf with h | h | h
  · subst f
    exact False.elim (h10 rfl)
  · exact ⟨fun hi => False.elim (h.1 hi),fun hi => False.elim (h.2 hi)⟩
  · constructor
    · intro hi
      by_contra hn
      exact h.2 (crossing_visits_right e f hi hn h20 h21)
    · intro hi
      by_contra hn
      exact h.1 (crossing_visits_left e f hi hn h10 h11)

theorem edge_arc_side (events : List (Event n)) (hsep : events.Pairwise LaterOutside)
    (e : Event n) (he : e ∈ events) {i j : Fin n} (hij : EventEdge events i j)
    (hi0 : i ≠ e.1) (hi1 : i ≠ e.2) (hj0 : j ≠ e.1) (hj1 : j ≠ e.2) :
    Inside e i ↔ Inside e j := by
  obtain ⟨f,hf,h⟩ := hij
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact event_arc_side events hsep he hf hi0 hi1 hj0 hj1
  · exact (event_arc_side events hsep he hf hj0 hj1 hi0 hi1).symm

theorem component_inside_arc (events : List (Event n)) (hsep : events.Pairwise LaterOutside)
    (e : Event n) (he : e ∈ events) (root : Fin n) (hroot : Inside e root)
    (havoid : ¬EventReaches events root e.1 ∧ ¬EventReaches events root e.2)
    {j : Fin n} (hp : EventReaches events root j) : Inside e j := by
  induction hp with
  | refl => exact hroot
  | @tail i j hp hij ih =>
    have hi0 : i ≠ e.1 := fun h => havoid.1 (h ▸ hp)
    have hi1 : i ≠ e.2 := fun h => havoid.2 (h ▸ hp)
    have hj0 : j ≠ e.1 := fun h => havoid.1 (h ▸ hp.tail hij)
    have hj1 : j ≠ e.2 := fun h => havoid.2 (h ▸ hp.tail hij)
    exact (edge_arc_side events hsep e he hij hi0 hi1 hj0 hj1).mp ih



end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- If one component crosses a vertex of another, the latter component
lies strictly inside the hull of the former. -/
theorem solution (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (a b z : Fin n) (ha : a.val < b.val) (hz : b.val < z.val)
    (haz : EventReaches events a z) (havoid : ¬EventReaches events a b)
    (lo hi : ℕ) (hbound : ∀ i, EventReaches events a i → lo ≤ i.val ∧ i.val ≤ hi)
    (j : Fin n) (hbj : EventReaches events b j) : lo < j.val ∧ j.val < hi := by
  obtain ⟨e,he,hea,heb,heinside⟩ := event_path_straddles events hlinear a b z ha havoid haz hz
  have hn : ¬EventReaches events b e.1 ∧ ¬EventReaches events b e.2 := by
    constructor
    · intro h
      exact havoid (hea.trans (event_reaches_symm events h))
    · intro h
      exact havoid (heb.trans (event_reaches_symm events h))
  have hj := component_inside_arc events hsep e he b heinside hn hbj
  have hji := (inside_linear_iff e (hlinear e he) j).mp hj
  have hleft := hbound e.1 hea
  have hright := hbound e.2 heb
  omega
