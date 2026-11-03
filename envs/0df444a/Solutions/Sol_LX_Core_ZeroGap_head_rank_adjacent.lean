-- Prove2me | solution 1 for LX.Core.ZeroGap.head_rank_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:27:51.294743+00:00
-- url     : https://prove2.me/submissions/e0344cf9-9967-479a-8a5e-a2615b006863

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
import Definitions.Def_LX_ShallowNeighborSplice
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Definitions.Def_LX_ZeroGapPair
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
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]













@[simp] theorem mem_endpoints (events : List (Event n)) (i : Fin n) :
    i ∈ endpoints events ↔ ∃ e ∈ events, i=e.1 ∨ i=e.2 := by
  simp [endpoints]






end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ}

theorem solution [NeZero n] (e : Event n) (events : List (Event n))
    (he : e.1.val < e.2.val) (hsep : (e::events).Pairwise LaterOutside) :
    RankAdjacent (eventComponent (e::events) e.1) e.1 e.2 := by
  have hfirst : e.1 ∈ eventComponent (e::events) e.1 :=
    (mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl
  have hsecond : e.2 ∈ eventComponent (e::events) e.1 :=
    (mem_eventComponent _ _ _).mpr (Relation.ReflTransGen.single ⟨e,by simp,Or.inl ⟨rfl,rfl⟩⟩)
  refine ⟨hfirst,hsecond,fun h => (by have := congrArg Fin.val h; omega),?_⟩
  intro z hz hz'
  have hins : Inside e z := (inside_linear_iff e he z).mpr (by
    simpa only [min_eq_left (le_of_lt he),max_eq_right (le_of_lt he)] using hz')
  have hnot : z ∉ endpoints (e::events) := by
    intro hm
    obtain ⟨f,hf,hzf⟩ := (mem_endpoints _ _).mp hm
    rcases List.mem_cons.mp hf with hf | hf
    · subst f
      rcases hzf with hzf | hzf
      · subst z; have h := hins.1; simp [distance] at h
      · subst z; exact lt_irrefl _ hins.2
    · have h := (List.pairwise_cons.mp hsep).1 f hf
      rcases hzf with hzf | hzf
      · exact h.1 (hzf ▸ hins)
      · exact h.2 (hzf ▸ hins)
  have hp := (mem_eventComponent (e::events) e.1 z).mp hz
  have hr : z=e.1 ∨ z ∈ endpoints (e::events) := by
    induction hp with
    | refl => exact Or.inl rfl
    | @tail u v hp hv ih =>
      right
      obtain ⟨f,hf,hor⟩ := hv
      apply (mem_endpoints _ _).mpr
      exact ⟨f,hf,hor.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)⟩
  rcases hr with hr | hr
  · subst z
    have h := hins.1
    simp [distance] at h
  · exact hnot hr
