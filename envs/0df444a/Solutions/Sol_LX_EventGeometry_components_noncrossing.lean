-- Prove2me | solution 1 for LX.EventGeometry.components_noncrossing
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:32:26.483047+00:00
-- url     : https://prove2.me/submissions/063ec1ad-f741-4037-9564-f80ff343e1e6

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
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Theorems.Thm_LX_Core_ZeroGap_component_inside_hull

namespace Int
end Int
namespace LX
end LX
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.CycleGeometry
end LX.CycleGeometry
namespace LX.EventGeometry
end LX.EventGeometry
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
/-! Extend a finite permutation to a contiguous window of a larger ambient
permutation, fixing every external label. No ambient size is changed. -/
namespace LX.Core.FiniteWindow
variable {n b : ℕ}



















@[simp] theorem permutation_embed (W : Window n b) (p : State b) (i : Fin b) :
    permutation W p (embed W i)=embed W (p i) := p.extendDomain_apply_image (windowEquiv W) i



@[simp] theorem permutation_symm (W : Window n b) (p : State b) :
    (permutation W p).symm=permutation W p.symm := rfl







end LX.Core.FiniteWindow

end

section
namespace LX.Core



@[simp] theorem Letter.eval_inverse {n : ℕ} [NeZero n] (c : Letter) :
    c.inverse.eval (n := n) = (c.eval)⁻¹ := by
  cases c <;> simp [inverse, Letter.eval, L, R, X]








end LX.Core

end

section
/-! Directed LX words. No inverse generator is included in the alphabet.
The target bound is a proposition, not an axiom or an assumed estimate. -/
namespace LX









@[simp] theorem eval_nil {n : ℕ} [NeZero n] : eval (n := n) [] = 1 := rfl

@[simp] theorem eval_append {n : ℕ} [NeZero n] (u v : List Letter) :
    eval (n := n) (u ++ v) = eval u * eval v := by
  simp [eval]





























end LX

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

namespace LX.EventGeometry
end LX.EventGeometry
open LX
open LX.EventGeometry
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- Two different components of a separated linear event graph cannot
alternate. The component statement itself does not require minimality. -/
theorem solution (events : List (Event n))
    (hlinear : ∀ e ∈ events,e.1.val < e.2.val)
    (hsep : events.Pairwise LaterOutside)
    (a b c d : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val)
    (hac : EventReaches events a c) (hbd : EventReaches events b d) :
    EventReaches events a b := by
  classical
  by_contra hnot
  let A := eventComponent events a
  let B := eventComponent events b
  have hA : A.Nonempty := ⟨a,(mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl⟩
  have hB : B.Nonempty := ⟨b,(mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl⟩
  let amin := A.min' hA
  let amax := A.max' hA
  let bmin := B.min' hB
  let bmax := B.max' hB
  have boundA (i : Fin n) (hi : EventReaches events a i) : amin.val ≤ i.val ∧ i.val ≤ amax.val :=
    ⟨Finset.min'_le A i ((mem_eventComponent _ _ _).mpr hi),
     Finset.le_max' A i ((mem_eventComponent _ _ _).mpr hi)⟩
  have boundB (i : Fin n) (hi : EventReaches events b i) : bmin.val ≤ i.val ∧ i.val ≤ bmax.val :=
    ⟨Finset.min'_le B i ((mem_eventComponent _ _ _).mpr hi),
     Finset.le_max' B i ((mem_eventComponent _ _ _).mpr hi)⟩
  have hbmax : EventReaches events b bmax :=
    (mem_eventComponent _ _ _).mp (Finset.max'_mem B hB)
  have hamax : EventReaches events a amax :=
    (mem_eventComponent _ _ _).mp (Finset.max'_mem A hA)
  have hbnd := component_inside_hull events hlinear hsep a b c hab hbc hac hnot
    amin.val amax.val boundA bmax hbmax
  have havoid : ¬EventReaches events b c := by
    intro h
    exact hnot (hac.trans (event_reaches_symm events h))
  have hcmax : EventReaches events c amax := (event_reaches_symm events hac).trans hamax
  have habnd := component_inside_hull events hlinear hsep b c d hbc hcd hbd havoid
    bmin.val bmax.val boundB amax hcmax
  omega
