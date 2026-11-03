-- Prove2me | solution 1 for LX.Core.ZeroGap.root_cover_equality_component_minimal
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:29:59.102923+00:00
-- url     : https://prove2.me/submissions/ba9edeb9-cb81-4185-9f20-7dc21832f12f

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
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph
import Theorems.Thm_LX_Core_ZeroGap_component_selected_size
import Theorems.Thm_LX_Core_ZeroGap_component_spanning_event_sublist
import Theorems.Thm_LX_Core_ZeroGap_root_cover_count
import Theorems.Thm_LX_Core_ZeroGap_spanning_replacement_reaches

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
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





theorem component_events_length (events : List (Event n)) (root : Fin n) :
    (componentEvents events root).length+(outsideEvents events root).length=events.length := by
  classical
  simp only [componentEvents,outsideEvents,decide_not]
  have hsplit : ∀ (xs : List (Event n)) (f : Event n → Bool),
      (xs.filter f).length+(xs.filter (fun e => !f e)).length=xs.length := by
    intro xs f
    induction xs with
    | nil => rfl
    | cons e rest ih => cases hf : f e <;> simp [hf] <;> omega
  exact hsplit events _







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
variable {n : ℕ} [NeZero n]

/-- Equality in the root-cover count forces every actual selected event
component to have exactly the number of edges of a tree. -/
theorem solution (events : List (Event n))
    (roots : List (Fin n)) (hcover : ∀ i : Fin n, ∃ r ∈ roots, EventReaches events r i)
    (heq : events.length+roots.length=n) (root : Fin n) :
    (componentEvents events root).length+1=(eventComponent events root).card := by
  obtain ⟨part,_,hcomp,hlen,_,_⟩ := component_spanning_event_sublist events root
  have hcover' : ∀ i : Fin n, ∃ r ∈ roots,
      EventReaches (part++outsideEvents events root) r i := by
    intro i
    obtain ⟨r,hr,hi⟩ := hcover i
    exact ⟨r,hr,spanning_replacement_reaches events part root hcomp hi⟩
  have hbound := root_cover_count (part++outsideEvents events root) roots hcover'
  rw [List.length_append] at hbound
  have hsplit := component_events_length events root
  have hsize := component_selected_size events root
  omega
