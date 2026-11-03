-- Prove2me | solution 1 for LX.Core.LiftedModel.mem_events
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:31:00.209203+00:00
-- url     : https://prove2.me/submissions/224c9f7b-ad46-435c-a237-9432d1212ca8

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
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PhysicalModel

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
/-! Exact event traces and detection of repeated lifted pairs in a literal word. -/
namespace LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]



theorem events_append (u v : List Letter) (s : Configuration n) :
    events (u++v) s=events u s ++ events v (run u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons a u ih => cases a <;> simp only [List.cons_append, events, run, ih, List.cons_append]









end LX.Core.LiftedModel

end

namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
open LX
open LX.Core
open LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]

theorem solution (w : List Letter) (s : Configuration n) (key : PairKey n) :
    key ∈ events w s ↔ ∃ u v, w=u++[.x]++v ∧ eventKey (run u s)=key := by
  constructor
  · induction w generalizing s with
    | nil => simp [events]
    | cons a w ih =>
      have liftTail (h : key ∈ events w (step a s)) :
          ∃ u v, a::w=u++[.x]++v ∧ eventKey (run u s)=key := by
        obtain ⟨u, v, he, hk⟩ := ih _ h
        exact ⟨a::u, v, by simp only [List.cons_append, he], hk⟩
      cases a with
      | l => exact liftTail
      | r => exact liftTail
      | x =>
        intro h
        rcases List.mem_cons.mp h with h | h
        · exact ⟨[], w, rfl, h.symm⟩
        · exact liftTail h
  · rintro ⟨u, v, rfl, hk⟩
    simp [events_append, events, hk]
