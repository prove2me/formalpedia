-- Prove2me | solution 1 for LX.AnchoredPhases.odd_zero_reserve_exception_seven
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:35:39.360203+00:00
-- url     : https://prove2.me/submissions/43aa960c-ac16-4f76-ab2f-0790c87d292c

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric

namespace LX
end LX
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords

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

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem solution (p : State 7) (r u : Fin 7)
    (hp : ∀ i,(p*Equiv.swap u (u+1)) i=r-i)
    (hcase : (r.val=3 ∧ u.val=4) ∨ (r.val=4 ∧ u.val=1)) :
    ∃ w : List Letter,p*eval w=1 ∧ w.length ≤ 25 := by
  have he : p=(Equiv.subLeft r)*Equiv.swap u (u+1) := by
    have hq : p*Equiv.swap u (u+1)=Equiv.subLeft r := by
      apply Equiv.ext
      exact hp
    have hh := congrArg (fun q : State 7 => q*Equiv.swap u (u+1)) hq
    simpa [mul_assoc] using hh
  rcases hcase with h | h
  · have hr : r=3 := Fin.ext h.1
    have hu : u=4 := Fin.ext h.2
    rw [hr,hu] at he
    rw [he]
    refine ⟨[.x,.l,.l,.x,.l,.x,.l,.x,.l,.l,.x,.l,.x,.l,.l,.x,.l,.x,.l],?_,?_⟩ <;> decide +kernel
  · have hr : r=4 := Fin.ext h.1
    have hu : u=1 := Fin.ext h.2
    rw [hr,hu] at he
    rw [he]
    refine ⟨[.x,.l,.x,.l,.l,.x,.l,.x,.l,.l,.x,.l,.x,.l,.x,.l,.l,.x,.l],?_,?_⟩ <;> decide +kernel
