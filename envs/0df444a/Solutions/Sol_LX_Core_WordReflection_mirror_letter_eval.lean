-- Prove2me | solution 1 for LX.Core.WordReflection.mirror_letter_eval
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:41:36.541336+00:00
-- url     : https://prove2.me/submissions/fed8cd33-01e6-44e9-b7ef-3d57b2684987

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
import Definitions.Def_LX_WordReflection

namespace LX.Core
end LX.Core
namespace LX.Core.WordReflection
end LX.Core.WordReflection

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
/-! Reflection in the edge between positions zero and one. It exchanges L/R,
fixes X, and agrees with the word symmetry already used by the lower proof. -/
namespace LX.Core.WordReflection
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



@[simp] theorem reflection_apply (i : Fin n) : reflection i=1-i := rfl

@[simp] theorem reflection_twice (i : Fin n) : reflection (reflection i)=i := by
  simp only [reflection_apply]
  abel

@[simp] theorem reflection_square : (reflection : State n)*reflection=1 := by
  apply Equiv.ext
  intro i
  exact reflection_twice i



end LX.Core.WordReflection

end

namespace LX.Core.WordReflection
end LX.Core.WordReflection
open LX
open LX.Core
open LX.Core.WordReflection
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution (a : Letter) :
    a.inverse.eval (n := n)=reflection*a.eval*reflection := by
  apply Equiv.ext
  intro i
  cases a with
  | l =>
    simp [Letter.inverse, Letter.eval, L, R, Equiv.Perm.mul_apply, reflection,
      finRotate_apply, finRotate_symm_apply]
  | r =>
    simp [Letter.inverse, Letter.eval, L, R, Equiv.Perm.mul_apply, reflection,
      finRotate_apply, finRotate_symm_apply]
    abel
  | x =>
    change Equiv.swap 0 1 i=reflection (Equiv.swap 0 1 (reflection i))
    have h := Function.Injective.map_swap (reflection (n := n)).injective
      (0 : Fin n) 1 (reflection i)
    change reflection (Equiv.swap 0 1 (reflection i))=
      Equiv.swap (reflection (0 : Fin n)) (reflection 1) (reflection (reflection i)) at h
    rw [reflection_twice] at h
    have hz : reflection (0 : Fin n)=1 := by simp
    have ho : reflection (1 : Fin n)=0 := by simp
    rw [hz, ho, Equiv.swap_comm 1 0] at h
    exact h.symm
