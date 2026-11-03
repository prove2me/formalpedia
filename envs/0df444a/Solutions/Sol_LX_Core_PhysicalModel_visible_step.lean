-- Prove2me | solution 1 for LX.Core.PhysicalModel.visible_step
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:32:20.318213+00:00
-- url     : https://prove2.me/submissions/64458951-44cc-406f-9876-eb72bbb34487

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
import Definitions.Def_LX_PhysicalModel

namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel

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
/-! A zero-displacement phase lift is an actual rotation. Its final rotation
is explicitly paid by an LX.Core word of length at most n-1. -/
namespace LX.Core.AffineLift
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem rotation_power_apply (k : ℕ) (i : Fin n) : (L n ^ k) i = i + (k : Fin n) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih]
    simp [L, finRotate_apply, Nat.cast_add, add_comm, add_left_comm]


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



theorem visible_apply (s : Configuration n) (i : Fin n) :
    visible s i = s.tokens (i + s.cursor) := by
  simp only [visible, Equiv.Perm.mul_apply, rotation_power_apply, Fin.cast_val_eq_self]














end LX.Core.PhysicalModel

end

namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
open LX
open LX.Core
open LX.Core.PhysicalModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open AffineLift
variable {n : ℕ} [NeZero n]

theorem solution (a : Letter) (s : Configuration n) :
    visible (step a s) = visible s * a.eval (n := n) := by
  apply Equiv.ext
  intro i
  cases a with
  | l =>
    simp only [step, visible_apply, Letter.eval, Equiv.Perm.mul_apply, L, finRotate_apply]
    congr 1
    abel
  | r =>
    simp only [step, visible_apply, Letter.eval, Equiv.Perm.mul_apply, R, L]
    change s.tokens (i + (s.cursor - 1)) = s.tokens ((finRotate n).symm i + s.cursor)
    rw [finRotate_symm_apply]
    congr 1
    abel
  | x =>
    simp only [step, visible_apply, Letter.eval, Equiv.Perm.mul_apply, X]
    congr 1
    have h := Function.Injective.map_swap (f := fun j : Fin n => j + s.cursor)
      (add_left_injective s.cursor) (0 : Fin n) 1 i
    simpa only [zero_add, add_zero, add_comm] using h.symm
