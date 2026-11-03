-- Prove2me | solution 1 for LX.Core.FiniteCuts.noncrossing_pair_interior
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:45:31.730969+00:00
-- url     : https://prove2.me/submissions/2a55be11-0419-4e52-a4fc-186e6e2879d8

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
import Definitions.Def_LX_LinearMatchingGeometry

namespace LX.Core
end LX.Core
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts

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

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
variable {n : ℕ}

/-- A pair's interior is closed: an escaping partner would alternate with the pair. -/
theorem solution (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (a b x : Fin n)
    (hax : a.val < x.val) (hxb : x.val < b.val) (hab : p a=b) :
    a.val < (p x).val ∧ (p x).val < b.val := by
  have hpa : p b=a := by rw [← hab]; exact hinv a
  have hnea : p x ≠ a := by
    intro he
    have h := hinv x
    rw [he,hab] at h
    have := congrArg Fin.val h
    omega
  have hneb : p x ≠ b := by
    intro he
    have h := p.injective (he.trans hab.symm)
    have := congrArg Fin.val h
    omega
  have hneav : (p x).val ≠ a.val := fun h => hnea (Fin.ext h)
  have hnebv : (p x).val ≠ b.val := fun h => hneb (Fin.ext h)
  constructor
  · by_contra h
    have hlt : (p x).val < a.val := by omega
    exact hnc (p x) a x b hlt hax hxb (hinv x) hab
  · by_contra h
    have hlt : b.val < (p x).val := by omega
    exact hnc a x b (p x) hax hxb hlt hab rfl
