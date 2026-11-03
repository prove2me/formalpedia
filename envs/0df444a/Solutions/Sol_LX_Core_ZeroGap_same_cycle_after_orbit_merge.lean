-- Prove2me | solution 1 for LX.Core.ZeroGap.same_cycle_after_orbit_merge
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:31:39.192309+00:00
-- url     : https://prove2.me/submissions/f92b6086-a522-4b52-93b0-5575bc4d3fd5

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
import Theorems.Thm_LX_Core_ZeroGap_swap_distinct_orbits_same_cycle

namespace LX.Core
end LX.Core
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap

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

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ}

/-- Joining different orbits preserves every previous cyclic connection. -/
theorem solution (p : State n) (a b : Fin n)
    (hnot : ¬p.SameCycle a b) {i j : Fin n} (hij : p.SameCycle i j) :
    (Equiv.swap a b*p).SameCycle i j := by
  let q := Equiv.swap a b*p
  have hab : q.SameCycle a b := swap_distinct_orbits_same_cycle p a b hnot
  have hstep (x : Fin n) : q.SameCycle x (p x) := by
    have hx : q.SameCycle x (q x) := (Equiv.Perm.SameCycle.refl q x).apply_right
    by_cases ha : p x=a
    · have he : q x=b := by simp [q,Equiv.Perm.mul_apply,ha]
      rw [he] at hx
      rw [ha]
      exact hx.trans hab.symm
    · by_cases hb : p x=b
      · have he : q x=a := by simp [q,Equiv.Perm.mul_apply,hb]
        rw [he] at hx
        rw [hb]
        exact hx.trans hab
      · have he : q x=p x := by simp [q,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne ha hb]
        rwa [he] at hx
  obtain ⟨k,rfl⟩ := hij.exists_nat_pow_eq
  clear hij
  induction k with
  | zero => exact Equiv.Perm.SameCycle.refl q i
  | succ k ih =>
    rw [pow_succ',Equiv.Perm.mul_apply]
    exact ih.trans (hstep ((p^k) i))
