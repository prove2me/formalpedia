-- Prove2me | solution 1 for LX.Core.FiniteCuts.two_fixed_matching_reflection
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:58:49.798686+00:00
-- url     : https://prove2.me/submissions/47792f2e-92ee-4c7f-b130-b364838b2add

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
import Theorems.Thm_LX_Core_FiniteCuts_two_fixed_matching_midpoint
import Theorems.Thm_LX_Core_FiniteCuts_two_fixed_pair_endpoint_sum

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
variable {n : ℕ} [NeZero n]

/-- The even equality matching, cut at a fixed point, is circular reflection. -/
theorem solution (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (t : Fin n) (ht : 0<t.val)
    (hfixed : ∀ i, p i=i ↔ i=0 ∨ i=t)
    (hnoadj : ∀ i : Fin n, i.val+1 ≠ (p i).val) :
    ∀ i : Fin n, i ≠ 0 → i.val+(p i).val=n := by
  have hmid := two_fixed_matching_midpoint p hinv hnc t ht hfixed hnoadj
  intro i hi
  by_cases hit : i=t
  · subst i
    rw [(hfixed t).mpr (Or.inr rfl)]
    omega
  · have hm : p i ≠ i := by
      intro h
      rcases (hfixed i).mp h with h | h
      · exact hi h
      · exact hit h
    have hne : (p i).val ≠ i.val := fun h => hm (Fin.ext h)
    by_cases hlt : i.val < (p i).val
    · exact two_fixed_pair_endpoint_sum p hinv hnc t hfixed hnoadj i (p i) hlt rfl
    · have h := two_fixed_pair_endpoint_sum p hinv hnc t hfixed hnoadj (p i) i (by omega) (hinv i)
      omega
