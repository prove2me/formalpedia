-- Prove2me | solution 1 for LX.Core.FiniteCuts.nested_pair_endpoint_sum
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:48:28.243373+00:00
-- url     : https://prove2.me/submissions/3cc3376d-faa6-47bc-bb87-5dc31aa7d12d

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
import Definitions.Def_LX_NestedMatchingGeometry
import Theorems.Thm_LX_Core_FiniteCuts_nested_pair_exterior

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

/-- Counting the two exterior regions identifies the sum of a nested pair's endpoints. -/
theorem solution (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (hsep : NoSeparatedPairs p) (hfixed : ∀ i, p i ≠ i)
    (a b : Fin n) (hab : a.val < b.val) (hpab : p a=b) : a.val+b.val=n-1 := by
  have hcard : (Finset.Iio a).card=(Finset.Ioi b).card := by
    refine Finset.card_bij (fun x _ => p x) ?_ ?_ ?_
    · intro x hx
      have hlt : x<a := Finset.mem_Iio.mp hx
      apply Finset.mem_Ioi.mpr
      exact (nested_pair_exterior p hinv hnc hsep hfixed a b hab hpab x).1 hlt
    · intro x hx y hy heq
      exact p.injective heq
    · intro y hy
      refine ⟨p y,?_,hinv y⟩
      have hlt : b<y := Finset.mem_Ioi.mp hy
      apply Finset.mem_Iio.mpr
      exact (nested_pair_exterior p hinv hnc hsep hfixed a b hab hpab y).2 hlt
  rw [Fin.card_Iio,Fin.card_Ioi] at hcard
  have hb := b.isLt
  omega
