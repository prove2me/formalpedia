-- Prove2me | solution 1 for LX.Core.FiniteCuts.noncrossing_pair_contains_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:47:55.093012+00:00
-- url     : https://prove2.me/submissions/fe28e08a-97f5-4564-b29f-013548db3faf

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
import Theorems.Thm_LX_Core_FiniteCuts_noncrossing_pair_interior

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

/-- Every fixed-point-free pair interval contains a pair of consecutive positions. -/
theorem solution (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (a b : Fin n) (hablt : a.val < b.val) (hab : p a=b)
    (hfixed : ∀ i : Fin n, a.val ≤ i.val → i.val ≤ b.val → p i ≠ i) :
    ∃ x y : Fin n, a.val ≤ x.val ∧ y.val ≤ b.val ∧ x.val+1=y.val ∧ p x=y := by
  by_cases hunit : a.val+1=b.val
  · exact ⟨a,b,le_rfl,le_rfl,hunit,hab⟩
  · let x : Fin n := ⟨a.val+1,by have := b.isLt; omega⟩
    have hax : a.val < x.val := by dsimp [x]; omega
    have hxb : x.val < b.val := by dsimp [x]; omega
    have hx := noncrossing_pair_interior p hinv hnc a b x hax hxb hab
    have hne := hfixed x (by omega) (by omega)
    have hnev : (p x).val ≠ x.val := fun h => hne (Fin.ext h)
    by_cases hp : x.val < (p x).val
    · obtain ⟨u,v,hu,hv,huv,hp⟩ := solution p hinv hnc x (p x) hp rfl
        (fun i hi hj => hfixed i (by omega) (by omega))
      exact ⟨u,v,by omega,by omega,huv,hp⟩
    · have hpx : (p x).val < x.val := by omega
      obtain ⟨u,v,hu,hv,huv,hp⟩ := solution p hinv hnc (p x) x hpx (hinv x)
        (fun i hi hj => hfixed i (by omega) (by omega))
      exact ⟨u,v,by omega,by omega,huv,hp⟩
termination_by b.val-a.val
decreasing_by all_goals dsimp [x] at *; omega
