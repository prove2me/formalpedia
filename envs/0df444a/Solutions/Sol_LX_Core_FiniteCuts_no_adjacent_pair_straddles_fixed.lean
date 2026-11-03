-- Prove2me | solution 1 for LX.Core.FiniteCuts.no_adjacent_pair_straddles_fixed
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:49:57.310444+00:00
-- url     : https://prove2.me/submissions/c4328f8f-0add-49b9-a580-36fd9de99ccf

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
import Theorems.Thm_LX_Core_FiniteCuts_noncrossing_pair_contains_adjacent

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

/-- Without adjacent pairs, every pair must surround the second fixed point. -/
theorem solution (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (t : Fin n)
    (hfixed : ∀ i, p i=i ↔ i=0 ∨ i=t)
    (hnoadj : ∀ i : Fin n, i.val+1 ≠ (p i).val)
    (a b : Fin n) (hab : a.val < b.val) (hpab : p a=b) :
    a.val < t.val ∧ t.val < b.val := by
  have hane : p a ≠ a := by rw [hpab]; intro h; have := congrArg Fin.val h; omega
  have hbne : p b ≠ b := by
    have hba : p b=a := by rw [← hpab]; exact hinv a
    rw [hba]; intro h; have := congrArg Fin.val h; omega
  have ha0 : a ≠ 0 := fun h => hane ((hfixed a).mpr (Or.inl h))
  have hat : a ≠ t := fun h => hane ((hfixed a).mpr (Or.inr h))
  have hbt : b ≠ t := fun h => hbne ((hfixed b).mpr (Or.inr h))
  have ha0v : a.val ≠ 0 := fun h => ha0 (Fin.ext h)
  have hatv : a.val ≠ t.val := fun h => hat (Fin.ext h)
  have hbtv : b.val ≠ t.val := fun h => hbt (Fin.ext h)
  by_contra h
  have hnofix : ∀ i : Fin n, a.val ≤ i.val → i.val ≤ b.val → p i ≠ i := by
    intro i hai hib hpi
    rcases (hfixed i).mp hpi with hi | hi
    · have hv := congrArg Fin.val hi
      change i.val=0 at hv
      omega
    · have hv := congrArg Fin.val hi
      omega
  obtain ⟨x,y,hx,hy,hxy,hp⟩ := noncrossing_pair_contains_adjacent p hinv hnc a b hab hpab hnofix
  exact hnoadj x (by rw [hp]; exact hxy)
