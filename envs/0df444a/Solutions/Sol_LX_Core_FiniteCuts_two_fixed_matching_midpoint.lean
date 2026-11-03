-- Prove2me | solution 1 for LX.Core.FiniteCuts.two_fixed_matching_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:56:51.941829+00:00
-- url     : https://prove2.me/submissions/89fcfe41-f09c-4392-857f-970a4e45da4f

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
import Theorems.Thm_LX_Core_FiniteCuts_no_adjacent_pair_straddles_fixed

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

/-- The two fixed vertices divide equal-sized arcs. -/
theorem solution (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (t : Fin n) (ht : 0<t.val)
    (hfixed : ∀ i, p i=i ↔ i=0 ∨ i=t)
    (hnoadj : ∀ i : Fin n, i.val+1 ≠ (p i).val) : 2*t.val=n := by
  have hp0 : p 0=0 := (hfixed 0).mpr (Or.inl rfl)
  have moved (x : Fin n) (hx0 : 0<x.val) (hxt : x.val ≠ t.val) : p x ≠ x := by
    intro h
    rcases (hfixed x).mp h with h | h
    · have := congrArg Fin.val h; change x.val=0 at this; omega
    · exact hxt (congrArg Fin.val h)
  have side (x : Fin n) (hx : p x ≠ x) :
      (x.val < t.val ∧ t.val < (p x).val) ∨ ((p x).val < t.val ∧ t.val < x.val) := by
    have hne : (p x).val ≠ x.val := fun h => hx (Fin.ext h)
    by_cases hlt : x.val < (p x).val
    · exact Or.inl (no_adjacent_pair_straddles_fixed p hinv hnc t hfixed hnoadj x (p x) hlt rfl)
    · exact Or.inr (no_adjacent_pair_straddles_fixed p hinv hnc t hfixed hnoadj (p x) x (by omega) (hinv x))
  have hcard : (Finset.Ioo (0 : Fin n) t).card=(Finset.Ioi t).card := by
    refine Finset.card_bij (fun x _ => p x) ?_ ?_ ?_
    · intro x hx
      have hh := Finset.mem_Ioo.mp hx
      have hx0 : 0<x.val := hh.1
      have hxt : x.val<t.val := hh.2
      have hs := side x (moved x hx0 (by omega))
      apply Finset.mem_Ioi.mpr
      change t.val < (p x).val
      omega
    · intro x hx y hy hxy
      exact p.injective hxy
    · intro y hy
      have hty : t<y := Finset.mem_Ioi.mp hy
      change t.val<y.val at hty
      have hs := side y (moved y (by omega) (by omega))
      have hpne : p y ≠ 0 := by
        intro h
        have hy0 := p.injective (h.trans hp0.symm)
        have hv := congrArg Fin.val hy0
        change y.val=0 at hv
        omega
      have hpv : (p y).val ≠ 0 := fun h => hpne (Fin.ext h)
      refine ⟨p y,Finset.mem_Ioo.mpr ⟨?_,?_⟩,hinv y⟩
      · change 0 < (p y).val; omega
      · change (p y).val < t.val; omega
  rw [Fin.card_Ioo,Fin.card_Ioi,Fin.val_zero] at hcard
  have := t.isLt
  omega
