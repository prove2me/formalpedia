-- Prove2me | solution 1 for LX.Core.FiniteCuts.nested_pair_exterior
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:47:03.167085+00:00
-- url     : https://prove2.me/submissions/d650f00a-70e7-49d2-ac24-d03d4b40e487

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

/-- In a fully nested matching, the outside prefix and suffix are paired with each other. -/
theorem solution (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (hsep : NoSeparatedPairs p) (hfixed : ∀ i, p i ≠ i)
    (a b : Fin n) (hab : a.val < b.val) (hpab : p a=b) (x : Fin n) :
    (x.val < a.val → b.val < (p x).val) ∧
      (b.val < x.val → (p x).val < a.val) := by
  have hpba : p b=a := by rw [← hpab]; exact hinv a
  have hfix : (p x).val ≠ x.val := fun h => hfixed x (Fin.ext h)
  constructor
  · intro hxa
    have hnea : (p x).val ≠ a.val := by
      intro h
      have he := p.injective ((Fin.ext h).trans hpba.symm)
      have := congrArg Fin.val he
      omega
    have hneb : (p x).val ≠ b.val := by
      intro h
      have he := p.injective ((Fin.ext h).trans hpab.symm)
      have := congrArg Fin.val he
      omega
    by_contra h
    have hpb : (p x).val < b.val := by omega
    by_cases hpa : (p x).val < a.val
    · by_cases hxp : x.val < (p x).val
      · exact hsep x (p x) a b hxp hpa hab rfl hpab
      · exact hsep (p x) x a b (by omega) hxa hab (hinv x) hpab
    · exact hnc x a (p x) b hxa (by omega) hpb rfl hpab
  · intro hbx
    have hnea : (p x).val ≠ a.val := by
      intro h
      have he := p.injective ((Fin.ext h).trans hpba.symm)
      have := congrArg Fin.val he
      omega
    have hneb : (p x).val ≠ b.val := by
      intro h
      have he := p.injective ((Fin.ext h).trans hpab.symm)
      have := congrArg Fin.val he
      omega
    by_contra h
    have hap : a.val < (p x).val := by omega
    by_cases hbp : b.val < (p x).val
    · by_cases hxp : x.val < (p x).val
      · exact hsep a b x (p x) hab hbx hxp hpab rfl
      · exact hsep a b (p x) x hab hbp (by omega) hpab (hinv x)
    · exact hnc a (p x) b x hap (by omega) hbx hpab (hinv x)
