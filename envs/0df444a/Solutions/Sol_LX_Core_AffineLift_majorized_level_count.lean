-- Prove2me | solution 1 for LX.Core.AffineLift.majorized_level_count
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:36:33.620048+00:00
-- url     : https://prove2.me/submissions/df5c0842-1ff2-4163-83c8-f9b2d0ed2c63

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
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_Graph

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
namespace List
end List

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

namespace LX.Core.AffineLift
end LX.Core.AffineLift
open LX
open LX.Core
open LX.Core.AffineLift
open scoped BigOperators
variable {n : ℕ}

/-- Majorization bounds the multiplicity of any level within the half-size range. -/
theorem solution {d : Fin n → ℤ} (hm : Majorized d) (h : ℤ)
    (hh : 2*h ≤ (n : ℤ)) :
    ((Finset.univ.filter (fun i => d i=h)).card : ℤ) ≤ (n : ℤ)-2*h := by
  classical
  let S := Finset.univ.filter (fun i => d i=h)
  have hb := hm S
  have hs : (∑ i ∈ S, d i)=(S.card : ℤ)*h := by
    calc
      _ = ∑ _i ∈ S, h := Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)
      _ = _ := by simp
  rw [hs] at hb
  change (S.card : ℤ) ≤ (n : ℤ)-2*h
  by_cases he : S.card=0
  · rw [he]; omega
  · have hp : (0 : ℤ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero he
    nlinarith
