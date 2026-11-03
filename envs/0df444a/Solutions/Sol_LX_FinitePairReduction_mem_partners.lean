-- Prove2me | solution 1 for LX.FinitePairReduction.mem_partners
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:43:24.202852+00:00
-- url     : https://prove2.me/submissions/da85855b-b7ab-48c9-9048-5cc5a306e5fc

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
import Definitions.Def_LX_FinitePairReduction
import Definitions.Def_LX_Graph
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.FinitePairReduction
end LX.FinitePairReduction
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

section
namespace LX.Core



@[simp] theorem Letter.eval_inverse {n : ℕ} [NeZero n] (c : Letter) :
    c.inverse.eval (n := n) = (c.eval)⁻¹ := by
  cases c <;> simp [inverse, Letter.eval, L, R, X]








end LX.Core

end

section
/-! Directed LX words. No inverse generator is included in the alphabet.
The target bound is a proposition, not an axiom or an assumed estimate. -/
namespace LX









@[simp] theorem eval_nil {n : ℕ} [NeZero n] : eval (n := n) [] = 1 := rfl

@[simp] theorem eval_append {n : ℕ} [NeZero n] (u v : List Letter) :
    eval (n := n) (u ++ v) = eval u * eval v := by
  simp [eval]





























end LX

end

section
namespace LX.FinitePairReduction
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]









theorem eval_cons_action (a : Letter) (w : List Letter) :
    eval (n := n) (a::w)=a.toCore.eval*eval w :=
  LX.Core.eval_cons a.toCore (w.map Letter.toCore)

theorem mem_head_partners (i j : Fin n) (p : State n) :
    j ∈ headPartners i p ↔ HeadPair p i j := by
  unfold headPartners HeadPair
  by_cases h0 : p 0=i <;> by_cases h1 : p 1=i <;> simp [h0,h1,eq_comm]





















end LX.FinitePairReduction

end

namespace LX.FinitePairReduction
end LX.FinitePairReduction
open LX
open LX.FinitePairReduction
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution (i j : Fin n) (w : List Letter) (p : State n)
    (hj : j ∈ partners i w p) :
    ∃ u v : List Letter,w=u++(.x::v) ∧ HeadPair (p*eval u) i j := by
  induction w generalizing p with
  | nil => simp [partners] at hj
  | cons a w ih =>
    cases a with
    | l =>
      obtain ⟨u,v,he,hp⟩ := ih (p*eval [.l]) hj
      refine ⟨.l::u,v,by simp [he],?_⟩
      simpa only [eval_cons_action,eval_nil,mul_one,mul_assoc] using hp
    | x =>
      rcases List.mem_append.mp hj with hhead | htail
      · exact ⟨[],w,rfl,by simpa using (mem_head_partners i j p).mp hhead⟩
      · obtain ⟨u,v,he,hp⟩ := ih (p*eval [.x]) htail
        refine ⟨.x::u,v,by simp [he],?_⟩
        simpa only [eval_cons_action,eval_nil,mul_one,mul_assoc] using hp
