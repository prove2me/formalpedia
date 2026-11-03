-- Prove2me | solution 1 for LX.FinitePairReduction.delete_returning_pair
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:43:24.222213+00:00
-- url     : https://prove2.me/submissions/cd4bc381-795e-4048-9af2-231d811193c2

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



theorem head_swap (p : State n) (a b : Fin n) (hp : HeadPair p a b) :
    p*eval [.x]=Equiv.swap a b*p := by
  have he : p*eval [.x]=Equiv.swap (p 0) (p 1)*p := by
    apply Equiv.ext
    intro i
    change p (Equiv.swap 0 1 i)=Equiv.swap (p 0) (p 1) (p i)
    exact Function.Injective.map_swap p.injective 0 1 i
  rcases hp with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · simpa only [h0,h1] using he
  · simpa only [h0,h1,Equiv.swap_comm b a] using he



















end LX.FinitePairReduction

end

namespace LX.FinitePairReduction
end LX.FinitePairReduction
open LX
open LX.FinitePairReduction
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Delete two actual exchanges of the same finite pair. The intervening
word, every L, and the final finite permutation are preserved. -/
theorem solution (p : State n) (a b : Fin n) (u v : List Letter)
    (hfirst : HeadPair p a b) (hsecond : HeadPair (p*eval [.x]*eval u) a b) :
    p*eval (.x::(u++(.x::v)))=p*eval (u++v) := by
  have h1 := head_swap p a b hfirst
  have h2 := head_swap (p*eval [.x]*eval u) a b hsecond
  have hss : (Equiv.swap a b : State n)*Equiv.swap a b=1 := by
    apply Equiv.ext
    intro i
    simp
  have he : (p*eval [.x]*eval u)*eval [.x]=p*eval u := by
    rw [h2,h1]
    simp only [← mul_assoc,hss,one_mul]
  have hh := congrArg (fun q : State n => q*eval v) he
  simpa only [eval_cons_action,eval_nil,mul_one,eval_append,mul_assoc] using hh
