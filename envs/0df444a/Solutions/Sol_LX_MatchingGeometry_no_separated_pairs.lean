-- Prove2me | solution 1 for LX.MatchingGeometry.no_separated_pairs
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:36:38.049785+00:00
-- url     : https://prove2.me/submissions/08e2f3a0-6f3b-446d-b470-fcac1d90e637

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
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_MatchingGeometry_pair_contains_gap_two

namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.MatchingGeometry
end LX.MatchingGeometry

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
namespace LX.MatchingGeometry
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}



variable [NeZero n]

theorem eq_add_of_value_add (i j : Fin n) (k : ℕ) (h : i.val+k=j.val) : i+(k : Fin n)=j := by
  have he := congrArg (fun t : ℕ => (t : Fin n)) h
  simpa only [Nat.cast_add,Fin.cast_val_eq_self] using he








end LX.MatchingGeometry

end

namespace LX.MatchingGeometry
end LX.MatchingGeometry
open LX
open LX.MatchingGeometry
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}
variable [NeZero n]

/-- Two separated intervals would contain two different cyclic gap-two pairs. -/
theorem solution (q : State n) (hinv : Function.Involutive q)
    (hnc : LX.Core.FiniteCuts.NoncrossingPairs q)
    (hnoadj : ∀ i : Fin n,q i ≠ i+1)
    (hnofix : ∀ i : Fin n,q i=i → q (i+1) ≠ i+1)
    (hunique : ∀ i j : Fin n,q i=i+2 → q j=j+2 → i=j) :
    LX.Core.FiniteCuts.NoSeparatedPairs q := by
  have hnoadj' (i : Fin n) : i.val+1 ≠ (q i).val := by
    intro hh
    exact hnoadj i (eq_add_of_value_add i (q i) 1 hh).symm
  have hnofix' (i j : Fin n) (hij : i.val+1=j.val) (hi : q i=i) : q j ≠ j := by
    have he := eq_add_of_value_add i j 1 hij
    have he' : i+1=j := he
    rw [← he']
    exact hnofix i hi
  intro a b c d hab hbc hcd hpab hpcd
  obtain ⟨x,y,hax,hyb,hxy,hpx⟩ := pair_contains_gap_two q hinv hnc hnoadj' hnofix' a b hab hpab
  obtain ⟨u,v,hcu,hvd,huv,hpu⟩ := pair_contains_gap_two q hinv hnc hnoadj' hnofix' c d hcd hpcd
  have he := hunique x u (hpx.trans (eq_add_of_value_add x y 2 hxy).symm)
    (hpu.trans (eq_add_of_value_add u v 2 huv).symm)
  have hv := congrArg Fin.val he
  omega
