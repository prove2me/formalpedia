-- Prove2me | solution 1 for LX.MatchingGeometry.pair_contains_gap_two
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:34:47.43506+00:00
-- url     : https://prove2.me/submissions/7b00dc01-3e5b-4211-b4d7-62c8d0ec83b2

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
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_Core_FiniteCuts_noncrossing_pair_interior

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

namespace LX.MatchingGeometry
end LX.MatchingGeometry
open LX
open LX.MatchingGeometry
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}

/-- If there are no adjacent fixed points and no adjacent pair, every pair
interval contains a pair whose endpoints are exactly two positions apart. -/
theorem solution (q : State n) (hinv : Function.Involutive q)
    (hnc : LX.Core.FiniteCuts.NoncrossingPairs q)
    (hnoadj : ∀ i : Fin n,i.val+1 ≠ (q i).val)
    (hnofix : ∀ i j : Fin n,i.val+1=j.val → q i=i → q j ≠ j)
    (a b : Fin n) (hab : a.val < b.val) (he : q a=b) :
    ∃ x y : Fin n,a.val ≤ x.val ∧ y.val ≤ b.val ∧ x.val+2=y.val ∧ q x=y := by
  by_cases htwo : a.val+2=b.val
  · exact ⟨a,b,le_rfl,le_rfl,htwo,he⟩
  · have hgap : a.val+2 < b.val := by
      have hno := hnoadj a
      rw [he] at hno
      omega
    have hmoved : ∃ x : Fin n,a.val < x.val ∧ x.val < b.val ∧ q x ≠ x := by
      let x : Fin n := ⟨a.val+1,by have := b.isLt; omega⟩
      by_cases hx : q x=x
      · let y : Fin n := ⟨a.val+2,by have := b.isLt; omega⟩
        refine ⟨y,by dsimp [y]; omega,by dsimp [y]; omega,?_⟩
        exact hnofix x y rfl hx
      · exact ⟨x,by dsimp [x]; omega,by dsimp [x]; omega,hx⟩
    obtain ⟨x,hax,hxb,hx⟩ := hmoved
    have hinside := LX.Core.FiniteCuts.noncrossing_pair_interior q hinv hnc a b x hax hxb he
    have hne : (q x).val ≠ x.val := fun hh => hx (Fin.ext hh)
    by_cases hxp : x.val < (q x).val
    · obtain ⟨u,v,hu,hv,huv,heq⟩ := solution q hinv hnc hnoadj hnofix x (q x) hxp rfl
      exact ⟨u,v,by omega,by omega,huv,heq⟩
    · obtain ⟨u,v,hu,hv,huv,heq⟩ := solution q hinv hnc hnoadj hnofix
        (q x) x (by omega) (hinv x)
      exact ⟨u,v,by omega,by omega,huv,heq⟩
termination_by b.val-a.val
 decreasing_by all_goals omega
