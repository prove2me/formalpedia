-- Prove2me | solution 1 for LX.AffineScan.exists_descent
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:32:40.506632+00:00
-- url     : https://prove2.me/submissions/069f6b37-c249-4df4-b880-0deaa1ad4d3d

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
import Definitions.Def_LX_AffineCrossings
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
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
/-! Signed affine crossing data obtained from an actual balanced phase lift.
The row-sum identity is proved from bijectivity of endpoint residues. -/
namespace LX.Core.AffineLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]






















@[simp] theorem crossing_self (d : Fin n → ℤ) (i : Fin n) : crossing d i i = 0 := by
  simp [crossing, crossingNumerator]









end LX.Core.AffineLift

end

section
/-! Physical positions, a paid cursor, and literal L/R/X words.
Every physical operation is proved to induce the same visible generator.
A realized balanced lift ends at the original target in its exact orientation. -/
namespace LX.Core.PhysicalModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open AffineLift



variable {n : ℕ} [NeZero n]















@[simp] theorem visible_initial : visible (initial (n := n)) = 1 := by
  simp [visible, initial]


end LX.Core.PhysicalModel

end

section
/-! Literal LX.Core execution with an integer cursor and integer positions of every
named token. The position log records winding, including exchanges at the seam.
Its residues are proved to agree with the finite physical permutation. -/
namespace LX.Core.LiftedModel
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing



variable {n : ℕ} [NeZero n]







theorem neighboring_positions_distinct (hn : 2 ≤ n) (c : Fin n) : c ≠ c + 1 := by
  have h1 : (1 : Fin n) ≠ 0 := by
    intro h
    have := Fin.one_eq_zero_iff.mp h
    omega
  intro h
  have h' : c + 0 = c + 1 := by simpa using h
  exact h1 (add_left_cancel h').symm





























end LX.Core.LiftedModel

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
/-! Local invariants for the forward scan used to construct LX words.
This module proves progress and energy descent, not the quadratic price. -/
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]
























theorem constant_of_neighbor_le (d : Fin n → ℤ)
    (h : ∀ i, d i ≤ d (finRotate n i)) : ∀ i, d i = d 0 := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ k =>
    have hm : Monotone d := Fin.monotone_iff_le_succ.mpr (by
      intro i
      have he : finRotate (k + 1) i.castSucc = i.succ := by
        apply Fin.ext
        rw [coe_finRotate_of_ne_last (ne_of_lt (Fin.castSucc_lt_last i))]
        rfl
      simpa only [he] using h i.castSucc)
    have hl : d (Fin.last k) ≤ d 0 := by simpa only [finRotate_last] using h (Fin.last k)
    intro i
    exact le_antisymm ((hm (Fin.le_last i)).trans hl) (hm (Fin.zero_le i))

theorem zero_of_neighbor_le (d : Fin n → ℤ) (hb : ∑ i, d i = 0)
    (h : ∀ i, d i ≤ d (finRotate n i)) : ∀ i, d i = 0 := by
  have hc := constant_of_neighbor_le d h
  have hs : (n : ℤ) * d 0 = 0 := by simpa only [hc, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using hb
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hz := (mul_eq_zero.mp hs).resolve_left hn
  intro i
  exact (hc i).trans hz



























end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- An unsorted balanced affine permutation has a legal exchange during a forward lap. -/
theorem solution (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i, d i = 0) (hi : Function.Injective (labels d))
    (hz : ¬ ∀ i, d i = 0) : ∃ i, d (finRotate n i) + 1 < d i := by
  by_contra hno
  push Not at hno
  apply hz
  apply zero_of_neighbor_le d hb
  intro i
  have hne : d i ≠ d (finRotate n i) + 1 := by
    intro he
    have hh : labels d i = labels d (finRotate n i) := by
      simp only [labels, he, Int.cast_add, Int.cast_one, finRotate_apply]
      abel
    have hc := hi hh
    exact LX.Core.LiftedModel.neighboring_positions_distinct hn i (by
      simpa only [finRotate_apply] using hc)
  have hh := hno i
  omega
