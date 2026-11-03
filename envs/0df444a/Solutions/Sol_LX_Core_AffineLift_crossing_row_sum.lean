-- Prove2me | solution 1 for LX.Core.AffineLift.crossing_row_sum
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:30:59.199687+00:00
-- url     : https://prove2.me/submissions/eb6cdfa2-bd43-4362-b752-e53b47775afc

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
/-! Integer residues and normalization of the phase of a balanced lift.
The normalized phase is represented by an element of `Fin n`. -/
namespace LX.Core.AffineLift
open scoped Fin.IntCast Fin.NatCast

variable {n : ℕ} [NeZero n]

theorem modulus_pos : (0 : ℤ) < n := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)








end LX.Core.AffineLift

end

section
/-! Signed affine crossing data obtained from an actual balanced phase lift.
The row-sum identity is proved from bijectivity of endpoint residues. -/
namespace LX.Core.AffineLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem cast_eq_of_modEq {a b : ℤ} (h : Int.ModEq (n : ℤ) a b) :
    (a : Fin n) = (b : Fin n) := by
  apply Fin.ext
  rw [Fin.val_intCast, Fin.val_intCast]
  exact congrArg Int.toNat h

theorem lift_residue {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i : Fin n) :
    i + (d i : Fin n) = p.symm i + (c : Fin n) := by
  have h := cast_eq_of_modEq (hd.2 i)
  simpa using h





theorem numerator_cast {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i j : Fin n) :
    (crossingNumerator d i j : Fin n) = p.symm j - p.symm i := by
  simp only [crossingNumerator, Int.cast_sub, Int.cast_add]
  simp only [Int.cast_natCast, Fin.cast_val_eq_self]
  calc
    j - i + (d j : Fin n) - (d i : Fin n) =
        (j + (d j : Fin n)) - (i + (d i : Fin n)) := by abel
    _ = (p.symm j + (c : Fin n)) - (p.symm i + (c : Fin n)) := by
      rw [lift_residue hd j, lift_residue hd i]
    _ = p.symm j - p.symm i := by abel

theorem numerator_remainder {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i j : Fin n) :
    crossingNumerator d i j % (n : ℤ) = ((p.symm j - p.symm i : Fin n) : ℤ) := by
  have h := congrArg (fun a : Fin n => (a : ℤ)) (numerator_cast hd i j)
  have hz : ((crossingNumerator d i j : Fin n) : ℤ) = crossingNumerator d i j % (n : ℤ) := by
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    simpa only [Fin.val_intCast] using
      Int.toNat_of_nonneg (Int.emod_nonneg (crossingNumerator d i j) hn0)
  exact hz.symm.trans h

theorem numerator_sum {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i : Fin n) :
    ∑ j, crossingNumerator d i j = (∑ j : Fin n, (j : ℤ)) - (n : ℤ) * d i := by
  have hshift := Equiv.sum_comp (Equiv.subRight i) (fun j : Fin n => (j : ℤ))
  change (∑ j : Fin n, ((j - i : Fin n) : ℤ)) = ∑ j : Fin n, (j : ℤ) at hshift
  simp only [crossingNumerator, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hshift, hd.1]
  simp

theorem remainder_sum {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i : Fin n) :
    ∑ j, crossingNumerator d i j % (n : ℤ) = ∑ j : Fin n, (j : ℤ) := by
  simp_rw [numerator_remainder hd]
  exact Equiv.sum_comp (p.symm.trans (Equiv.subRight (p.symm i)))
    (fun j : Fin n => (j : ℤ))
















end LX.Core.AffineLift

end

namespace LX.Core.AffineLift
end LX.Core.AffineLift
open LX
open LX.Core
open LX.Core.AffineLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Net signed crossings of a token equal its exact integer displacement. -/
theorem solution {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i : Fin n) : ∑ j, crossing d i j = d i := by
  have hdiv : (n : ℤ) * (∑ j, crossingNumerator d i j / (n : ℤ)) +
      (∑ j, crossingNumerator d i j % (n : ℤ)) = ∑ j, crossingNumerator d i j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact Int.mul_ediv_add_emod _ _
  rw [remainder_sum hd, numerator_sum hd] at hdiv
  have he : (∑ j, crossingNumerator d i j / (n : ℤ)) = -d i := by
    apply (mul_left_cancel₀ (ne_of_gt (modulus_pos (n := n))))
    linarith [hdiv]
  simp only [crossing, Finset.sum_neg_distrib, he, neg_neg]
