-- Prove2me | solution 1 for LX.AffineScan.sweep_prefix_values
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:00:49.538809+00:00
-- url     : https://prove2.me/submissions/297e4046-3d06-41f2-8d37-512eb174386e

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
import Definitions.Def_LX_ForwardCarrier
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SweepCarrier
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
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace List
end List

section
/-! Compatibility aliases for core if-then-else lemmas renamed after Lean 4.33.1.
The source proof bodies use the newer names; these aliases preserve their types.
-/
namespace LX
universe u



theorem ite_eq_right {α : Sort u} {p : Prop} {inst : Decidable p} {a b : α} (h : ¬ p) :
    (if p then a else b) = b := if_neg h

end LX

namespace List
universe u

end List

/-
The following proof is adapted from Mathlib, copyright (c) 2026 Seewoo Lee,
licensed under Apache 2.0. Source revision 56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/Algebra/Order/Floor/BigOperators.lean, lines 28-45.
-/
namespace Int
open scoped BigOperators


end Int

end

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
namespace LX.ForwardCarrier





theorem prefix_tail (F : ℕ → ℤ) (k j : ℕ) (hkj : k < j) : sweepPrefix F k j = F j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [sweepPrefix, compareAt, ite_eq_right (by omega : j ≠ k), ite_eq_right (by omega : j ≠ k+1)]
    exact ih (by omega)

theorem carrier_step (F : ℕ → ℤ) (k : ℕ) :
    sweepPrefix F (k+1) (k+1) = max (sweepPrefix F k k) (F (k+1)) := by
  simp only [sweepPrefix, compareAt, ite_eq_right (by omega : k+1 ≠ k), ite_true]
  rw [prefix_tail F k (k+1) (by omega)]







end LX.ForwardCarrier

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
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]


















theorem at_rotate (d : Fin n → ℤ) (j : ℕ) :
    atTarget (rotate d) j = atTarget d (j+1) - 1 := by
  simp only [atTarget, rotate, finRotate_apply, Nat.cast_add, Nat.cast_one]
  omega




theorem compare_head_one (hn : 2 ≤ n) (d : Fin n → ℤ) :
    atTarget (compareHead d) 1 = max (atTarget d 0) (atTarget d 1) := by
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  simp only [compareHead, atTarget, Nat.cast_zero, Nat.cast_one, zero_add]
  split_ifs with h
  · simp only [exchange, Equiv.swap_apply_right, Ne.symm h01, ite_true, ite_false, add_zero]
    rw [max_eq_left (by omega)]
    omega
  · exact (max_eq_right (by omega)).symm

theorem compare_head_tail (d : Fin n → ℤ) (j : ℕ) (hj : 2 ≤ j) (hjn : j < n) :
    atTarget (compareHead d) j = atTarget d j := by
  have hj0 : (j : Fin n) ≠ 0 := by
    intro h
    have hh := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt hjn] at hh
    omega
  have hj1 : (j : Fin n) ≠ 1 := by
    intro h
    have hh := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt hjn, Nat.mod_eq_of_lt (by omega : 1 < n)] at hh
    omega
  unfold compareHead
  split_ifs
  · simp [atTarget, exchange, Equiv.swap_apply_of_ne_of_ne hj0 hj1, hj0, hj1]
  · rfl

theorem sweep_step_head (hn : 2 ≤ n) (d : Fin n → ℤ) :
    atTarget (sweepStep d) 0 = max (atTarget d 0) (atTarget d 1) - 1 := by
  rw [sweepStep, at_rotate, compare_head_one hn]














end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- A prefix of the actual LX program has the ordinary forward carrier and untouched future entries. -/
theorem solution (hn : 2 ≤ n) (d : Fin n → ℤ) (k : ℕ) (hk : k < n) :
    atTarget (sweep d k) 0 = ForwardCarrier.sweepPrefix (atTarget d) k k - k ∧
    ∀ j : ℕ, 0 < j → j+k < n →
      atTarget (sweep d k) j = atTarget d (j+k) - k := by
  induction k with
  | zero => simp [sweep, ForwardCarrier.sweepPrefix]
  | succ k ih =>
    obtain ⟨hhead, htail⟩ := ih (by omega)
    constructor
    · rw [sweep, sweep_step_head hn, hhead, htail 1 (by omega) (by omega),
        ForwardCarrier.carrier_step]
      have he : 1+k=k+1 := by omega
      rw [he]
      push_cast
      by_cases h : ForwardCarrier.sweepPrefix (atTarget d) k k ≤ atTarget d (k+1)
      · rw [max_eq_right h, max_eq_right (by omega)]
        omega
      · rw [max_eq_left (by omega : atTarget d (k+1) ≤ ForwardCarrier.sweepPrefix (atTarget d) k k),
          max_eq_left (by omega)]
        omega
    · intro j hj hjk
      rw [sweep, sweepStep, at_rotate, compare_head_tail _ (j+1) (by omega) (by omega),
        htail (j+1) (by omega) (by omega)]
      have he : j+1+k=j+(k+1) := by omega
      rw [he]
      push_cast
      omega
