-- Prove2me | solution 1 for LX.AffineScan.ScanTrace.rotations_le_of_compare_zero
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:45:15.175043+00:00
-- url     : https://prove2.me/submissions/c0895af3-b16d-46f0-a10f-116bcfd08b38

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
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SweepCarrier
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_ScanTrace_unique

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

theorem ite_eq_left {α : Sort u} {p : Prop} {inst : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h



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





















theorem compare_head_zero (hn : 2 ≤ n) (d : Fin n → ℤ) :
    atTarget (compareHead d) 0 = min (atTarget d 0) (atTarget d 1) := by
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  simp only [compareHead, atTarget, Nat.cast_zero, Nat.cast_one, zero_add]
  split_ifs with h
  · simp only [exchange, Equiv.swap_apply_left, h01, ite_true, ite_false, sub_zero]
    rw [min_eq_right (by omega)]
    omega
  · exact (min_eq_left (by omega)).symm

theorem compare_head_one (hn : 2 ≤ n) (d : Fin n → ℤ) :
    atTarget (compareHead d) 1 = max (atTarget d 0) (atTarget d 1) := by
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  simp only [compareHead, atTarget, Nat.cast_zero, Nat.cast_one, zero_add]
  split_ifs with h
  · simp only [exchange, Equiv.swap_apply_right, Ne.symm h01, ite_true, ite_false, add_zero]
    rw [max_eq_left (by omega)]
    omega
  · exact (max_eq_right (by omega)).symm









/-- A real descent exchange leaves the head sorted, as required by the return lemma. -/
theorem exchanged_head_sorted (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hdesc : d 1+1 < d 0) : atTarget (exchange d) 0 ≤ atTarget (exchange d) 1 := by
  have h0 := compare_head_zero hn d
  have h1 := compare_head_one hn d
  simp only [compareHead, ite_eq_left hdesc] at h0 h1
  rw [h0, h1]
  exact min_le_max

theorem sweep_succ_start (d : Fin n → ℤ) (k : ℕ) :
    sweep d (k+1) = sweep (sweepStep d) k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg sweepStep ih






end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Once the bounded comparison schedule has sorted, the genuine stopping trace
has used no more than the scheduled number of rotations. -/
theorem solution (hn : 2 ≤ n) {d : Fin n → ℤ}
    {w : List Letter} (ht : ScanTrace d w) (k : ℕ)
    (hz : ∀ i, compareHead (sweep d k) i = 0) : w.count .l ≤ k := by
  induction k generalizing d w with
  | zero =>
    cases ht with
    | done => simp
    | @left d w hnon hle tail =>
      have he : compareHead (sweep d 0) = d := by
        simp [sweep, compareHead, not_lt.mpr hle]
      rw [he] at hz
      exact False.elim (hnon hz)
    | @swap d w hdesc tail =>
      have he : compareHead (sweep d 0) = exchange d := by
        simp [sweep, compareHead, hdesc]
      rw [he] at hz
      have hw : w=[] := tail.unique (ScanTrace.done hz)
      simp [hw]
  | succ k ih =>
    rw [sweep_succ_start] at hz
    cases ht with
    | done => simp
    | @left d w hnon hle tail =>
      have he : sweepStep d = rotate d := by simp [sweepStep, compareHead, not_lt.mpr hle]
      rw [he] at hz
      have hh := ih tail hz
      simpa only [List.count_cons_self] using Nat.add_le_add_right hh 1
    | @swap d w hdesc tail =>
      have he : sweepStep d = rotate (exchange d) := by simp [sweepStep, compareHead, hdesc]
      rw [he] at hz
      cases tail with
      | done => simp
      | left _ _ tail' =>
        have hh := ih tail' hz
        simpa using Nat.add_le_add_right hh 1
      | swap hdesc' _ =>
        have hh := exchanged_head_sorted hn d hdesc
        simp only [atTarget, Nat.cast_zero, Nat.cast_one, zero_add] at hh
        omega
