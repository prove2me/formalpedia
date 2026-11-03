-- Prove2me | solution 1 for LX.AffineScan.sweep_zero_of_depth_bound
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:12:26.144169+00:00
-- url     : https://prove2.me/submissions/96e5ec9d-1b44-47e2-96ce-197bd6531085

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
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_DepthReturn
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SweepCarrier
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_compare_head_tail_depth
import Theorems.Thm_LX_AffineScan_exchange_backward_depth
import Theorems.Thm_LX_AffineScan_exchange_labels
import Theorems.Thm_LX_AffineScan_exists_zero_depth
import Theorems.Thm_LX_AffineScan_rotate_backward_depth
import Theorems.Thm_LX_AffineScan_sweep_depth_deadline
import Theorems.Thm_LX_AffineScan_sweep_prefix_depth
import Theorems.Thm_LX_AffineScan_sweep_step_head_depth
import Theorems.Thm_LX_AffineScan_zero_of_depth_zero

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
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.ForwardCarrier
end LX.ForwardCarrier
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







theorem rotate_labels (d : Fin n → ℤ) (i : Fin n) :
    labels (rotate d) i = labels d (finRotate n i) - 1 := by
  simp only [labels, rotate, finRotate_apply]
  abel

theorem rotate_injective (d : Fin n → ℤ) (hi : Function.Injective (labels d)) :
    Function.Injective (labels (rotate d)) := by
  intro i j hij
  simp only [rotate_labels, sub_left_inj] at hij
  exact (finRotate n).injective (hi hij)



theorem exchange_injective (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) : Function.Injective (labels (exchange d)) := by
  intro i j hij
  simp only [exchange_labels hn] at hij
  exact (Equiv.swap (0 : Fin n) 1).injective (hi hij)

omit [NeZero n] in
theorem rotate_sum (d : Fin n → ℤ) : ∑ i, rotate d i = ∑ i, d i :=
  Equiv.sum_comp (finRotate n) d


theorem exchange_sum (d : Fin n → ℤ) : ∑ i, exchange d i = ∑ i, d i := by
  simp [exchange, Finset.sum_add_distrib, Finset.sum_sub_distrib, Equiv.sum_comp]















theorem run_append (u v : List Letter) (d : Fin n → ℤ) :
    run (u ++ v) d = run v (run u d) := by
  induction u generalizing d with
  | nil => rfl
  | cons a u ih => exact ih (step a d)

theorem run_sum (w : List Letter) (d : Fin n → ℤ) : ∑ i, run w d i = ∑ i, d i := by
  induction w generalizing d with
  | nil => rfl
  | cons a w ih =>
    rw [run, ih]
    cases a with
    | l => exact rotate_sum d
    | x => exact exchange_sum d

theorem run_injective (hn : 2 ≤ n) (w : List Letter) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) : Function.Injective (labels (run w d)) := by
  induction w generalizing d with
  | nil => exact hi
  | cons a w ih =>
    apply ih
    cases a with
    | l => exact rotate_injective d hi
    | x => exact exchange_injective hn d hi















end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]













theorem run_sweep_step (d : Fin n → ℤ) : run (sweepStepWord d) d = sweepStep d := by
  unfold sweepStepWord sweepStep compareHead
  split_ifs <;> rfl

theorem run_sweep_word (d : Fin n → ℤ) (k : ℕ) : run (sweepWord d k) d = sweep d k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sweepWord, run_append, ih, run_sweep_step, sweep]


























end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem at_depth_rotate (hn : 2 ≤ n) (d : Fin n → ℤ) (j : ℕ) :
    atDepth (rotate d) j = atDepth d (j+1) := by
  simp only [atDepth, rotate_backward_depth hn, finRotate_apply, Nat.cast_add, Nat.cast_one]




end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem sweep_injective (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (k : ℕ) :
    Function.Injective (labels (sweep d k)) := by
  rw [← run_sweep_word]
  exact run_injective hn _ d hi

theorem sweep_balance (d : Fin n → ℤ) (k : ℕ) :
    ∑ i, sweep d k i = ∑ i, d i := by
  rw [← run_sweep_word, run_sum]

theorem sweep_step_last_depth (hn : 2 ≤ n) (d : Fin n → ℤ) :
    atDepth (sweepStep d) (n-1) =
      if d 1+1 < d 0 then backwardDepth d 1-1 else backwardDepth d 0 := by
  rw [sweepStep, at_depth_rotate hn, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  simp only [atDepth, Fin.natCast_self, compareHead]
  split_ifs with hd
  · have hh := exchange_backward_depth hn d hd
    omega
  · rfl

theorem sweep_step_tail_depth (hn : 2 ≤ n) (d : Fin n → ℤ) (j : ℕ)
    (hj : 0 < j) (hjn : j+1 < n) :
    atDepth (sweepStep d) j = atDepth d (j+1) := by
  rw [sweepStep, at_depth_rotate hn, compare_head_tail_depth hn _ (j+1) (by omega) hjn]

theorem sweep_depth_le (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (h : ℕ)
    (hd : ∀ i, backwardDepth d i ≤ h) (k : ℕ) :
    ∀ i, backwardDepth (sweep d k) i ≤ h := by
  induction k with
  | zero => exact hd
  | succ k ih =>
    intro i
    have hinj := sweep_injective hn d hi k
    by_cases hi0 : i=0
    · subst i
      rw [sweep, sweep_step_head_depth hn _ hinj]
      exact (min_le_left _ _).trans (ih 0)
    · have hip : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi0
      suffices hs : atDepth (sweepStep (sweep d k)) i.val ≤ h by
        simpa [atDepth,sweep] using hs
      by_cases hil : i.val=n-1
      · rw [hil, sweep_step_last_depth hn]
        split_ifs <;> have h0 := ih 0 <;> have h1 := ih 1 <;> omega
      · rw [sweep_step_tail_depth hn _ _ hip (by have := i.isLt; omega)]
        exact ih _





theorem sweep_head_zero (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) : backwardDepth (sweep d (n-1)) 0=0 := by
  obtain ⟨i,hi0⟩ := exists_zero_depth d
  have hh := (sweep_prefix_depth hn d hi (n-1) (by omega)).1 i.val (by have := i.isLt; omega)
  simpa [atDepth, hi0] using hh







theorem sweep_add (d : Fin n → ℤ) (a b : ℕ) :
    sweep d (a+b)=sweep (sweep d a) b := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg sweepStep ih










end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- A depth bound h gives a concrete quadratic stopping time for the actual scan. -/
theorem solution (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i, d i=0) (hi : Function.Injective (labels d))
    (h : ℕ) (hd : ∀ i, backwardDepth d i ≤ h) :
    ∀ i, sweep d ((n-1)+(n-1)*h) i=0 := by
  let e := sweep d (n-1)
  have hei : Function.Injective (labels e) := sweep_injective hn d hi _
  have heh : ∀ i, backwardDepth e i ≤ h := sweep_depth_le hn d hi h hd _
  have hz := sweep_depth_deadline hn e hei (sweep_head_zero hn d hi) ((n-1)*h)
  have hz' : ∀ i, backwardDepth (sweep e ((n-1)*h)) i=0 := by
    apply hz
    intro j hj hjn hpos
    have hh := heh (j : Fin n)
    change atDepth e j ≤ h at hh
    have he : atDepth e j-1+1=atDepth e j := by omega
    have hmul := Nat.mul_le_mul_left (n-1) hh
    rw [← he, Nat.mul_add, Nat.mul_one] at hmul
    omega
  rw [sweep_add]
  apply zero_of_depth_zero _ _ (sweep_injective hn e hei _) hz'
  rw [sweep_balance,sweep_balance,hb]
