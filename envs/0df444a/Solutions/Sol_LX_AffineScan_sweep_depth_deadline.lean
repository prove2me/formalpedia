-- Prove2me | solution 1 for LX.AffineScan.sweep_depth_deadline
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:02:35.036775+00:00
-- url     : https://prove2.me/submissions/cd865f94-aa87-4125-9275-bd914ca0a615

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
import Theorems.Thm_LX_AffineScan_rotate_backward_depth
import Theorems.Thm_LX_AffineScan_sweep_step_head_depth

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




















theorem run_append (u v : List Letter) (d : Fin n → ℤ) :
    run (u ++ v) d = run v (run u d) := by
  induction u generalizing d with
  | nil => rfl
  | cons a u ih => exact ih (step a d)



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



















theorem sweep_succ_start (d : Fin n → ℤ) (k : ℕ) :
    sweep d (k+1) = sweep (sweepStep d) k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg sweepStep ih






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









/-- After a zero-depth carrier is reached, the tail is a queue: it shifts once
and its first depth is decremented when appended at the other end. -/
theorem sweep_step_zero_queue (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (hz : backwardDepth d 0=0) :
    backwardDepth (sweepStep d) 0=0 ∧
      atDepth (sweepStep d) (n-1)=backwardDepth d 1-1 := by
  constructor
  · rw [sweep_step_head_depth hn d hi, hz, Nat.zero_min]
  · rw [sweep_step_last_depth hn]
    split_ifs with hdesc
    · rfl
    · have hh := sweep_step_head_depth hn d hi
      have he : sweepStep d=rotate d := by simp [sweepStep,compareHead,hdesc]
      rw [he,rotate_backward_depth hn] at hh
      simp only [finRotate_apply, zero_add, hz, Nat.zero_min] at hh
      omega
















end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Each positive queue entry has a deadline. Every step reduces all deadlines
by one, including the entry that wraps around the cursor. -/
theorem solution (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (hz : backwardDepth d 0=0)
    (k : ℕ) (hk : ∀ j : ℕ, 0 < j → j < n → 0 < atDepth d j →
      (n-1)*(atDepth d j-1)+j ≤ k) :
    ∀ i, backwardDepth (sweep d k) i=0 := by
  induction k generalizing d with
  | zero =>
    intro i
    by_cases hi0 : i=0
    · simpa [sweep,hi0] using hz
    · have hip : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi0
      have hh := hk i.val hip i.isLt
      simp only [atDepth, Fin.cast_val_eq_self] at hh
      simp only [sweep]
      by_contra hnot
      have hh' := hh (by omega)
      omega
  | succ k ih =>
    rw [sweep_succ_start]
    have hinj := sweep_injective hn d hi 1
    change Function.Injective (labels (sweepStep d)) at hinj
    have hqueue := sweep_step_zero_queue hn d hi hz
    apply ih (sweepStep d) hinj hqueue.1
    intro j hj hjn hpos
    by_cases hjl : j=n-1
    · subst j
      rw [hqueue.2] at hpos ⊢
      have hb : 1 < backwardDepth d 1 := by omega
      have hh := hk 1 (by omega) (by omega) (by exact Nat.zero_lt_of_lt hb)
      change (n-1)*(backwardDepth d 1-1)+1 ≤ k+1 at hh
      have he : (n-1)*(backwardDepth d 1-1-1)+(n-1) =
          (n-1)*(backwardDepth d 1-1) := by
        rw [← Nat.mul_add_one]
        congr 1
        omega
      rw [he]
      omega
    · rw [sweep_step_tail_depth hn _ j hj (by omega)] at hpos ⊢
      have hh := hk (j+1) (by omega) (by omega) hpos
      omega
