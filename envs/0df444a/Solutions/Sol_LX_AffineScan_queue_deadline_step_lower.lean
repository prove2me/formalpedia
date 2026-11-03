-- Prove2me | solution 1 for LX.AffineScan.queue_deadline_step_lower
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:06:45.660195+00:00
-- url     : https://prove2.me/submissions/7681b52c-90d4-4e40-822b-2a9d604a818b

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
import Definitions.Def_LX_DeadlinePrice
import Definitions.Def_LX_DepthReturn
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SweepCarrier
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_compare_head_tail_depth
import Theorems.Thm_LX_AffineScan_exchange_backward_depth
import Theorems.Thm_LX_AffineScan_rotate_backward_depth
import Theorems.Thm_LX_AffineScan_sweep_step_head_depth

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteGaps
end LX.Core.FiniteGaps
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
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



theorem at_depth_rotate (hn : 2 ≤ n) (d : Fin n → ℤ) (j : ℕ) :
    atDepth (rotate d) j = atDepth d (j+1) := by
  simp only [atDepth, rotate_backward_depth hn, finRotate_apply, Nat.cast_add, Nat.cast_one]




end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





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

section
/-! Extend a finite permutation to a contiguous window of a larger ambient
permutation, fixing every external label. No ambient size is changed. -/
namespace LX.Core.FiniteWindow
variable {n b : ℕ}



















@[simp] theorem permutation_embed (W : Window n b) (p : State b) (i : Fin b) :
    permutation W p (embed W i)=embed W (p i) := p.extendDomain_apply_image (windowEquiv W) i



@[simp] theorem permutation_symm (W : Window n b) (p : State b) :
    (permutation W p).symm=permutation W p.symm := rfl







end LX.Core.FiniteWindow

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem mem_descendingPositions (p : State n) (i : Fin n) :
    i ∈ descendingPositions p ↔ (p i).val < i.val := by
  simp [descendingPositions]









@[simp] theorem descending_positions_one : descendingPositions (1 : State n) = ∅ := by
  ext i
  simp




















end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem inversion_indicator_self (p : State n) (i : Fin n) :
    inversionIndicator p i i=0 := by simp [inversionIndicator]















end LX.Core.FiniteCuts

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

 theorem _root_.LX.UploadHelpers.QueueDeadlineLower.queue_term_le (d : Fin n → ℤ) (j : ℕ) (hj : j < n) :
    (if atDepth d j=0 then 0 else (n-1)*(atDepth d j-1)+j) ≤ queueDeadline d := by
  have hh := Finset.le_sup (f := fun i : Fin n =>
    if backwardDepth d i=0 then 0 else (n-1)*(backwardDepth d i-1)+i.val)
    (Finset.mem_univ (j : Fin n))
  convert hh using 1 <;>
    (try simp only [queueDeadline,atDepth,Fin.val_natCast,Nat.mod_eq_of_lt hj]) <;>
    with_unfolding_all rfl


















end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- A queue step cannot remove more than one unit of remaining deadline.
This is the lower counterpart of the existing completion bound. -/
theorem solution (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (hz : backwardDepth d 0=0) :
    queueDeadline d ≤ queueDeadline (sweepStep d)+1 := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  apply Finset.sup_le
  intro i _
  by_cases hi0 : i=0
  · subst i; simp [hz]
  · by_cases hb0 : backwardDepth d i=0
    · simp [hb0]
    · simp only [ite_eq_right hb0]
      have hip : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi0
      by_cases hi1 : i=1
      · subst i
        rw [hv1]
        have hq := sweep_step_zero_queue hn d hi hz
        have ht := _root_.LX.UploadHelpers.QueueDeadlineLower.queue_term_le (sweepStep d) (n-1) (by omega)
        rw [hq.2] at ht
        by_cases hb1 : backwardDepth d 1=1
        · simp [hb1]
        · have hb2 : 2 ≤ backwardDepth d 1 := by omega
          rw [ite_eq_right (by omega : backwardDepth d 1-1 ≠ 0)] at ht
          have he : (n-1)*(backwardDepth d 1-1-1)+(n-1)=
              (n-1)*(backwardDepth d 1-1) := by
            rw [← Nat.mul_add_one]
            congr 1
            omega
          rw [he] at ht
          omega
      · have hip2 : 2 ≤ i.val := by
          have hne1 : i.val ≠ 1 := fun h => hi1 (Fin.ext (by omega))
          omega
        have ht := _root_.LX.UploadHelpers.QueueDeadlineLower.queue_term_le (sweepStep d) (i.val-1) (by have := i.isLt; omega)
        rw [sweep_step_tail_depth hn d (i.val-1) (by omega) (by have := i.isLt; omega),
          Nat.sub_add_cancel (by omega : 1 ≤ i.val)] at ht
        simp only [atDepth,Fin.cast_val_eq_self] at ht
        rw [ite_eq_right hb0] at ht
        omega
