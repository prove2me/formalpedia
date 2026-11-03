-- Prove2me | solution 1 for LX.AffineScan.compare_zero_at_scan_deadline
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:12:03.71547+00:00
-- url     : https://prove2.me/submissions/4b81f58f-dbed-4371-932e-ad6572fe2b5a

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
import Theorems.Thm_LX_AffineScan_exchange_labels
import Theorems.Thm_LX_AffineScan_exists_zero_depth
import Theorems.Thm_LX_AffineScan_sweep_depth_deadline
import Theorems.Thm_LX_AffineScan_sweep_prefix_depth
import Theorems.Thm_LX_AffineScan_zero_of_depth_zero

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

theorem sweep_injective (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (k : ℕ) :
    Function.Injective (labels (sweep d k)) := by
  rw [← run_sweep_word]
  exact run_injective hn _ d hi

theorem sweep_balance (d : Fin n → ℤ) (k : ℕ) :
    ∑ i, sweep d k i = ∑ i, d i := by
  rw [← run_sweep_word, run_sum]











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





theorem sweep_queue_deadline (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (hz : backwardDepth d 0=0) :
    ∀ i, backwardDepth (sweep d (queueDeadline d)) i=0 := by
  apply sweep_depth_deadline hn d hi hz
  intro j hj hjn hpos
  have hh := Finset.le_sup (f := fun i : Fin n =>
    if backwardDepth d i=0 then 0 else (n-1)*(backwardDepth d i-1)+i.val)
    (Finset.mem_univ (j : Fin n))
  change 0 < backwardDepth d (j : Fin n) at hpos
  simpa only [queueDeadline,ite_eq_right (by omega : backwardDepth d (j : Fin n) ≠ 0),
    Fin.val_natCast, Nat.mod_eq_of_lt hjn, atDepth] using hh

theorem compare_zero_of_sweep_succ_zero (d : Fin n → ℤ) (k : ℕ)
    (hz : ∀ i, sweep d (k+1) i=0) :
    ∀ i, compareHead (sweep d k) i=0 := by
  intro i
  have hh := hz ((finRotate n).symm i)
  simpa only [sweep,sweepStep,rotate,Equiv.apply_symm_apply] using hh












end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

end LX.AnchoredPhases

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- A scalar computed from the first lap certifies the complete stopping trace. -/
theorem solution (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i,d i=0) (hi : Function.Injective (labels d)) :
    ∀ i, compareHead (sweep d (scanDeadline d)) i=0 := by
  have hei := sweep_injective hn d hi (n-1)
  have hdepth := sweep_queue_deadline hn (sweep d (n-1)) hei (sweep_head_zero hn d hi)
  have hz := zero_of_depth_zero _
    (show ∑ i, sweep (sweep d (n-1)) (queueDeadline (sweep d (n-1))) i=0 by
      rw [sweep_balance,sweep_balance,hb])
    (sweep_injective hn _ hei _) hdepth
  have he : scanDeadline d+1=(n-1)+queueDeadline (sweep d (n-1)) := by
    unfold scanDeadline
    omega
  apply compare_zero_of_sweep_succ_zero
  rw [he,sweep_add]
  exact hz
