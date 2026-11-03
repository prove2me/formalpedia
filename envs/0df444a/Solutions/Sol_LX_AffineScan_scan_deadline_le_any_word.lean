-- Prove2me | solution 1 for LX.AffineScan.scan_deadline_le_any_word
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:12:04.451755+00:00
-- url     : https://prove2.me/submissions/601af87a-9906-4dba-8ba3-ae60c9ef9720

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
import Definitions.Def_LX_AffineRankOrder
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_DeadlinePrice
import Definitions.Def_LX_DepthReturn
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyRotationOptimality
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SweepCarrier
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_exchange_backward_depth
import Theorems.Thm_LX_AffineScan_exchange_labels
import Theorems.Thm_LX_AffineScan_exists_depth_extreme
import Theorems.Thm_LX_AffineScan_exists_zero_depth
import Theorems.Thm_LX_AffineScan_queue_deadline_step_lower
import Theorems.Thm_LX_AffineScan_rotate_backward_depth
import Theorems.Thm_LX_AffineScan_saturated_sweep_rank_le_run
import Theorems.Thm_LX_AffineScan_sweep_prefix_depth
import Theorems.Thm_LX_AffineScan_sweep_step_head_depth
import Theorems.Thm_LX_AffineScan_zero_of_rank_le_zero

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
/-!
A balanced phase lift of an actual permutation, with subset majorization.
We minimize the nonnegative integer sum of squared displacements over all
balanced lifts and phases. Phase shifts yield majorization directly, without
assuming an affine inversion formula or a pre-existing bounded lift.
-/
namespace LX.Core.AffineLift
open scoped BigOperators







theorem canonical_lift {n : ℕ} (p : State n) :
    IsLift p 0 (fun i => (p.symm i : ℤ) - (i : ℤ)) := by
  constructor
  · rw [Finset.sum_sub_distrib]
    have h := Equiv.sum_comp p.symm (fun i : Fin n => (i : ℤ))
    rw [h]
    simp
  · intro i
    simp [Int.ModEq]




















end LX.Core.AffineLift

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









/-- A lower displacement bound controls every token's backward exchanges. -/
theorem backward_depth_le_strip {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LX.Core.AffineLift.IsLift p c d) (h : ℤ) (hlo : ∀ i, -h ≤ d i) (i : Fin n) :
    (backwardDepth d i : ℤ) ≤ h := by
  obtain ⟨a,hmax,he⟩ := exists_depth_extreme hd
  have hh : (backwardDepth d i : ℤ) ≤ backwardDepth d a := by exact_mod_cast hmax i
  have := hlo a
  omega




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









theorem sweep_head_zero (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) : backwardDepth (sweep d (n-1)) 0=0 := by
  obtain ⟨i,hi0⟩ := exists_zero_depth d
  have hh := (sweep_prefix_depth hn d hi (n-1) (by omega)).1 i.val (by have := i.isLt; omega)
  simpa [atDepth, hi0] using hh

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







theorem saturated_sweep_balance (d : Fin n → ℤ) (t : ℕ) :
    (∑ i,saturatedSweep d t i)=∑ i,d i := by
  unfold saturatedSweep compareHead
  split_ifs
  · rw [exchange_sum,sweep_balance]
  · rw [sweep_balance]



theorem saturated_sweep_zero_of_word (hn : 2 ≤ n) (d : Fin n → ℤ) (w : List Letter)
    (hb : ∑ i,d i=0) (hz : ∀ i,run w d i=0) :
    ∀ i,saturatedSweep d (w.count .l) i=0 := by
  have hr := saturated_sweep_rank_le_run hn d w
  have he : run w d=(fun _ => 0) := funext hz
  rw [he] at hr
  exact zero_of_rank_le_zero _ (by rw [saturated_sweep_balance,hb]) hr





end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem queue_deadline_sweep_lower (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (hz : backwardDepth d 0=0) (k : ℕ) :
    queueDeadline d ≤ queueDeadline (sweep d k)+k := by
  induction k generalizing d with
  | zero => simp [sweep]
  | succ k ih =>
    have hs := queue_deadline_step_lower hn d hi hz
    have hnext := (sweep_step_zero_queue hn d hi hz).1
    have hinj : Function.Injective (labels (sweepStep d)) := sweep_injective hn d hi 1
    have ht := ih (sweepStep d) hinj hnext
    rw [sweep_succ_start]
    omega

theorem queue_deadline_of_zero (d : Fin n → ℤ) (hz : ∀ i,d i=0) : queueDeadline d=0 := by
  have he : d=(fun _ => 0) := funext hz
  subst d
  have hd : LX.Core.AffineLift.IsLift (1 : State n) 0 (fun _ => 0) := by
    simpa only [← Equiv.Perm.inv_def,inv_one,Equiv.Perm.one_apply,sub_self] using
      LX.Core.AffineLift.canonical_lift (1 : State n)
  have hb (i : Fin n) : backwardDepth (fun _ : Fin n => 0) i=0 := by
    have hh := backward_depth_le_strip hd (0 : ℤ) (by simp) i
    omega
  simp [queueDeadline,hb]

theorem sweep_zero_persists (d : Fin n → ℤ) {a b : ℕ} (hab : a ≤ b)
    (hz : ∀ i,sweep d a i=0) : ∀ i,sweep d b i=0 := by
  have hzero (k : ℕ) : sweep (fun _ : Fin n => 0) k=(fun _ => 0) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [sweep,ih]; funext i; simp [sweepStep,compareHead,rotate]
  rw [show b=a+(b-a) by omega,sweep_add,funext hz,hzero]
  simp










end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- If the first lap leaves a positive queue, its deadline is also a
lower bound for every word realizing the same exact lift. -/
theorem solution (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i,d i=0) (hi : Function.Injective (labels d))
    (hq : 0 < queueDeadline (sweep d (n-1))) (w : List Letter)
    (hw : ∀ i,run w d i=0) : scanDeadline d ≤ w.count .l := by
  have hz := saturated_sweep_zero_of_word hn d w hb hw
  have hs : ∀ i,sweep d (w.count .l+1) i=0 := by
    intro i
    change saturatedSweep d (w.count .l) (finRotate n i)=0
    exact hz _
  have hstart : n-1 ≤ w.count .l+1 := by
    by_contra hnot
    have he := sweep_zero_persists d (by omega : w.count .l+1 ≤ n-1) hs
    have hq0 := queue_deadline_of_zero _ he
    omega
  have hqueue := queue_deadline_sweep_lower hn (sweep d (n-1))
    (sweep_injective hn d hi _) (sweep_head_zero hn d hi) (w.count .l+1-(n-1))
  have he : ∀ i,sweep (sweep d (n-1)) (w.count .l+1-(n-1)) i=0 := by
    rw [← sweep_add,show n-1+(w.count .l+1-(n-1))=w.count .l+1 by omega]
    exact hs
  rw [queue_deadline_of_zero _ he,zero_add] at hqueue
  unfold scanDeadline
  omega
