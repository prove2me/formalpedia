-- Prove2me | solution 1 for LX.AffineScan.word_with_nonmaximal_head
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:21:34.563097+00:00
-- url     : https://prove2.me/submissions/3e1af75e-aad7-4ef5-8468-37f1f64f7e47

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
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_DeadlinePrice
import Definitions.Def_LX_DepthReturn
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FirstLapFormula
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SweepCarrier
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_ScanTrace_exchange_count
import Theorems.Thm_LX_AffineScan_ScanTrace_rotations_le_of_compare_zero
import Theorems.Thm_LX_AffineScan_compare_zero_at_scan_deadline
import Theorems.Thm_LX_AffineScan_exchange_labels
import Theorems.Thm_LX_AffineScan_exists_scan_trace
import Theorems.Thm_LX_AffineScan_first_lap_depth_formula
import Theorems.Thm_LX_AffineScan_prefix_minimum_le_iff
import Theorems.Thm_LX_AffineScan_rotate_inversions
import Theorems.Thm_LX_AffineScan_sorting_word_of_zero

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
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
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


















@[simp] theorem crossing_self (d : Fin n → ℤ) (i : Fin n) : crossing d i i = 0 := by
  simp [crossing, crossingNumerator]









end LX.Core.AffineLift

end

section
/-! A zero-displacement phase lift is an actual rotation. Its final rotation
is explicitly paid by an LX.Core word of length at most n-1. -/
namespace LX.Core.AffineLift
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem rotation_power_apply (k : ℕ) (i : Fin n) : (L n ^ k) i = i + (k : Fin n) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih]
    simp [L, finRotate_apply, Nat.cast_add, add_comm, add_left_comm]


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







theorem run_left_apply (k : ℕ) (d : Fin n → ℤ) (i : Fin n) :
    run (List.replicate k .l) d i = d (((LX.Core.L n)^k) i) := by
  induction k generalizing d with
  | zero => simp [run]
  | succ k ih =>
    simp only [List.replicate_succ, run, step]
    rw [ih]
    simp only [rotate, LX.Core.L, pow_succ', Equiv.Perm.mul_apply]







end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem ScanTrace.run_zero {d : Fin n → ℤ} {w : List Letter} (ht : ScanTrace d w) :
    ∀ i, run w d i = 0 := by
  induction ht with
  | done hz => exact hz
  | left _ _ _ ih => exact ih
  | swap _ _ ih => exact ih















end LX.AffineScan

end

section
/-! Choosing a different root cyclically relabels crossing data and preserves
the exact affine exchange price. -/
namespace LX.Core.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem crossing_recentered (d : Fin n → ℤ) (r i j : Fin n) :
    AffineLift.crossing (localDisplacement d r) i j=
      AffineLift.crossing d ((L n^r.val) i) ((L n^r.val) j) := by
  have hsub : (L n^r.val) j-(L n^r.val) i=j-i := by
    simp only [AffineLift.rotation_power_apply, Fin.cast_val_eq_self]
    abel
  simp only [AffineLift.crossing, AffineLift.crossingNumerator, localDisplacement, hsub]







end LX.Core.RotationWords

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]























theorem length_eq_counts (w : List Letter) : w.length = w.count .l + w.count .x := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]







end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem recentered_backward_depth (d : Fin n → ℤ) (r i : Fin n) :
    backwardDepth (LX.Core.RotationWords.localDisplacement d r) i =
      backwardDepth d ((LX.Core.L n ^ r.val) i) := by
  unfold backwardDepth
  simp_rw [LX.Core.RotationWords.crossing_recentered]
  exact Equiv.sum_comp (LX.Core.L n ^ r.val)
    (fun j => (-LX.Core.AffineLift.crossing d ((LX.Core.L n ^ r.val) i) j).toNat)












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











theorem ScanTrace.rotations_le_deadline (hn : 2 ≤ n) {d : Fin n → ℤ}
    {w : List Letter} (ht : ScanTrace d w) (hb : ∑ i,d i=0)
    (hi : Function.Injective (labels d)) : w.count .l ≤ scanDeadline d :=
  ht.rotations_le_of_compare_zero hn _ (compare_zero_at_scan_deadline hn d hb hi)








end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

end LX.AnchoredPhases

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem first_lap_depth_le_pred (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (h : ℕ)
    (hmax : ∀ i, backwardDepth d i ≤ h) (hhead : backwardDepth d 0 < h) :
    ∀ i, backwardDepth (sweep d (n-1)) i ≤ h-1 := by
  intro i
  rw [first_lap_depth_formula hn d hi]
  split_ifs with hi0
  · omega
  · unfold emittedDepth
    split_ifs
    · have hh := hmax i
      simp only [atDepth,Fin.cast_val_eq_self]
      omega
    · have hh := (prefix_minimum_le_iff (atDepth d) (i.val-1)
        (prefixMinimum (atDepth d) (i.val-1))).mp le_rfl 0 (by omega)
      change _ ≤ backwardDepth d 0 at hh
      omega

theorem queue_deadline_le (d : Fin n → ℤ) (h : ℕ)
    (hmax : ∀ i, backwardDepth d i ≤ h) : queueDeadline d ≤ (n-1)*h := by
  unfold queueDeadline
  apply Finset.sup_le
  intro i _
  split_ifs with hz
  · omega
  · have hi := i.isLt
    have hh := Nat.mul_le_mul_left (n-1) (hmax i)
    have he : backwardDepth d i-1+1=backwardDepth d i := by omega
    rw [← he,Nat.mul_add,Nat.mul_one] at hh
    omega

/-- A head below the maximum depth saves a whole lap in the stopping bound. -/
theorem scan_deadline_head_reserve (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (h : ℕ)
    (hmax : ∀ i, backwardDepth d i ≤ h) (hhead : backwardDepth d 0 < h) :
    scanDeadline d ≤ h*(n-1)-1 := by
  have hq := queue_deadline_le (sweep d (n-1)) (h-1)
    (first_lap_depth_le_pred hn d hi h hmax hhead)
  have hp : 1 ≤ h := by omega
  have he : (n-1)+(n-1)*(h-1)=h*(n-1) := by
    have hh : h-1+1=h := by omega
    calc
      _ = (h-1+1)*(n-1) := by ring
      _ = _ := by rw [hh]
  unfold scanDeadline
  omega

theorem left_run_inversions (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i,d i=0) (hi : Function.Injective (labels d)) (k : ℕ) :
    inversions (run (List.replicate k .l) d)=inversions d := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ,run,step]
    rw [ih (rotate d) (by rw [rotate_sum,hb]) (rotate_injective d hi),rotate_inversions hn d hb hi]


end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts LX.AffineScan
variable {n : ℕ} [NeZero n]











end LX.AnchoredPhases

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Charge the chosen prefix explicitly while retaining the actual number
of exchanges. This is the input needed to spend an inversion reserve. -/
theorem solution (hn : 2 ≤ n) (p : State n) (c : ℤ)
    (d : Fin n → ℤ) (hd : IsLift p.symm c d) (h : ℕ) (r : Fin n)
    (hmax : ∀ i,backwardDepth d i ≤ h) (hhead : backwardDepth d r < h) :
    ∃ v : List Letter,p*eval v=1 ∧
      (v.length : ℤ) ≤ inversions d+((h : ℤ)+1)*((n : ℤ)-1)+r.val-1 := by
  let u : List Letter := List.replicate r.val .l
  let e := run u d
  have hl (i : Fin n) : labels d i=p i+(c : Fin n) := by
    simpa only [labels,Equiv.symm_symm] using lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.injective (add_right_cancel hij)
  have he : e=LX.Core.RotationWords.localDisplacement d r := by
    funext i
    exact run_left_apply r.val d i
  have hei : Function.Injective (labels e) := run_injective hn u d hi
  have heb : ∑ i,e i=0 := (run_sum u d).trans hd.1
  have hem (i : Fin n) : backwardDepth e i ≤ h := by
    rw [he,recentered_backward_depth]
    exact hmax _
  have heh : backwardDepth e 0 < h := by
    rw [he,recentered_backward_depth]
    simpa only [LX.Core.AffineLift.rotation_power_apply,Fin.val_zero,Nat.cast_zero,
      Fin.cast_val_eq_self,zero_add] using hhead
  obtain ⟨w,hw⟩ := exists_scan_trace hn e heb hei
  have hL := (hw.rotations_le_deadline hn heb hei).trans
    (scan_deadline_head_reserve hn e hei h hem heh)
  have hX := hw.exchange_count hn heb hei
  have hIe : inversions e=inversions d := left_run_inversions hn d hd.1 hi r.val
  rw [hIe] at hX
  let v := paidWord (c : Fin n) (u++w)
  have hv : p*eval v=1 := by
    apply sorting_word_of_zero hn p (c : Fin n) d hl
    intro i
    rw [run_append]
    exact hw.run_zero i
  refine ⟨v,hv,?_⟩
  have hlen : v.length=r.val+w.count .l+w.count .x+
      ((c : Fin n)-((u++w).count .l : Fin n)).val := by
    simp only [v,paidWord,List.length_append,List.length_replicate,u,length_eq_counts]
    omega
  have hp := ((c : Fin n)-((u++w).count .l : Fin n)).isLt
  have hprod : 1 ≤ h*(n-1) := by
    have hh : 1 ≤ h := by omega
    have hn1 : 1 ≤ n-1 := by omega
    nlinarith
  have hLc : (w.count .l : ℤ) ≤ (h : ℤ)*((n : ℤ)-1)-1 := by
    have hnat : w.count .l+1 ≤ h*(n-1) := by omega
    have hnat' : (w.count .l : ℤ)+1 ≤ (h : ℤ)*((n-1 : ℕ) : ℤ) := by exact_mod_cast hnat
    have hn' : ((n-1 : ℕ) : ℤ)=(n : ℤ)-1 := by omega
    rw [hn'] at hnat'
    omega
  rw [hlen,hX]
  push_cast
  nlinarith
