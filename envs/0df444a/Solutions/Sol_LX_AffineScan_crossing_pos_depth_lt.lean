-- Prove2me | solution 1 for LX.AffineScan.crossing_pos_depth_lt
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:56:00.901402+00:00
-- url     : https://prove2.me/submissions/5d78701f-1c43-4967-9ddd-2597f5ce5b5d

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
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_backward_depth_gt_head

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
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
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

theorem recentered_backward_depth (d : Fin n → ℤ) (r i : Fin n) :
    backwardDepth (LX.Core.RotationWords.localDisplacement d r) i =
      backwardDepth d ((LX.Core.L n ^ r.val) i) := by
  unfold backwardDepth
  simp_rw [LX.Core.RotationWords.crossing_recentered]
  exact Equiv.sum_comp (LX.Core.L n ^ r.val)
    (fun j => (-LX.Core.AffineLift.crossing d ((LX.Core.L n ^ r.val) i) j).toNat)












end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- An outgoing inversion always ends at a token of strictly larger backward depth. -/
theorem solution (d : Fin n → ℤ) (a j : Fin n)
    (h : 0 < LX.Core.AffineLift.crossing d a j) : backwardDepth d a < backwardDepth d j := by
  let r := LX.Core.L n ^ a.val
  let b : Fin n := r.symm j
  let e := LX.Core.RotationWords.localDisplacement d a
  have hr0 : r 0=a := by simp [r,LX.Core.AffineLift.rotation_power_apply]
  have hrb : r b=j := r.apply_symm_apply j
  have hc : LX.Core.AffineLift.crossing e 0 b=LX.Core.AffineLift.crossing d a j := by
    have hh := LX.Core.RotationWords.crossing_recentered d a 0 b
    change LX.Core.AffineLift.crossing e 0 b=LX.Core.AffineLift.crossing d (r 0) (r b) at hh
    simpa only [hr0,hrb] using hh
  have htarget : targets e b < targets e 0 := by
    have hh : 0 < LX.Core.AffineLift.crossing e 0 b := by omega
    have hnum : LX.Core.AffineLift.crossingNumerator e 0 b=targets e b-targets e 0 := by
      simp [LX.Core.AffineLift.crossingNumerator,targets]
    simp only [LX.Core.AffineLift.crossing,hnum] at hh
    by_contra hnot
    have hq := Int.ediv_nonneg (by omega : 0 ≤ targets e b-targets e 0)
      (show (0 : ℤ) ≤ n by positivity)
    omega
  have hlt := backward_depth_gt_head e b htarget
  have h0 := recentered_backward_depth d a 0
  have hb := recentered_backward_depth d a b
  change backwardDepth e 0=backwardDepth d (r 0) at h0
  change backwardDepth e b=backwardDepth d (r b) at hb
  rwa [h0,hb,hr0,hrb] at hlt
