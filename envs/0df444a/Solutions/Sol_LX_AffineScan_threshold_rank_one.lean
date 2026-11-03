-- Prove2me | solution 1 for LX.AffineScan.threshold_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:30:59.948483+00:00
-- url     : https://prove2.me/submissions/9b6a1ed5-db55-4f36-908c-969988c4497b

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
import Definitions.Def_LX_AffineRankOrder
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
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
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]








 theorem _root_.LX.UploadHelpers.AffineRankOrder.split_head_sum (hn : 2 ≤ n) (f : Fin n → ℤ) :
    (∑ i : Fin n,f i)=(∑ i ∈ (Finset.univ.erase (0 : Fin n)).erase 1,f i)+f 0+f 1 := by
  have h10 : (1 : Fin n) ≠ 0 := by intro h; have := Fin.one_eq_zero_iff.mp h; omega
  have h0 := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n))) f (Finset.mem_univ 0)
  have h1 := Finset.sum_erase_add (s := Finset.univ.erase (0 : Fin n)) f
    (Finset.mem_erase.mpr ⟨h10,Finset.mem_univ 1⟩)
  omega


































end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution (hn : 2 ≤ n) (d : Fin n → ℤ) (v : ℤ) :
    thresholdRank d 1 v=_root_.LX.UploadDefinitions.AffineRankOrder.rankTail d v+
      max ((targets d 0-v)/(n : ℤ)+1) 0+max ((targets d 1-v)/(n : ℤ)+1) 0 := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  rw [thresholdRank,_root_.LX.UploadHelpers.AffineRankOrder.split_head_sum hn]
  have ht : (∑ i ∈ (Finset.univ.erase (0 : Fin n)).erase 1,
      max ((targets d i-v)/(n : ℤ)+(if i ≤ 1 then 1 else 0)) 0)=_root_.LX.UploadDefinitions.AffineRankOrder.rankTail d v := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 := (Finset.mem_erase.mp hi).1
    have hi0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hnot : ¬i ≤ 1 := by
      change ¬i.val ≤ (1 : Fin n).val
      have hne0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      have hne1 : i.val ≠ 1 := fun h => hi1 (Fin.ext (by omega))
      omega
    simp [hnot]
  rw [ht]
  simp
