-- Prove2me | solution 1 for LX.AffineScan.backward_depth_gt_head
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:49:41.49823+00:00
-- url     : https://prove2.me/submissions/387fd26e-9219-4e94-b3aa-bcb71e550bc6

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



theorem crossing_quotient (d : Fin n → ℤ) (i j : Fin n) :
    -LX.Core.AffineLift.crossing d i j =
      (targets d j-targets d i)/(n : ℤ) + if j < i then 1 else 0 := by
  simp only [LX.Core.AffineLift.crossing, neg_neg, LX.Core.AffineLift.crossingNumerator,
    Fin.intCast_val_sub_eq_sub_add_ite]
  by_cases hji : j < i
  · have hh : ¬ i ≤ j := not_le.mpr hji
    simp only [hh, ite_false, hji, ite_true]
    have he : (j : ℤ)-(i : ℤ)+(n : ℤ)+d j-d i = targets d j-targets d i+n := by
      unfold targets
      ring
    rw [he]
    simpa only [one_mul] using Int.add_mul_ediv_right
      (targets d j-targets d i) 1 (by exact_mod_cast NeZero.ne n)
  · have hh : i ≤ j := le_of_not_gt hji
    simp only [hh, ite_true, hji, ite_false, add_zero]
    congr 1
    unfold targets
    ring

theorem backward_depth_formula (d : Fin n → ℤ) (i : Fin n) :
    backwardDepth d i = ∑ j : Fin n,
      ((targets d j-targets d i)/(n : ℤ) + if j < i then 1 else 0).toNat := by
  simp only [backwardDepth, crossing_quotient]

theorem backward_depth_head (d : Fin n → ℤ) :
    backwardDepth d 0 = ∑ j : Fin n, ((targets d j-targets d 0)/(n : ℤ)).toNat := by
  simp [backward_depth_formula]












end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Along an inversion, the smaller target has strictly more inverted predecessors. -/
theorem solution (d : Fin n → ℤ) (j : Fin n)
    (hj : targets d j < targets d 0) : backwardDepth d 0 < backwardDepth d j := by
  rw [backward_depth_head, backward_depth_formula]
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  apply Finset.sum_lt_sum
  · intro k _
    have hq : (targets d k-targets d 0)/(n : ℤ) ≤
        (targets d k-targets d j)/(n : ℤ) :=
      Int.ediv_le_ediv (by omega) (by omega)
    split_ifs <;> omega
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    have hj0 : j ≠ 0 := by intro h; subst j; omega
    have hjpos : (0 : Fin n) < j := Fin.pos_iff_ne_zero.mpr hj0
    have hq : 0 ≤ (targets d 0-targets d j)/(n : ℤ) := Int.ediv_nonneg (by omega) (by omega)
    simp only [sub_self, Int.zero_ediv, Int.toNat_zero, hjpos, ite_true]
    omega
