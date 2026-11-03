-- Prove2me | solution 1 for LX.AffineScan.zero_of_rank_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:32:21.883384+00:00
-- url     : https://prove2.me/submissions/2cf24bc8-d7de-41da-a92d-b11a0c00b7ac

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
/-! Integer division is determined by lower and upper quotient bounds.
This arithmetic identity is used in the finite-coordinate estimates. -/
namespace LX.Core.PeriodicBuffer

theorem quotient_eq_of_bounds {M x q : ℤ} (hM : 0 < M)
    (hlo : q*M ≤ x) (hhi : x < (q+1)*M) : x/M = q := by
  have ha := (Int.le_ediv_iff_mul_le hM).mpr hlo
  have hb := (Int.ediv_lt_iff_lt_mul hM).mpr hhi
  omega


end LX.Core.PeriodicBuffer

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




































theorem threshold_rank_zero_diagonal (r : Fin n) :
    thresholdRank (fun _ : Fin n => 0) r ((r : ℤ)+1)=0 := by
  have hnpos : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  unfold thresholdRank
  apply Finset.sum_eq_zero
  intro i _
  by_cases hir : i ≤ r
  · have hq : ((i : ℤ)-((r : ℤ)+1))/(n : ℤ)= -1 := by
      apply LX.Core.PeriodicBuffer.quotient_eq_of_bounds hnpos <;> have := i.isLt <;>
        have := r.isLt <;> have : i.val ≤ r.val := hir <;> omega
    simp [targets,hir,hq]
  · have hq : ((i : ℤ)-((r : ℤ)+1))/(n : ℤ)=0 := by
      apply LX.Core.PeriodicBuffer.quotient_eq_of_bounds hnpos <;> have := i.isLt <;>
        have := r.isLt <;> have : ¬i.val ≤ r.val := hir <;> omega
    simp [targets,hir,hq]






end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Dominance by the sorted board forces a balanced board to be zero.
This connects the rank order to literal completion, not just a statistic. -/
theorem solution (d : Fin n → ℤ) (hb : ∑ i,d i=0)
    (hle : RankLE d (fun _ => 0)) : ∀ i,d i=0 := by
  have hnonpos (i : Fin n) : d i ≤ 0 := by
    have hr := hle i ((i : ℤ)+1)
    rw [threshold_rank_zero_diagonal] at hr
    have ht := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => max ((targets d j-((i : ℤ)+1))/(n : ℤ)+(if j ≤ i then 1 else 0)) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ i)
    change _ ≤ thresholdRank d i ((i : ℤ)+1) at ht
    simp only [le_refl,ite_true,targets] at ht
    have he : (i : ℤ)+d i-((i : ℤ)+1)=d i-1 := by ring
    rw [he] at ht
    by_contra hnot
    have hq := Int.ediv_nonneg (show 0 ≤ d i-1 by omega) (show (0 : ℤ) ≤ n by positivity)
    omega
  exact fun i => (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hnonpos j)).mp hb i (Finset.mem_univ i)
