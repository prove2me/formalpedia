-- Prove2me | solution 1 for LX.AffineScan.rotate_threshold_rank
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:32:27.293249+00:00
-- url     : https://prove2.me/submissions/1ceb1a6d-967e-4abb-a84a-81549263f2b1

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
import Definitions.Def_LX_AffineScan
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
/-! Compatibility aliases for core if-then-else lemmas renamed after Lean 4.33.1.
The source proof bodies use the newer names; these aliases preserve their types.
-/
namespace LX
universe u

theorem ite_eq_left {α : Sort u} {p : Prop} {inst : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h

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

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Rotation transports the cut and threshold together. The correction
at the seam is necessary because the targets are integer lifts. -/
theorem solution (hn : 2 ≤ n) (d : Fin n → ℤ) (r : Fin n) (v : ℤ) :
    thresholdRank (rotate d) r v=
      thresholdRank d (finRotate n r)
        (v+1-(if r.val=n-1 then (1 : ℤ) else 0)*n) := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  let turn (i : Fin n) : ℤ := if i.val=n-1 then 1 else 0
  have hval (i : Fin n) : (finRotate n i).val=if i.val=n-1 then 0 else i.val+1 := by
    rw [finRotate_apply,Fin.val_add,hv1]
    by_cases hi : i.val=n-1
    · rw [ite_eq_left hi,show i.val+1=n by omega,Nat.mod_self]
    · rw [ite_eq_right hi,Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  have hvali (i : Fin n) : (finRotate n i : ℤ)=(i : ℤ)+1-turn i*n := by
    rw [hval]
    dsimp only [turn]
    split_ifs <;> push_cast <;> omega
  have htarget (i : Fin n) : targets (rotate d) i=targets d (finRotate n i)-1+turn i*n := by
    unfold targets rotate
    rw [hvali]
    ring
  have hleft (i : Fin n) : (targets (rotate d) i-v)/(n : ℤ)=
      (targets d (finRotate n i)-(v+1))/(n : ℤ)+turn i := by
    rw [htarget]
    have he : targets d (finRotate n i)-1+turn i*n-v=
        (targets d (finRotate n i)-(v+1))+turn i*n := by ring
    rw [he,Int.add_mul_ediv_right _ _ hnz]
  have hright (i : Fin n) :
      (targets d (finRotate n i)-(v+1-turn r*n))/(n : ℤ)=
        (targets d (finRotate n i)-(v+1))/(n : ℤ)+turn r := by
    have he : targets d (finRotate n i)-(v+1-turn r*n)=
        (targets d (finRotate n i)-(v+1))+turn r*n := by ring
    rw [he,Int.add_mul_ediv_right _ _ hnz]
  have hcut (i : Fin n) :
      turn i+(if i ≤ r then (1 : ℤ) else 0)=
        turn r+(if finRotate n i ≤ finRotate n r then (1 : ℤ) else 0) := by
    dsimp only [turn]
    simp only [Fin.le_def,hval]
    split_ifs <;> have := i.isLt <;> have := r.isLt <;> omega
  change thresholdRank (rotate d) r v=thresholdRank d (finRotate n r) (v+1-turn r*n)
  unfold thresholdRank
  rw [← Equiv.sum_comp (finRotate n) (fun i =>
    max ((targets d i-(v+1-turn r*n))/(n : ℤ)+(if i ≤ finRotate n r then 1 else 0)) 0)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hleft,hright]
  congr 1
  have := hcut i
  omega
