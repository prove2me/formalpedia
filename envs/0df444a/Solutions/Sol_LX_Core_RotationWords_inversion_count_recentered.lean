-- Prove2me | solution 1 for LX.Core.RotationWords.inversion_count_recentered
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:35:28.129764+00:00
-- url     : https://prove2.me/submissions/304708e5-6cf1-4918-a982-2fbd417409d7

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_RecenteredLift
import Theorems.Thm_LX_Core_RotationWords_recentered_lift
import Theorems.Thm_LX_Core_RotationWords_twice_inversion_count

namespace Int
end Int
namespace LX
end LX
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

namespace LX.Core.RotationWords
end LX.Core.RotationWords
open LX
open LX.Core
open LX.Core.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution {p : State n} {d : Fin n → ℤ} (c r : Fin n)
    (hd : AffineLift.IsLift p (c : ℤ) d) :
    LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+localDisplacement d r i)=
      LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) := by
  have hlocal := twice_inversion_count (recentered_lift c r hd)
  have horiginal := twice_inversion_count hd
  have hsum : (∑ i : Fin n, ∑ j : Fin n,
      (AffineLift.crossing (localDisplacement d r) i j).natAbs)=
      ∑ i : Fin n, ∑ j : Fin n, (AffineLift.crossing d i j).natAbs := by
    simp_rw [crossing_recentered]
    have hinner (i : Fin n) : (∑ j : Fin n,
        (AffineLift.crossing d ((L n^r.val) i) ((L n^r.val) j)).natAbs)=
        ∑ j : Fin n, (AffineLift.crossing d ((L n^r.val) i) j).natAbs :=
      Equiv.sum_comp (L n^r.val) (fun j => (AffineLift.crossing d ((L n^r.val) i) j).natAbs)
    simp_rw [hinner]
    exact Equiv.sum_comp (L n^r.val) (fun i => ∑ j : Fin n, (AffineLift.crossing d i j).natAbs)
  rw [hsum] at hlocal
  omega
