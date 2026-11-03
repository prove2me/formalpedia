-- Prove2me | solution 1 for LX.FinitePairReduction.position_run_partner_bound
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:43:25.306944+00:00
-- url     : https://prove2.me/submissions/edbfb950-d559-47df-aa4a-fff4445e4297

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
import Definitions.Def_LX_FinitePairReduction
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedScanBridge
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_Core_PhysicalModel_visible_step

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
namespace LX.FinitePairReduction
end LX.FinitePairReduction
namespace LX.LiftedScan
end LX.LiftedScan
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



theorem visible_apply (s : Configuration n) (i : Fin n) :
    visible s i = s.tokens (i + s.cursor) := by
  simp only [visible, Equiv.Perm.mul_apply, rotation_power_apply, Fin.cast_val_eq_self]











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
namespace LX.LiftedScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem visible_step (s : LX.Core.LiftedModel.Configuration n) (a : Letter) :
    visible (LX.Core.LiftedModel.step a.toCore s)=visible s*eval [a] := by
  change LX.Core.PhysicalModel.visible (LX.Core.PhysicalModel.step a.toCore s.physical)=_
  rw [LX.Core.PhysicalModel.visible_step]
  congr 1



























end LX.LiftedScan

end

section
namespace LX.FinitePairReduction
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]

theorem position_step_partner_bound (s : Configuration n) (a : Letter) (i : Fin n) :
    |(step a.toCore s).position i-s.position i| ≤
      (if a=.x then ((headPartners i (LiftedScan.visible s)).length : ℤ) else 0) := by
  have h0 : s.physical.tokens s.physical.cursor=LiftedScan.visible s 0 := by
    simp [LiftedScan.visible,LX.Core.PhysicalModel.visible_apply]
  have h1 : s.physical.tokens (s.physical.cursor+1)=LiftedScan.visible s 1 := by
    simp [LiftedScan.visible,LX.Core.PhysicalModel.visible_apply,add_comm]
  cases a with
  | l => simp [Letter.toCore,step]
  | x =>
    simp only [Letter.toCore,step,h0,h1,headPartners,ite_true,abs_le]
    split_ifs <;> simp only [List.length_singleton,List.length_nil,Nat.cast_one,Nat.cast_zero] <;> omega







end LX.FinitePairReduction

end

namespace LX.FinitePairReduction
end LX.FinitePairReduction
open LX
open LX.FinitePairReduction
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]

/-- Integer displacement is charged to the actual partners of this token,
including seam crossings; no winding is discarded. -/
theorem solution (w : List Letter) (s : Configuration n) (i : Fin n) :
    |(run (w.map Letter.toCore) s).position i-s.position i| ≤
      ((partners i w (LiftedScan.visible s)).length : ℤ) := by
  induction w generalizing s with
  | nil => simp [run,partners]
  | cons a w ih =>
    have ht := ih (step a.toCore s)
    have hh := position_step_partner_bound s a i
    have hlen : (partners i (a::w) (LiftedScan.visible s)).length=
        (partners i w (LiftedScan.visible (step a.toCore s))).length+
          (if a=.x then (headPartners i (LiftedScan.visible s)).length else 0) := by
      rw [LiftedScan.visible_step]
      cases a <;> simp [partners,Nat.add_comm]
    have hleni : ((partners i (a::w) (LiftedScan.visible s)).length : ℤ)=
        ((partners i w (LiftedScan.visible (step a.toCore s))).length : ℤ)+
          (if a=.x then ((headPartners i (LiftedScan.visible s)).length : ℤ) else 0) := by
      exact_mod_cast hlen
    have ha := abs_add_le
      ((run (w.map Letter.toCore) (step a.toCore s)).position i-(step a.toCore s).position i)
      ((step a.toCore s).position i-s.position i)
    have he : (run (w.map Letter.toCore) (step a.toCore s)).position i-(step a.toCore s).position i+
        ((step a.toCore s).position i-s.position i)=
        (run (w.map Letter.toCore) (step a.toCore s)).position i-s.position i := by ring
    rw [he] at ha
    change |(run (w.map Letter.toCore) (step a.toCore s)).position i-s.position i| ≤ _
    omega
