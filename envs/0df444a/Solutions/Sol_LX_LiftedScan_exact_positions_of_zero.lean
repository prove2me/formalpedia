-- Prove2me | solution 1 for LX.LiftedScan.exact_positions_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:33:34.873202+00:00
-- url     : https://prove2.me/submissions/930a24da-1cdd-4347-9bc4-7ccf8329d690

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedScanBridge
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
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

theorem remainder_step (hn : 2 ≤ n) (F : Fin n → ℤ)
    (s : LX.Core.LiftedModel.Configuration n) (a : Letter) :
    remainder F (LX.Core.LiftedModel.step a.toCore s)=AffineScan.step a (remainder F s) := by
  funext i
  have h0 : s.physical.tokens s.physical.cursor=visible s 0 := by
    simp [visible,LX.Core.PhysicalModel.visible_apply]
  have h1 : s.physical.tokens (s.physical.cursor+1)=visible s 1 := by
    simp [visible,LX.Core.PhysicalModel.visible_apply,add_comm]
  have h01 : (0 : Fin n) ≠ 1 := by
    intro he
    have hh := Fin.one_eq_zero_iff.mp he.symm
    omega
  cases a with
  | l =>
    rw [remainder,visible_step]
    simp only [Letter.toCore,eval, List.map_cons,List.map_nil,LX.Core.eval_cons,LX.Core.eval_nil,
      mul_one,LX.Core.Letter.eval,Equiv.Perm.mul_apply,LX.Core.L,LX.Core.LiftedModel.step,
      AffineScan.step,AffineScan.rotate,remainder]
  | x =>
    rw [remainder,visible_step]
    simp only [Letter.toCore,eval,List.map_cons,List.map_nil,LX.Core.eval_cons,LX.Core.eval_nil,
      mul_one,LX.Core.Letter.eval,Equiv.Perm.mul_apply,LX.Core.X,LX.Core.LiftedModel.step,
      AffineScan.step,AffineScan.exchange,remainder,h0,h1]
    by_cases hi0 : i=0
    · subst i
      simp [h01,Ne.symm h01,(visible s).injective.eq_iff]
      ring
    · by_cases hi1 : i=1
      · subst i
        simp [h01,Ne.symm h01,(visible s).injective.eq_iff]
        ring
      · simp [Equiv.swap_apply_of_ne_of_ne hi0 hi1,(visible s).injective.eq_iff,hi0,hi1]

theorem remainder_run (hn : 2 ≤ n) (F : Fin n → ℤ) (w : List Letter)
    (s : LX.Core.LiftedModel.Configuration n) :
    remainder F (LX.Core.LiftedModel.run (w.map Letter.toCore) s)=AffineScan.run w (remainder F s) := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons,LX.Core.LiftedModel.run,AffineScan.run]
    rw [ih,remainder_step hn]

theorem remainder_initial (d : Fin n → ℤ) :
    remainder (AffineScan.targets d) (LX.Core.LiftedModel.initial (n := n))=d := by
  funext i
  simp [remainder,visible,LX.Core.LiftedModel.initial,LX.Core.PhysicalModel.visible_initial,
    AffineScan.targets]





















end LX.LiftedScan

end

namespace LX.LiftedScan
end LX.LiftedScan
open LX
open LX.LiftedScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- A zero residual board determines every named token's exact integer
endpoint. Finite evaluation alone would not imply this statement. -/
theorem solution (hn : 2 ≤ n) (d : Fin n → ℤ) (w : List Letter)
    (hz : ∀ i,AffineScan.run w d i=0) :
    ∀ i,(LX.Core.LiftedModel.run (w.map Letter.toCore) LX.Core.LiftedModel.initial).position i=
      (i : ℤ)+d i := by
  have hr := remainder_run hn (AffineScan.targets d) w LX.Core.LiftedModel.initial
  rw [remainder_initial] at hr
  intro i
  let s : LX.Core.LiftedModel.Configuration n := LX.Core.LiftedModel.run (w.map Letter.toCore) LX.Core.LiftedModel.initial
  have hh := congrFun hr ((visible s).symm i)
  rw [hz] at hh
  change AffineScan.targets d (visible s ((visible s).symm i))-
    s.position (visible s ((visible s).symm i))=0 at hh
  rw [Equiv.apply_symm_apply] at hh
  change (i : ℤ)+d i-s.position i=0 at hh
  change s.position i=(i : ℤ)+d i
  omega
