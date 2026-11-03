-- Prove2me | solution 1 for LX.AffineScan.exists_exact_word_board
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:45:42.233034+00:00
-- url     : https://prove2.me/submissions/a4df1335-a4d1-4b11-b342-d192d57d0a4a

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedScanBridge
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_Core_PhysicalModel_visible_step
import Theorems.Thm_LX_DirectedTokenLower_word_endpoint_lift

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
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace LX.ForwardCarrier
end LX.ForwardCarrier
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
/-! Literal LX.Core execution with an integer cursor and integer positions of every
named token. The position log records winding, including exchanges at the seam.
Its residues are proved to agree with the finite physical permutation. -/
namespace LX.Core.LiftedModel
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing



variable {n : ℕ} [NeZero n]























theorem cursor_run (w : List Letter) (s : Configuration n) :
    (run w s).cursor = s.cursor + (w.map increment).sum := by
  induction w generalizing s with
  | nil => simp [run]
  | cons a w ih => simp [run, ih, step, add_assoc]













end LX.Core.LiftedModel

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
namespace LX.DirectedTokenLower
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]











theorem cursor_eq_left_count (w : List Letter) :
    (run (w.map Letter.toCore) (initial (n := n))).cursor=(w.count .l : ℤ) := by
  rw [cursor_run]
  simp only [initial,zero_add,List.map_map]
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [Letter.toCore,increment,ih,add_comm]









end LX.DirectedTokenLower

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

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- The exact physical endpoint of an arbitrary word is a board on which
that same word terminates at zero. Winding is retained. -/
theorem solution (hn : 2 ≤ n) (w : List Letter) :
    ∃ d : Fin n → ℤ,IsLift (eval w) (w.count .l : ℤ) d ∧ ∀ i,run w d i=0 := by
  let s := LX.Core.LiftedModel.run (w.map Letter.toCore) (LX.Core.LiftedModel.initial (n := n))
  let d : Fin n → ℤ := fun i => s.position i-(i : ℤ)
  have hd : IsLift (eval w) (w.count .l : ℤ) d := by
    have hh := DirectedTokenLower.word_endpoint_lift hn w
    rw [DirectedTokenLower.cursor_eq_left_count] at hh
    exact hh
  refine ⟨d,hd,?_⟩
  have he : targets d=s.position := by funext i; simp [targets,d]
  have hr := LiftedScan.remainder_run hn (targets d) w LX.Core.LiftedModel.initial
  rw [LiftedScan.remainder_initial] at hr
  intro i
  rw [← hr]
  change targets d (LiftedScan.visible s i)-s.position (LiftedScan.visible s i)=0
  rw [he,sub_self]
