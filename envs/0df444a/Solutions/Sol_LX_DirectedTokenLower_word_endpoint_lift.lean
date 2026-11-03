-- Prove2me | solution 1 for LX.DirectedTokenLower.word_endpoint_lift
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:43:25.54974+00:00
-- url     : https://prove2.me/submissions/8c3b61f4-1191-415d-ab87-a360572d8e19

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
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_Core_LiftedModel_step_aligned
import Theorems.Thm_LX_Core_PhysicalModel_visible_step

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
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







theorem visible_run (w : List Letter) (s : Configuration n) :
    visible (run w s) = visible s * eval w := by
  induction w generalizing s with
  | nil => simp [run]
  | cons a w ih => rw [run, ih, visible_step, eval_cons, mul_assoc]



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











theorem position_sum_step (a : Letter) (s : Configuration n) :
    ∑ i, (step a s).position i = ∑ i, s.position i := by
  cases a <;> simp [step, Finset.sum_add_distrib, Finset.sum_sub_distrib]





theorem run_physical (w : List Letter) (s : Configuration n) :
    (run w s).physical = PhysicalModel.run w s.physical := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => exact ih (step a s)

theorem run_aligned (hn : 2 ≤ n) (w : List Letter) {s : Configuration n}
    (hs : Aligned s) : Aligned (run w s) := by
  induction w generalizing s with
  | nil => exact hs
  | cons a w ih => exact ih (step_aligned hn a hs)

theorem position_sum_run (w : List Letter) (s : Configuration n) :
    ∑ i, (run w s).position i = ∑ i, s.position i := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => exact (ih (step a s)).trans (position_sum_step a s)





theorem initial_aligned : Aligned (initial (n := n)) := by
  constructor
  · rfl
  · intro i
    simp [initial, PhysicalModel.initial]
    rfl

/-- Every literal word has a balanced exact displacement vector, even if tokens wind. -/
theorem displacement_balanced (w : List Letter) :
    ∑ i, ((run w (initial (n := n))).position i - (i : ℤ)) = 0 := by
  rw [Finset.sum_sub_distrib, position_sum_run]
  simp [initial]


theorem cast_eq_iff_modEq (a b : ℤ) :
    (a : Fin n) = (b : Fin n) ↔ Int.ModEq (n : ℤ) a b := by
  constructor
  · intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_intCast] at hh
    have hi := congrArg (fun k : ℕ => (k : ℤ)) hh
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    rw [Int.toNat_of_nonneg (Int.emod_nonneg a hn0),
      Int.toNat_of_nonneg (Int.emod_nonneg b hn0)] at hi
    exact hi
  · exact AffineLift.cast_eq_of_modEq




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

namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
open LX
open LX.DirectedTokenLower
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.LiftedModel LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Every actual LX word provides a balanced lift with its paid cursor,
not an independently selected phase. -/
theorem solution (hn : 2 ≤ n) (w : List Letter) :
    IsLift (eval (n := n) w) (run (w.map Letter.toCore) (initial (n := n))).cursor
      (fun i => (run (w.map Letter.toCore) (initial (n := n))).position i-(i : ℤ)) := by
  let s := run (w.map Letter.toCore) (initial (n := n))
  have hs : Aligned s := run_aligned hn _ initial_aligned
  have he : LX.Core.PhysicalModel.visible s.physical=eval w := by
    dsimp only [s]
    rw [run_physical,LX.Core.PhysicalModel.visible_run]
    change 1*eval w=eval w
    exact one_mul _
  refine ⟨displacement_balanced _,?_⟩
  intro i
  change Int.ModEq (n : ℤ) ((i : ℤ)+(s.position i-(i : ℤ)))
    (((eval w).symm i : ℤ)+s.cursor)
  apply (cast_eq_iff_modEq _ _).mp
  simp only [add_sub_cancel,Int.cast_add]
  rw [hs.2,hs.1]
  have hv := congrArg (fun p : State n => p ((eval w).symm i)) he
  rw [LX.Core.PhysicalModel.visible_apply,Equiv.apply_symm_apply] at hv
  have hh := congrArg s.physical.tokens.symm hv
  simpa using hh.symm
