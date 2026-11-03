-- Prove2me | solution 1 for LX.Core.FiniteCuts.shifted_fixed_iff_negative_extreme
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:37:32.259915+00:00
-- url     : https://prove2.me/submissions/335d1eb8-44cf-4f03-be41-8c944c922833

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
import Definitions.Def_LX_ClockwiseLiftCount
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_StrictBandInversionCapacity

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
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteGaps
end LX.Core.FiniteGaps
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
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

theorem lift_residue {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i : Fin n) :
    i + (d i : Fin n) = p.symm i + (c : Fin n) := by
  have h := cast_eq_of_modEq (hd.2 i)
  simpa using h


















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
/-! Literal LX.Core execution with an integer cursor and integer positions of every
named token. The position log records winding, including exchanges at the seam.
Its residues are proved to agree with the finite physical permutation. -/
namespace LX.Core.LiftedModel
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing



variable {n : ℕ} [NeZero n]
































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
/-! Extend a finite permutation to a contiguous window of a larger ambient
permutation, fixing every external label. No ambient size is changed. -/
namespace LX.Core.FiniteWindow
variable {n b : ℕ}



















@[simp] theorem permutation_embed (W : Window n b) (p : State b) (i : Fin b) :
    permutation W p (embed W i)=embed W (p i) := p.extendDomain_apply_image (windowEquiv W) i



@[simp] theorem permutation_symm (W : Window n b) (p : State b) :
    (permutation W p).symm=permutation W p.symm := rfl







end LX.Core.FiniteWindow

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem mem_descendingPositions (p : State n) (i : Fin n) :
    i ∈ descendingPositions p ↔ (p i).val < i.val := by
  simp [descendingPositions]









@[simp] theorem descending_positions_one : descendingPositions (1 : State n) = ∅ := by
  ext i
  simp




















end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}



theorem clockwise_representative_bounds (p : State n) (i : Fin n) :
    (i : ℤ) ≤ clockwiseRepresentative p i ∧ clockwiseRepresentative p i < (i : ℤ)+n := by
  have hi := i.isLt
  have hp := (p i).isLt
  unfold clockwiseRepresentative
  split_ifs <;> omega

theorem clockwise_representative_modEq (p : State n) (i : Fin n) :
    Int.ModEq (n : ℤ) (clockwiseRepresentative p i) (p i : ℤ) := by
  unfold clockwiseRepresentative
  split_ifs <;> simp [Int.ModEq]

theorem clockwise_representative_unique (p : State n) (g : Fin n → ℤ)
    (hb : ∀ i : Fin n, (i : ℤ) ≤ g i ∧ g i < (i : ℤ)+n)
    (hm : ∀ i : Fin n, Int.ModEq (n : ℤ) (g i) (p i : ℤ)) :
    g = clockwiseRepresentative p := by
  funext i
  have h := ((hm i).trans (clockwise_representative_modEq p i).symm).sub_right (i : ℤ)
  have hg := hb i
  have hc := clockwise_representative_bounds p i
  unfold Int.ModEq at h
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at h
  omega






end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem inversion_indicator_self (p : State n) (i : Fin n) :
    inversionIndicator p i i=0 := by simp [inversionIndicator]















end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem shifted_lift_permutation_modEq {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (h : ℤ) (i : Fin n) :
    Int.ModEq (n : ℤ) ((i : ℤ)+d i+h) (shiftedLiftPermutation p c h i : ℤ) := by
  apply (LiftedModel.cast_eq_iff_modEq _ _).mp
  have hi := AffineLift.lift_residue hd i
  simp only [Int.cast_add, Int.cast_natCast, Fin.cast_val_eq_self]
  change i+(d i : Fin n)+(h : Fin n)=p.symm i+((c+h : ℤ) : Fin n)
  rw [Int.cast_add, hi, add_assoc]











end LX.Core.FiniteCuts

end

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- A fixed endpoint residue is exactly a negative extreme coordinate. -/
theorem solution {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (h : ℤ)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ)) (i : Fin n) :
    shiftedLiftPermutation p c h i=i ↔ d i= -h := by
  let q := shiftedLiftPermutation p c h
  have heq : (fun j : Fin n => (j : ℤ)+d j+h)=clockwiseRepresentative q :=
    clockwise_representative_unique q _
      (fun j => by have := hband j; omega) (shifted_lift_permutation_modEq hd h)
  constructor
  · intro hfix
    have hi := congrFun heq i
    change q i=i at hfix
    simp only [clockwiseRepresentative, hfix, lt_self_iff_false, ite_false, add_zero] at hi
    omega
  · intro hi
    have hm := shifted_lift_permutation_modEq hd h i
    have hz : (i : ℤ)+d i+h=(i : ℤ) := by omega
    rw [hz] at hm
    have hc := (LiftedModel.cast_eq_iff_modEq _ _).mpr hm
    simpa only [Int.cast_natCast, Fin.cast_val_eq_self] using hc.symm
