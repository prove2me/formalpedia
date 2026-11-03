-- Prove2me | solution 1 for LX.AnchoredPhases.majorized_capacity_reflection
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:17:07.003618+00:00
-- url     : https://prove2.me/submissions/f2414e06-3608-4994-8baa-90c3b2448211

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
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Theorems.Thm_LX_Core_AffineLift_short_coordinates
import Theorems.Thm_LX_Core_FiniteCuts_inherited_capacity_equality_reflection

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCoordinates
end LX.Core.FiniteCoordinates
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
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.WordReflection
end LX.Core.WordReflection
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
/-! Recenter a phase lift at an arbitrary port. The local target is chosen so
that paid entry and exit rotations recover the original visible permutation. -/
namespace LX.Core.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem local_target_inverse (p : State n) (c r i : Fin n) :
    (localTarget p c r).symm i=p.symm (i+r)+(c-r) := by
  change (localTarget p c r)⁻¹ i= _
  simp only [localTarget, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply,
    AffineLift.rotation_power_apply, Fin.cast_val_eq_self]
  rfl








end LX.Core.RotationWords

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



@[simp] theorem inversion_indicator_self (p : State n) (i : Fin n) :
    inversionIndicator p i i=0 := by simp [inversionIndicator]















end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}



@[simp] theorem mem_fixedPositions (p : State n) (i : Fin n) :
    i ∈ fixedPositions p ↔ p i=i := by simp [fixedPositions]









end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]











/-- Strict shortness gives the strip used in Lemma 12, without majorization. -/
theorem strict_short_strip (d : Fin n → ℤ)
    (hshort : ∀ i, 2*|d i| < (n : ℤ)) (i : Fin n) :
    0 ≤ d i+((n-1)/2 : ℕ) ∧ d i+((n-1)/2 : ℕ) < (n : ℤ) := by
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h := hshort i
  have hp := le_abs_self (d i)
  have hm := neg_abs_le (d i)
  omega



end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]







/-- Strict shortness supplies the symmetric integer bound, including the tighter even case. -/
theorem strict_short_upper (d : Fin n → ℤ) (hshort : ∀ i, 2*|d i| < (n : ℤ)) :
    ∀ i, d i ≤ (((n-1)/2 : ℕ) : ℤ) := by
  intro i
  have hh := hshort i
  have hu := le_abs_self (d i)
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  omega




end LX.Core.FiniteCuts

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]













@[simp] theorem mem_endpoints (events : List (Event n)) (i : Fin n) :
    i ∈ endpoints events ↔ ∃ e ∈ events, i=e.1 ∨ i=e.2 := by
  simp [endpoints]






end LX.Core.ZeroGap

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]



/-- Arithmetic conversion between the strip parameter and the research budget Q-m. -/
theorem strict_band_budget_identity :
    ((((n-1)/2 : ℕ) : ℤ)*((n : ℤ)-((n-1)/2 : ℕ)-1))=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ) := by
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hparity : n=2*(n/2) ∨ n=2*(n/2)+1 := by omega
  rcases hparity with he | ho
  · have hh : (((n-1)/2 : ℕ) : ℤ)=((n/2 : ℕ) : ℤ)-1 := by omega
    have hnint : (n : ℤ)=2*((n/2 : ℕ) : ℤ) := by exact_mod_cast he
    rw [hh]
    nlinarith
  · have hh : (n-1)/2=n/2 := by omega
    rw [hh]
    ring

/-- Equality in the actual strict-band budget forces circular reflection after
an internally chosen cut, provided the completion inherits both extremes. -/
theorem strict_capacity_equality_reflection
    {p : State n} {original d : Fin n → ℤ}
    (horiginal : ∑ i, original i=0) (hmaj : AffineLift.Majorized original)
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ))
    (hinheritNeg : ∀ i, d i= -(((n-1)/2 : ℕ) : ℤ) → original i= -(((n-1)/2 : ℕ) : ℤ))
    (hinheritPos : ∀ i, d i= (((n-1)/2 : ℕ) : ℤ) → original i= (((n-1)/2 : ℕ) : ℤ))
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)) :
    ∃ r : Fin n, ∀ i : Fin n,
      (localTarget p 0 r).symm i= -i-((((n-1)/2 : ℕ) : ℤ) : Fin n) := by
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  apply inherited_capacity_equality_reflection horiginal hmaj hd (((n-1)/2 : ℕ) : ℤ)
    (by omega) (strict_short_strip d hshort) (strict_short_upper d hshort)
    hinheritNeg hinheritPos
  rw [strict_band_budget_identity]
  exact heq



end LX.Core.FiniteCuts

end

section
/-! In a window no wider than half the circle, a strictly short lift has the
canonical finite displacements. The no-winding premise is derived here. -/
namespace LX.Core.FiniteWindow
variable {n b : ℕ} [NeZero n]


omit [NeZero n] in
theorem majorized_short {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (i : Fin n) :
    2*|d i| < (n : ℤ) := by
  have h := AffineLift.short_coordinates hd.1 hm i
  by_cases hi : 0 ≤ d i
  · rw [abs_of_nonneg hi]; omega
  · rw [abs_of_neg (by omega : d i < 0)]; omega

open scoped BigOperators

end LX.Core.FiniteWindow

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

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift LX.Core.RotationWords
variable {n : ℕ} [NeZero n]

/-- The LX.Core equality classification applies to the actual LX phase after a
proved output shift. Its conclusion is pulled back to the original input. -/
theorem solution {p : State n} {c₀ : ℤ} {d : Fin n → ℤ}
    (hsource : IsLift p.symm c₀ d) (hm : Majorized d)
    (heq : (inversions d : ℤ)=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)) :
    ∃ r : Fin n,∀ i,p i=r-i := by
  let c : Fin n := (c₀ : Fin n)
  let q : State n := (p.trans (Equiv.addRight c)).symm
  have hq (i : Fin n) : q.symm i=p i+c := rfl
  have hd : IsLift q 0 d := by
    refine ⟨hsource.1,?_⟩
    intro i
    apply (LX.Core.LiftedModel.cast_eq_iff_modEq _ _).mp
    simp only [Int.cast_add,Int.cast_natCast,Fin.cast_val_eq_self,Int.cast_zero,add_zero,hq]
    exact lift_residue hsource i
  have hshort := LX.Core.FiniteWindow.majorized_short hd hm
  have hx : (LX.Core.LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ) := heq
  obtain ⟨t,ht⟩ := LX.Core.FiniteCuts.strict_capacity_equality_reflection hd.1 hm hd hshort
    (fun _ hh => hh) (fun _ hh => hh) hx
  refine ⟨t+t-(((n-1)/2 : ℕ) : Fin n)-c,?_⟩
  intro i
  have hh := ht (i-t)
  rw [local_target_inverse,hq,sub_add_cancel] at hh
  simp only [zero_sub,Int.cast_natCast] at hh
  linear_combination hh
