-- Prove2me | solution 1 for LX.AffineScan.raise_coordinate_inversions
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:04:46.11272+00:00
-- url     : https://prove2.me/submissions/460befe6-0963-40d1-88dd-aa05ea120f80

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
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_PhaseMinimumRescue
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_Core_AffineLift_crossing_antisymm
import Theorems.Thm_LX_Core_RotationWords_twice_inversion_count

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
/-!
A balanced phase lift of an actual permutation, with subset majorization.
We minimize the nonnegative integer sum of squared displacements over all
balanced lifts and phases. Phase shifts yield majorization directly, without
assuming an affine inversion formula or a pre-existing bounded lift.
-/
namespace LX.Core.AffineLift
open scoped BigOperators













theorem shift_balanced {n : ℕ} (d : Fin n → ℤ) (s : Finset (Fin n))
    (hd : ∑ i, d i = 0) : ∑ i, phaseShift d s i = 0 := by
  simp [phaseShift, Finset.sum_sub_distrib, Finset.sum_add_distrib, hd,
    Finset.sum_ite_mem, mul_comm]

theorem shift_lift {n : ℕ} {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (s : Finset (Fin n)) :
    IsLift p (c + s.card) (phaseShift d s) := by
  refine ⟨shift_balanced d s hd.1, ?_⟩
  intro i
  have h := (hd.2 i).add_right (s.card : ℤ)
  simp only [phaseShift]
  by_cases hi : i ∈ s
  · simp only [ite_eq_left hi]
    rw [← add_sub_assoc, Int.sub_modulus_modEq_iff]
    simpa only [add_assoc] using h
  · simp only [ite_eq_right hi, sub_zero]
    simpa only [add_assoc] using h












end LX.Core.AffineLift

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
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Changing a phase alters each signed crossing by the difference of the
selected endpoint indicators. -/
theorem phase_shift_crossing (d : Fin n → ℤ) (S : Finset (Fin n)) (i j : Fin n) :
    crossing (phaseShift d S) i j=crossing d i j-
      (if i ∈ S then (1 : ℤ) else 0)+(if j ∈ S then (1 : ℤ) else 0) := by
  have he : crossingNumerator (phaseShift d S) i j=crossingNumerator d i j+
      ((if i ∈ S then (1 : ℤ) else 0)-(if j ∈ S then (1 : ℤ) else 0))*(n : ℤ) := by
    unfold crossingNumerator phaseShift
    split_ifs <;> ring
  rw [crossing,he,Int.add_mul_ediv_right _ _ (show (n : ℤ) ≠ 0 by exact_mod_cast NeZero.ne n)]
  unfold crossing
  ring









end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]





theorem raise_minimum_lift {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (a : Fin n) :
    IsLift p (c+(n : ℤ)-1) (raiseMinimum d a) := by
  have hh := shift_lift hd (Finset.univ.erase a)
  have hn : 1 ≤ n := NeZero.pos n
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,Fintype.card_fin,
    Nat.cast_sub hn,Nat.cast_one,raiseMinimum,add_sub_assoc] using hh


end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem raise_coordinate_crossing (d : Fin n → ℤ) (a i j : Fin n) :
    crossing (raiseMinimum d a) i j=crossing d i j+
      (if i=a then (1 : ℤ) else 0)-(if j=a then (1 : ℤ) else 0) := by
  rw [raiseMinimum,phase_shift_crossing]
  simp only [Finset.mem_erase,Finset.mem_univ,and_true]
  by_cases hi : i=a <;> by_cases hj : j=a <;> simp [hi,hj] <;> ring

 theorem _root_.LX.UploadHelpers.SingleRaisePrice.crossing_ge_neg_one (d : Fin n → ℤ)
    (hw : ∀ i j,d i-d j < (n : ℤ)) (i j : Fin n) : -1 ≤ crossing d i j := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have ht : crossingNumerator d i j < (2 : ℤ)*n := by
    have := hw j i
    have := (j-i).isLt
    unfold crossingNumerator
    omega
  have hq := (Int.ediv_lt_iff_lt_mul hn).mpr ht
  unfold crossing
  omega

 theorem _root_.LX.UploadHelpers.SingleRaisePrice.abs_add_one_price (x : ℤ) (hx : -1 ≤ x) :
    |x+1|-|x|=1-2*((-x).toNat : ℤ) := by
  by_cases he : x= -1
  · subst x; norm_num
  · have hx0 : 0 ≤ x := by omega
    rw [abs_of_nonneg hx0,abs_of_nonneg (by omega : 0 ≤ x+1)]
    have hz : (-x).toNat=0 := by omega
    rw [hz]; ring







end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Raising any coordinate has an exact price in terms of its backward
depth. A minimum-coordinate premise is unnecessary. -/
theorem solution {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (a : Fin n) (hw : ∀ i j,d i-d j < (n : ℤ)) :
    (inversions (raiseMinimum d a) : ℤ)-inversions d=
      (n : ℤ)-1-2*(backwardDepth d a : ℤ) := by
  let Δ : Fin n → ℤ := fun j => if j=a then 0 else |crossing d a j+1|-|crossing d a j|
  have hpoint (i j : Fin n) :
      |crossing (raiseMinimum d a) i j|-|crossing d i j|=
        (if i=a then Δ j else 0)+(if j=a then Δ i else 0) := by
    rw [raise_coordinate_crossing]
    by_cases hi : i=a
    · subst i
      by_cases hj : j=a
      · subst j; simp [Δ]
      · simp [Δ,hj]
    · by_cases hj : j=a
      · subst j
        simp only [ite_eq_right hi,ite_true,zero_add,add_zero,Δ]
        rw [crossing_antisymm hd i a]
        rw [show -crossing d a i-1= -(crossing d a i+1) by ring,abs_neg,abs_neg]
      · simp [hi,hj]
  have hterm (j : Fin n) : Δ j=
      1-(if j=a then (1 : ℤ) else 0)-2*((-crossing d a j).toNat : ℤ) := by
    by_cases hj : j=a
    · subst j; simp [Δ]
    · simp only [Δ,ite_eq_right hj,sub_zero]
      exact _root_.LX.UploadHelpers.SingleRaisePrice.abs_add_one_price _ (_root_.LX.UploadHelpers.SingleRaisePrice.crossing_ge_neg_one d hw a j)
  have hsumΔ : (∑ j : Fin n,Δ j)=(n : ℤ)-1-2*(backwardDepth d a : ℤ) := by
    simp only [hterm,Finset.sum_sub_distrib,← Finset.mul_sum,backwardDepth,Nat.cast_sum]
    simp
  have hs : (∑ i : Fin n,∑ j : Fin n,
      (|crossing (raiseMinimum d a) i j|-|crossing d i j|))=2*(∑ j : Fin n,Δ j) := by
    simp only [hpoint,Finset.sum_add_distrib]
    have h1 : (∑ i : Fin n,∑ j : Fin n,if i=a then Δ j else 0)=∑ j : Fin n,Δ j := by simp
    have h2 : (∑ i : Fin n,∑ j : Fin n,if j=a then Δ i else 0)=∑ j : Fin n,Δ j := by simp
    rw [h1,h2]; ring
  have hold : 2*(inversions d : ℤ)=∑ i : Fin n,∑ j : Fin n,|crossing d i j| := by
    change 2*(LX.Core.LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=_
    have hh := congrArg (fun k : ℕ => (k : ℤ)) (LX.Core.RotationWords.twice_inversion_count hd)
    simpa only [inversions,targets,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum,Int.natCast_natAbs] using hh
  have hnew : 2*(inversions (raiseMinimum d a) : ℤ)=
      ∑ i : Fin n,∑ j : Fin n,|crossing (raiseMinimum d a) i j| := by
    change 2*(LX.Core.LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+raiseMinimum d a i) : ℤ)=_
    have hh := congrArg (fun k : ℕ => (k : ℤ))
      (LX.Core.RotationWords.twice_inversion_count (raise_minimum_lift hd a))
    simpa only [inversions,targets,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum,Int.natCast_natAbs] using hh
  simp only [Finset.sum_sub_distrib] at hs
  rw [← hold,← hnew,hsumΔ] at hs
  omega
