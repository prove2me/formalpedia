-- Prove2me | solution 1 for LX.FiniteDropBudget.head_merge_inversions
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:39:34.883376+00:00
-- url     : https://prove2.me/submissions/2d75daa7-b7d5-4bfd-8b64-1716c9989622

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
import Definitions.Def_LX_FiniteChainMerge
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel

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
namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
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

namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
open LX
open LX.FiniteDropBudget
open scoped BigOperators
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Erasing an ascending chain vertex increases the finite inversion count
by exactly one when all intervening positions are fixed. -/
theorem solution (p : LX.Core.State n) (b : Fin n)
    (hb : 0 < b.val) (hhead : p 0=b) (hnext : b.val < (p b).val)
    (hfix : ∀ j : Fin n,0 < j.val → j.val < b.val → p j=j) :
    inversionNumber (p*Equiv.swap 0 b)=inversionNumber p+1 := by
  classical
  let q := p*Equiv.swap 0 b
  have hb0 : b ≠ 0 := Fin.ne_of_val_ne (by simpa using Nat.ne_of_gt hb)
  have hq0 : q 0=p b := by simp [q]
  have hqb : q b=b := by simp [q,hhead]
  have hqi (i : Fin n) (hi0 : i ≠ 0) (hib : i ≠ b) : q i=p i := by
    simp only [q,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hi0 hib]
  have hend (j : Fin n) : _root_.LX.UploadDefinitions.FiniteChainMerge.invTerm q 0 j+_root_.LX.UploadDefinitions.FiniteChainMerge.invTerm q b j=
      _root_.LX.UploadDefinitions.FiniteChainMerge.invTerm p 0 j+_root_.LX.UploadDefinitions.FiniteChainMerge.invTerm p b j+(if j=b then 1 else 0) := by
    by_cases hj0 : j=0
    · subst j
      simp [_root_.LX.UploadDefinitions.FiniteChainMerge.invTerm,Ne.symm hb0]
    by_cases hjb : j=b
    · subst j
      simp only [_root_.LX.UploadDefinitions.FiniteChainMerge.invTerm,hq0,hqb,hhead,Fin.val_zero]
      split_ifs <;> omega
    simp only [_root_.LX.UploadDefinitions.FiniteChainMerge.invTerm,hq0,hqb,hhead,hqi j hj0 hjb,Fin.val_zero,hjb,ite_false,add_zero]
    have hjpos : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj0
    by_cases hjlt : j.val < b.val
    · rw [hfix j hjpos hjlt]
      split_ifs <;> omega
    · have hjne : j.val ≠ b.val := fun he => hjb (Fin.ext he)
      split_ifs <;> omega
  have hother (i : Fin n) (hi0 : i ≠ 0) (hib : i ≠ b) (j : Fin n) :
      _root_.LX.UploadDefinitions.FiniteChainMerge.invTerm q i j=_root_.LX.UploadDefinitions.FiniteChainMerge.invTerm p i j := by
    have hipos : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi0
    by_cases hj0 : j=0
    · subst j
      simp [_root_.LX.UploadDefinitions.FiniteChainMerge.invTerm]
    by_cases hjb : j=b
    · subst j
      rw [_root_.LX.UploadDefinitions.FiniteChainMerge.invTerm,_root_.LX.UploadDefinitions.FiniteChainMerge.invTerm,hqb,hqi i hi0 hib]
      by_cases hil : i.val < b.val
      · rw [hfix i hipos hil]
        split_ifs <;> omega
      · simp only [hil,false_and,ite_false]
    · simp only [_root_.LX.UploadDefinitions.FiniteChainMerge.invTerm,hqi i hi0 hib,hqi j hj0 hjb]
  let row := fun t : LX.Core.State n => fun i : Fin n => ∑ j,_root_.LX.UploadDefinitions.FiniteChainMerge.invTerm t i j
  have hrow : row q 0+row q b=row p 0+row p b+1 := by
    have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hend j)
    simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh
  have hr (i : Fin n) (hi0 : i ≠ 0) (hib : i ≠ b) : row q i=row p i := by
    apply Finset.sum_congr rfl
    exact fun j _ => hother i hi0 hib j
  have decomp (t : LX.Core.State n) : inversionNumber t=row t 0+row t b+
      ∑ i ∈ (Finset.univ.erase (0 : Fin n)).erase b,row t i := by
    have h0 := Finset.sum_erase_add Finset.univ (row t) (Finset.mem_univ (0 : Fin n))
    have h1 := Finset.sum_erase_add (Finset.univ.erase (0 : Fin n)) (row t)
      (by simp [hb0] : b ∈ Finset.univ.erase (0 : Fin n))
    change (∑ i,row t i)=_
    omega
  have he : (∑ i ∈ (Finset.univ.erase (0 : Fin n)).erase b,row q i)=
      ∑ i ∈ (Finset.univ.erase (0 : Fin n)).erase b,row p i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hr i (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      (Finset.mem_erase.mp hi).1
  rw [decomp q,decomp p,he,hrow]
  omega
