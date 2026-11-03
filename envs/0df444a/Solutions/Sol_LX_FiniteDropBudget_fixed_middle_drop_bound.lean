-- Prove2me | solution 1 for LX.FiniteDropBudget.fixed_middle_drop_bound
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:39:27.053288+00:00
-- url     : https://prove2.me/submissions/09ef40f9-7ad5-4287-b47c-b2befea74708

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
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteDropBudget
import Definitions.Def_LX_FiniteEnergyRotation
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Theorems.Thm_LX_Core_FiniteCuts_domain_rotation_inversions
import Theorems.Thm_LX_Core_FiniteCuts_inverse_rotate_int
import Theorems.Thm_LX_Core_FiniteCuts_inversion_number_inverse
import Theorems.Thm_LX_Core_FiniteCuts_rotation_energy_change
import Theorems.Thm_LX_FiniteDropBudget_fixed_prefix_drop_bound

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

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem inversion_indicator_self (p : State n) (i : Fin n) :
    inversionIndicator p i i=0 := by simp [inversionIndicator]







theorem sum_descending_indicator (p : State n) :
    (∑ i, descendingIndicator p i)=((descendingPositions p).card : ℤ) := by
  unfold descendingIndicator
  rw [← Finset.sum_filter]
  simp [descendingPositions]







end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {k : ℕ}







theorem value_rotation_inversions (p : State (k+1)) :
    inversionNumber ((finRotate (k+1))⁻¹*p)+2*(p⁻¹ 0).val=inversionNumber p+k := by
  have h := domain_rotation_inversions p⁻¹
  have he : p⁻¹*finRotate (k+1)=((finRotate (k+1))⁻¹*p)⁻¹ := by simp
  rw [he,inversion_number_inverse,inversion_number_inverse] at h
  exact h



end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {k : ℕ}

theorem rotation_inversion_change (p : State (k+1)) :
    (inversionNumber (rotateConjugate p) : ℤ)-(inversionNumber p : ℤ)=
      if p 0=0 then 0 else 2*(k+1 : ℤ)-2*(p 0 : ℤ)-2*(p.symm 0 : ℤ) := by
  have hd := congrArg (fun v : ℕ => (v : ℤ)) (domain_rotation_inversions p)
  have hv := congrArg (fun v : ℕ => (v : ℤ)) (value_rotation_inversions (p*finRotate (k+1)))
  push_cast at hd hv
  simp only [← mul_assoc] at hv
  change (inversionNumber (rotateConjugate p) : ℤ)+2*((p*finRotate (k+1))⁻¹ 0 : ℤ)=
    (inversionNumber (p*finRotate (k+1)) : ℤ)+(k : ℤ) at hv
  have hb : ((p*finRotate (k+1))⁻¹ 0 : ℤ)=
      (p.symm 0 : ℤ)-1+(if p.symm 0=0 then (k+1 : ℤ) else 0) := by
    simpa only [mul_inv_rev,Equiv.Perm.mul_apply,Equiv.Perm.inv_def] using inverse_rotate_int (p.symm 0)
  rw [hb] at hv
  by_cases hp : p 0=0
  · have hp' : p.symm 0=0 := by simpa only [hp] using p.symm_apply_apply 0
    simp only [hp',ite_true,Fin.val_zero,Nat.cast_zero] at hv
    simp only [hp,Fin.val_zero,Nat.cast_zero] at hd
    simp only [hp,ite_true]
    linarith only [hd,hv]
  · have hp' : p.symm 0 ≠ 0 := by
      intro h
      apply hp
      have he := congrArg p h
      simpa only [Equiv.apply_symm_apply] using he.symm
    simp only [hp',ite_false] at hv
    simp only [hp,ite_false]
    linarith only [hd,hv]

theorem rotation_energy_minus_inversions (p : State (k+1)) :
    (∑ i : Fin (k+1), |_root_.LX.Core.FiniteCuts.displacement (rotateConjugate p) i|)-
      (inversionNumber (rotateConjugate p) : ℤ)=
    (∑ i : Fin (k+1), |_root_.LX.Core.FiniteCuts.displacement p i|)-(inversionNumber p : ℤ) := by
  have hE := rotation_energy_change p
  have hI := rotation_inversion_change p
  linarith only [hE,hI]



end LX.Core.FiniteCuts

end

section
namespace LX.FiniteDropBudget
open scoped BigOperators
open LX.Core.FiniteCuts
variable {k : ℕ}

theorem rotate_conjugate_drops (p : LX.Core.State (k+1)) (hp : p 0 ≠ 0) :
    (descendingPositions (rotateConjugate p)).card=(descendingPositions p).card := by
  have hp' : p.symm 0 ≠ 0 := by
    intro he
    have hh := congrArg p he
    simp only [Equiv.apply_symm_apply] at hh
    exact hp hh.symm
  have hz (i : Fin (k+1)) : p i=0 ↔ i=p.symm 0 := by
    exact (Equiv.eq_symm_apply p).symm
  have hpoint (i : Fin (k+1)) :
      descendingIndicator (rotateConjugate p) ((finRotate (k+1)).symm i)+
        (if i=p.symm 0 then (1 : ℤ) else 0)=
      descendingIndicator p i+(if i=0 then (1 : ℤ) else 0) := by
    have hri := inverse_rotate_int i
    have hrp := inverse_rotate_int (p i)
    have he : rotateConjugate p ((finRotate (k+1)).symm i)=
        (finRotate (k+1)).symm (p i) := by
      simp only [rotateConjugate,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply]
    unfold descendingIndicator
    rw [he]
    simp only [hz] at hrp
    by_cases hi0 : i=0
    · subst i
      simp only [hp',Ne.symm hp',ite_false,ite_true,Fin.val_zero,Nat.cast_zero] at hri hrp ⊢
      have := (p 0).isLt
      have := Fin.pos_iff_ne_zero.mpr hp
      split_ifs <;> omega
    by_cases hip : i=p.symm 0
    · subst i
      simp only [hp',ite_false,ite_true,Equiv.apply_symm_apply,Fin.val_zero,Nat.cast_zero] at hri hrp ⊢
      have := (p.symm 0).isLt
      have := Fin.pos_iff_ne_zero.mpr hp'
      split_ifs <;> omega
    · simp only [hi0,hip,ite_false,add_zero] at hri hrp ⊢
      split_ifs <;> omega
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hpoint i)
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hs
  rw [Equiv.sum_comp (finRotate (k+1)).symm,sum_descending_indicator,sum_descending_indicator] at hs
  omega

theorem rotate_conjugate_units_le (p : LX.Core.State (k+1))
    (hp : p 0 ≠ Fin.last k) :
    (backwardUnits (rotateConjugate p)).card ≤ (backwardUnits p).card := by
  classical
  apply Finset.card_le_card_of_injOn (finRotate (k+1))
  · intro j hj
    let i := finRotate (k+1) j
    have hj' : j=(finRotate (k+1)).symm i := by simp [i]
    have hunit : ((rotateConjugate p) j).val+1=j.val := (Finset.mem_filter.mp hj).2
    have he : rotateConjugate p j=(finRotate (k+1)).symm (p i) := by
      simp only [rotateConjugate,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,i]
    have hri := inverse_rotate_int i
    have hrp := inverse_rotate_int (p i)
    rw [he,hj'] at hunit
    have hi := i.isLt
    have hpi := (p i).isLt
    have hval : (p 0).val ≠ k := fun hh => hp (Fin.ext hh)
    have hgoal : (p i).val+1=i.val := by
      by_cases hi0 : i=0
      · simp only [hi0,ite_true,Fin.val_zero,Nat.cast_zero] at hri hrp hunit ⊢
        split_ifs at hrp <;> omega
      by_cases hpi0 : p i=0
      · simp only [hpi0,hi0,ite_false,ite_true,Fin.val_zero,Nat.cast_zero,add_zero] at hri hrp hunit
        omega
      · simp only [hi0,hpi0,ite_false,add_zero] at hri hrp
        omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hgoal⟩
  · intro i _ j _ he
    exact (finRotate (k+1)).injective he






end LX.FiniteDropBudget

end

namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
open LX
open LX.FiniteDropBudget
open scoped BigOperators
open LX.Core.FiniteCuts
variable {k : ℕ}

/-- A fixed interval just after a moving head can be recentered without
creating a backward unit arrow unless the head maps to the last position. -/
theorem solution (p : LX.Core.State (k+1)) (r : ℕ)
    (hr : r ≤ k+1) (hp : p 0 ≠ 0) (hlast : p 0 ≠ Fin.last k)
    (hfix : ∀ i : Fin (k+1),0 < i.val → i.val < r → p i=i) :
    3*((descendingPositions p).card : ℤ) ≤ ((k+1 : ℕ) : ℤ)-(r : ℤ)+
      (∑ i, |_root_.LX.Core.FiniteCuts.displacement p i|)-(inversionNumber p : ℤ)+(backwardUnits p).card := by
  have h := fixed_prefix_drop_bound (rotateConjugate p) (r-1) (by omega) (by
    intro i hi
    have hik : i.val < k := by omega
    have hri : (finRotate (k+1) i).val=i.val+1 := by
      rw [finRotate_of_lt hik]
    have hf := hfix (finRotate (k+1) i) (by omega) (by omega)
    simp only [rotateConjugate,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,hf,Equiv.symm_apply_apply])
  rw [rotate_conjugate_drops p hp] at h
  have hm := rotation_energy_minus_inversions p
  have hu := rotate_conjugate_units_le p hlast
  rw [Nat.cast_sub (by omega : r-1 ≤ k+1)] at h
  omega
