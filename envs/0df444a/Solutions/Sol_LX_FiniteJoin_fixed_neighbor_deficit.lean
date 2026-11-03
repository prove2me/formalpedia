-- Prove2me | solution 1 for LX.FiniteJoin.fixed_neighbor_deficit
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:33:19.117238+00:00
-- url     : https://prove2.me/submissions/7da202a4-5d20-4af5-bd48-1ce5f176c11a

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
import Definitions.Def_LX_FiniteEnergyRotation
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_FixedPairJoinPrice
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ShallowCutShift
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_Core_FiniteCuts_adjacent_boundary_mass_price
import Theorems.Thm_LX_Core_FiniteCuts_adjacent_swap_inversion_price
import Theorems.Thm_LX_Core_FiniteCuts_domain_rotation_inversions
import Theorems.Thm_LX_Core_FiniteCuts_inverse_rotate_int
import Theorems.Thm_LX_Core_FiniteCuts_inversion_number_inverse
import Theorems.Thm_LX_Core_FiniteCuts_rotation_energy_change

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
namespace LX.FiniteJoin
end LX.FiniteJoin
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



/-- The same raising adjacent exchange has exact inversion cost one. -/
theorem adjacent_raising_inversion_price (p : State n) (a b : Fin n)
    (hadj : b.val=a.val+1) (hp : (p a).val < (p b).val) :
    inversionNumber (p*Equiv.swap a b)=inversionNumber p+1 := by
  have hh := adjacent_swap_inversion_price (p*Equiv.swap a b) a b hadj (by
    simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_left,Equiv.swap_apply_right] using hp)
  have he : p*Equiv.swap a b*Equiv.swap a b=p := by simp [mul_assoc]
  rw [he] at hh
  exact hh.symm



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
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]




theorem shift_conjugate_succ (p : State n) (t : ℕ) :
    shiftConjugate p (t+1)=rotateConjugate (shiftConjugate p t) := by
  simp only [shiftConjugate,rotateConjugate,pow_succ,mul_inv_rev,mul_assoc]


theorem shift_conjugate_apply (p : State n) (c i : Fin n) :
    shiftConjugate p c.val i=p (i+c)-c := by
  have hP (j : Fin n) : (finRotate n^c.val) j=j+c := by
    simpa only [LX.Core.L,Fin.cast_val_eq_self] using AffineLift.rotation_power_apply c.val j
  have hR (j : Fin n) : (finRotate n^c.val)⁻¹ j=j-c := by
    apply (finRotate n^c.val).injective
    change (finRotate n^c.val) ((finRotate n^c.val).symm j)=(finRotate n^c.val) (j-c)
    rw [Equiv.apply_symm_apply,hP,sub_add_cancel]
  simp only [shiftConjugate,Equiv.Perm.mul_apply,hP,hR]


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
namespace LX.FiniteJoin
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]



theorem shift_depth_deficit (q : State n) (t : ℕ) :
    depthDeficit (shiftConjugate q t)=depthDeficit q := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ k =>
    induction t with
    | zero => simp [shiftConjugate,depthDeficit]
    | succ t ih =>
      rw [shift_conjugate_succ]
      exact (rotation_energy_minus_inversions (shiftConjugate q t)).trans ih

theorem shift_neighbor_swap (q : State n) (u : Fin n) :
    shiftConjugate (q*Equiv.swap u (u+1)) u.val=shiftConjugate q u.val*Equiv.swap 0 1 := by
  apply Equiv.ext
  intro i
  rw [shift_conjugate_apply]
  change q (Equiv.swap u (u+1) (i+u))-u=shiftConjugate q u.val (Equiv.swap 0 1 i)
  rw [shift_conjugate_apply]
  congr 1
  apply congrArg q
  have hh := Function.Injective.map_swap (f := fun j : Fin n => j+u) (add_left_injective u) 0 1 i
  simpa only [zero_add,add_zero,add_comm] using hh.symm





end LX.FiniteJoin

end

namespace LX.FiniteJoin
end LX.FiniteJoin
open LX
open LX.FiniteJoin
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Joining two fixed neighbors increases finite depth minus inversions by
exactly one. Moving the finite cut first handles the seam without a separate
unproved formula for exchanging the first and last positions. -/
theorem solution (hn : 2 ≤ n) (q : State n) (u : Fin n)
    (hu : q u=u) (hv : q (u+1)=u+1) :
    depthDeficit (q*Equiv.swap u (u+1))=depthDeficit q+1 := by
  let Q := shiftConjugate q u.val
  have hQ0 : Q 0=0 := by
    simp only [Q,shift_conjugate_apply,zero_add,hu,sub_self]
  have hQ1 : Q 1=1 := by
    change shiftConjugate q u.val 1=1
    rw [shift_conjugate_apply,add_comm (1 : Fin n) u,hv]
    abel
  have h01 : (1 : Fin n).val=(0 : Fin n).val+1 := by
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hmass := adjacent_boundary_mass_price Q 0 1 h01
    (by rw [hQ0]) (by rw [hQ1])
  have hI := adjacent_raising_inversion_price Q 0 1 h01 (by rw [hQ0,hQ1]; omega)
  have hprice : depthDeficit (Q*Equiv.swap 0 1)=depthDeficit Q+1 := by
    unfold depthDeficit
    rw [hmass,hI]
    push_cast
    ring
  calc
    _ = depthDeficit (shiftConjugate (q*Equiv.swap u (u+1)) u.val) := (shift_depth_deficit _ _).symm
    _ = depthDeficit (Q*Equiv.swap 0 1) := by rw [shift_neighbor_swap]
    _ = depthDeficit Q+1 := hprice
    _ = depthDeficit q+1 := by rw [shift_depth_deficit]
