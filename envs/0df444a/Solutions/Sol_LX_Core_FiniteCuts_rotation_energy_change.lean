-- Prove2me | solution 1 for LX.Core.FiniteCuts.rotation_energy_change
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:27:58.267464+00:00
-- url     : https://prove2.me/submissions/a6c94abb-9ac6-4573-a377-1ae99d56e517

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Theorems.Thm_LX_Core_FiniteCuts_inverse_rotate_int

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
variable {k : ℕ}





theorem rotation_energy_point (p : State (k+1)) (hp : p 0 ≠ 0) (i : Fin (k+1)) :
    |((finRotate (k+1)).symm (p i) : ℤ)-((finRotate (k+1)).symm i : ℤ)|=
      |_root_.LX.Core.FiniteCuts.displacement p i|+
      (if i=0 then (k+1 : ℤ)-2*(p 0 : ℤ) else 0)+
      (if i=p.symm 0 then (k+1 : ℤ)-2*(p.symm 0 : ℤ) else 0) := by
  have hb : p.symm 0 ≠ 0 := by
    intro h
    apply hp
    have he := congrArg p h
    simpa only [Equiv.apply_symm_apply] using he.symm
  have hz : p i=0 ↔ i=p.symm 0 := by
    constructor
    · intro h
      exact (p.symm_apply_apply i).symm.trans (congrArg p.symm h)
    · intro h
      rw [h,p.apply_symm_apply]
  rw [inverse_rotate_int,inverse_rotate_int]
  unfold _root_.LX.Core.FiniteCuts.displacement
  by_cases hi : i=0
  · subst i
    have ha0 : (0 : ℤ) ≤ p 0 := by positivity
    have han : (p 0 : ℤ) < k+1 := by exact_mod_cast (p 0).isLt
    simp only [hp,hb,Ne.symm hb,ite_false,ite_true,Fin.val_zero,Nat.cast_zero]
    rw [abs_of_nonpos (show (p 0 : ℤ)-1+0-(0-1+(k+1 : ℤ)) ≤ 0 by omega),
      abs_of_nonneg (show (0 : ℤ) ≤ (p 0 : ℤ)-0 by omega)]
    omega
  · by_cases hib : i=p.symm 0
    · subst i
      have hb0 : (0 : ℤ) ≤ p.symm 0 := by positivity
      have hbn : (p.symm 0 : ℤ) < k+1 := by exact_mod_cast (p.symm 0).isLt
      simp only [p.apply_symm_apply,hb,ite_false,ite_true,Fin.val_zero,Nat.cast_zero]
      rw [abs_of_nonneg (show (0 : ℤ) ≤ 0-1+(k+1 : ℤ)-((p.symm 0 : ℤ)-1+0) by omega),
        abs_of_nonpos (show (0 : ℤ)-(p.symm 0 : ℤ) ≤ 0 by omega)]
      omega
    · have hpi : p i ≠ 0 := fun h => hib (hz.mp h)
      simp only [hi,hib,hpi,ite_false,add_zero]
      congr 1
      ring




end LX.Core.FiniteCuts

end

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open scoped BigOperators
variable {k : ℕ}

theorem solution (p : State (k+1)) :
    (∑ i : Fin (k+1), |_root_.LX.Core.FiniteCuts.displacement (rotateConjugate p) i|)-
      (∑ i : Fin (k+1), |_root_.LX.Core.FiniteCuts.displacement p i|)=
      if p 0=0 then 0 else 2*(k+1 : ℤ)-2*(p 0 : ℤ)-2*(p.symm 0 : ℤ) := by
  classical
  have hm : (∑ i : Fin (k+1), |_root_.LX.Core.FiniteCuts.displacement (rotateConjugate p) i|)=
      ∑ i : Fin (k+1), |((finRotate (k+1)).symm (p i) : ℤ)-((finRotate (k+1)).symm i : ℤ)| := by
    have h := Equiv.sum_comp (finRotate (k+1)).symm (fun i : Fin (k+1) => |_root_.LX.Core.FiniteCuts.displacement (rotateConjugate p) i|)
    simpa only [_root_.LX.Core.FiniteCuts.displacement,rotateConjugate,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,
      Equiv.apply_symm_apply] using h.symm
  rw [hm]
  by_cases hp : p 0=0
  · have hz (i : Fin (k+1)) : p i=0 ↔ i=0 := by
      calc
        p i=0 ↔ p i=p 0 := by rw [hp]
        _ ↔ i=0 := p.injective.eq_iff
    have he (i : Fin (k+1)) :
        |((finRotate (k+1)).symm (p i) : ℤ)-((finRotate (k+1)).symm i : ℤ)|=|_root_.LX.Core.FiniteCuts.displacement p i| := by
      rw [inverse_rotate_int,inverse_rotate_int]
      simp only [hz]
      unfold _root_.LX.Core.FiniteCuts.displacement
      congr 1
      ring
    simp only [he,hp,ite_true,sub_self]
  · simp only [hp,ite_false]
    simp_rw [rotation_energy_point p hp]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
    simp
    ring
