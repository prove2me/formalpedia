-- Prove2me | solution 1 for LX.Core.FiniteCuts.domain_rotation_inversions
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:16:19.836548+00:00
-- url     : https://prove2.me/submissions/0f5680d5-ac6d-4740-924d-74be55aed798

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
import Definitions.Def_LX_FiniteInversionDecomposition
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
variable {n k : ℕ}



theorem inversion_on_first (f : Fin (k+1) → Fin n) :
    inversionOn f=inversionOn (fun i : Fin k => f i.succ)+
      ∑ i : Fin k, if (f i.succ).val < (f 0).val then 1 else 0 := by
  simp only [inversionOn,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,
    Nat.not_lt_zero,false_and,ite_false,Nat.zero_lt_succ,true_and,
    Nat.add_lt_add_iff_right,add_zero,zero_add]
  omega

theorem inversion_on_last (f : Fin (k+1) → Fin n) :
    inversionOn f=inversionOn (fun i : Fin k => f i.castSucc)+
      ∑ i : Fin k, if (f (Fin.last k)).val < (f i.castSucc).val then 1 else 0 := by
  have hlt (i : Fin k) : i.val < k := i.isLt
  have hnot (i : Fin k) : ¬k < i.val := by have := i.isLt; omega
  simp only [inversionOn,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,
    hlt,hnot,lt_self_iff_false,false_and,true_and,ite_false,Finset.sum_const_zero,
    add_zero,zero_add,Finset.sum_add_distrib]






end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {k : ℕ}

theorem count_values_below {n : ℕ} (p : State n) (a : ℕ) :
    (∑ i : Fin n, if (p i).val < a then (1 : ℕ) else 0)=min n a := by
  calc
    _ = ∑ i : Fin n, if i.val < a then (1 : ℕ) else 0 := Equiv.sum_comp p _
    _ = _ := by simp [Fin.card_filter_val_lt]

theorem rotate_castSucc (i : Fin k) : finRotate (k+1) i.castSucc=i.succ :=
  finRotate_of_lt i.isLt







end LX.Core.FiniteCuts

end

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open scoped BigOperators
variable {k : ℕ}

/-- Moving the first position to the last changes only its inversion pairs. -/
theorem solution (p : State (k+1)) :
    inversionNumber (p*finRotate (k+1))+2*(p 0).val=inversionNumber p+k := by
  classical
  have hfirst := inversion_on_first p
  have hlast := inversion_on_last (fun i : Fin (k+1) => p (finRotate (k+1) i))
  simp only [rotate_castSucc,finRotate_last] at hlast
  have hlow : (∑ i : Fin k, if (p i.succ).val < (p 0).val then (1 : ℕ) else 0)=(p 0).val := by
    have h := count_values_below p (p 0).val
    rw [Fin.sum_univ_succ] at h
    simpa only [lt_self_iff_false,ite_false,zero_add,min_eq_right (le_of_lt (p 0).isLt)] using h
  have hsplit :
      (∑ i : Fin k, if (p i.succ).val < (p 0).val then (1 : ℕ) else 0)+
      (∑ i : Fin k, if (p 0).val < (p i.succ).val then (1 : ℕ) else 0)=k := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : Fin k, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        have hne : (p i.succ).val ≠ (p 0).val := by
          intro h
          have hi := p.injective (Fin.ext h)
          have hv := congrArg Fin.val hi
          simp only [Fin.val_succ,Fin.val_zero] at hv
          omega
        split_ifs <;> omega
      _ = k := by simp
  change inversionNumber p=_ at hfirst
  change inversionNumber (p*finRotate (k+1))=_ at hlast
  omega
