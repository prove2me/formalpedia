-- Prove2me | solution 1 for LX.Core.FiniteCuts.adjacent_swap_inversion_price
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:40:01.337293+00:00
-- url     : https://prove2.me/submissions/89d6b09a-b6c6-4466-bf90-3011db57930a

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

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem solution (p : State n) (a b : Fin n)
    (hadj : b.val=a.val+1) (hdesc : (p b).val < (p a).val) :
    inversionNumber (p*Equiv.swap a b)+1=inversionNumber p := by
  let τ : State n := Equiv.swap a b
  have hab : a ≠ b := by intro he; have := congrArg Fin.val he; omega
  have point (i j : Fin n) :
      (if (τ i).val < (τ j).val ∧ (p j).val < (p i).val then (1 : ℕ) else 0)+
        (if i=a ∧ j=b then 1 else 0)=
      (if i.val < j.val ∧ (p j).val < (p i).val then 1 else 0) := by
    have hiaval : i.val=a.val ↔ i=a := Fin.ext_iff.symm
    have hibval : i.val=b.val ↔ i=b := Fin.ext_iff.symm
    have hjaval : j.val=a.val ↔ j=a := Fin.ext_iff.symm
    have hjbval : j.val=b.val ↔ j=b := Fin.ext_iff.symm
    dsimp [τ]
    by_cases hia : i=a <;> by_cases hib : i=b <;>
      by_cases hja : j=a <;> by_cases hjb : j=b
    all_goals simp only [Equiv.swap_apply_def,hia,hib,hja,hjb,ite_true,ite_false]
    all_goals try subst i
    all_goals try subst j
    all_goals simp only [hab,Ne.symm hab,ite_false,true_and,false_and,and_true,and_false,ite_true,add_zero]
    all_goals try have hia' : i.val ≠ a.val := fun he => hia (Fin.ext he)
    all_goals try have hib' : i.val ≠ b.val := fun he => hib (Fin.ext he)
    all_goals try have hja' : j.val ≠ a.val := fun he => hja (Fin.ext he)
    all_goals try have hjb' : j.val ≠ b.val := fun he => hjb (Fin.ext he)
    all_goals split_ifs <;> omega
  have hreindex : inversionNumber (p*τ)=
      ∑ i : Fin n, ∑ j : Fin n, if (τ i).val < (τ j).val ∧ (p j).val < (p i).val then 1 else 0 := by
    unfold inversionNumber
    rw [← Equiv.sum_comp τ (fun i => ∑ j : Fin n,
      if i.val < j.val ∧ ((p*τ) j).val < ((p*τ) i).val then (1 : ℕ) else 0)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Equiv.sum_comp τ (fun j =>
      if (τ i).val < j.val ∧ ((p*τ) j).val < ((p*τ) (τ i)).val then (1 : ℕ) else 0)]
    simp only [Equiv.Perm.mul_apply,τ,Equiv.swap_apply_self]
  have hsum := congrArg (fun g : Fin n → Fin n → ℕ => ∑ i, ∑ j, g i j) (funext fun i => funext (point i))
  simp only [Finset.sum_add_distrib] at hsum
  have hone : (∑ i : Fin n, ∑ j : Fin n, if i=a ∧ j=b then (1 : ℕ) else 0)=1 := by
    simp only [ite_and]
    simp only [Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_const_zero]
  rw [hone] at hsum
  rw [hreindex]
  exact hsum
