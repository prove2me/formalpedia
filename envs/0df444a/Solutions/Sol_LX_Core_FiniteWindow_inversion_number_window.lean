-- Prove2me | solution 1 for LX.Core.FiniteWindow.inversion_number_window
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:35:46.638741+00:00
-- url     : https://prove2.me/submissions/3152ad80-f9d2-4fba-8f54-d925107bacf1

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
import Theorems.Thm_LX_Core_FiniteWindow_sum_window_nat

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















theorem contains_embed (W : Window n b) (i : Fin b) : Contains W (embed W i) :=
  (windowEquiv W i).property

theorem contains_iff (W : Window n b) (j : Fin n) : Contains W j ↔ ∃ i, embed W i=j := by
  constructor
  · intro h
    refine ⟨(windowEquiv W).symm ⟨j,h⟩, ?_⟩
    exact congrArg Subtype.val ((windowEquiv W).apply_symm_apply ⟨j,h⟩)
  · rintro ⟨i,rfl⟩
    exact contains_embed W i

@[simp] theorem permutation_embed (W : Window n b) (p : State b) (i : Fin b) :
    permutation W p (embed W i)=embed W (p i) := p.extendDomain_apply_image (windowEquiv W) i

theorem permutation_outside (W : Window n b) (p : State b) (j : Fin n) (hj : ¬Contains W j) :
    permutation W p j=j := p.extendDomain_apply_not_subtype (windowEquiv W) hj

@[simp] theorem permutation_symm (W : Window n b) (p : State b) :
    (permutation W p).symm=permutation W p.symm := rfl







end LX.Core.FiniteWindow

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}






end LX.Core.FiniteCuts

namespace LX.Core.FiniteWindow
open scoped BigOperators
variable {n b : ℕ}



theorem contains_permutation (W : Window n b) (p : State b) (i : Fin n)
    (hi : Contains W i) : Contains W (permutation W p i) := by
  obtain ⟨j,rfl⟩ := (contains_iff W i).mp hi
  rw [permutation_embed]
  exact contains_embed W (p j)

theorem no_outside_inversion (W : Window n b) (p : State b) (i j : Fin n)
    (hout : ¬Contains W i ∨ ¬Contains W j) :
    ¬(i.val < j.val ∧ (permutation W p j).val < (permutation W p i).val) := by
  intro h
  rcases hout with hi | hj
  · rw [permutation_outside W p i hi] at h
    by_cases hj : Contains W j
    · have hpj := contains_permutation W p j hj
      unfold Contains at hi hj hpj
      omega
    · rw [permutation_outside W p j hj] at h
      omega
  · rw [permutation_outside W p j hj] at h
    by_cases hi : Contains W i
    · have hpi := contains_permutation W p i hi
      unfold Contains at hi hj hpi
      omega
    · rw [permutation_outside W p i hi] at h
      omega




end LX.Core.FiniteWindow

end

namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
open LX
open LX.Core
open LX.Core.FiniteWindow
open scoped BigOperators
variable {n b : ℕ}

theorem solution (W : Window n b) (p : State b) :
    FiniteCuts.inversionNumber (permutation W p)=FiniteCuts.inversionNumber p := by
  unfold FiniteCuts.inversionNumber
  rw [sum_window_nat W _ (by
    intro i hi
    apply Finset.sum_eq_zero
    intro j _
    exact if_neg (no_outside_inversion W p i j (Or.inl hi)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_window_nat W _ (by
    intro j hj
    exact if_neg (no_outside_inversion W p (embed W i) j (Or.inr hj)))]
  apply Finset.sum_congr rfl
  intro j _
  simp only [permutation_embed]
  simp [embed]
