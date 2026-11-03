-- Prove2me | solution 1 for LX.Core.FiniteCuts.sole_zero_fixed_matching_reflection
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:59:47.345416+00:00
-- url     : https://prove2.me/submissions/0e4ffbf4-ad46-494d-8a0e-860339bd5a54

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LinearMatchingGeometry
import Definitions.Def_LX_PhysicalModel
import Theorems.Thm_LX_Core_FiniteCuts_window_unique_adjacent_reflection

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
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



@[simp] theorem permutation_symm (W : Window n b) (p : State b) :
    (permutation W p).symm=permutation W p.symm := rfl







end LX.Core.FiniteWindow

end

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
variable {n b : ℕ}

/-- After cutting at the sole fixed point, the remaining matching is the linear reversal. -/
theorem solution (p : State (n+1))
    (hinv : Function.Involutive p) (hnc : NoncrossingPairs p) (hzero : p 0=0)
    (hfixed : ∀ i : Fin (n+1), p i=i → i=0)
    (hunique : ∀ a b : Fin (n+1), a.val+1=(p a).val → b.val+1=(p b).val → a=b) :
    ∀ i : Fin (n+1), i ≠ 0 → i.val+(p i).val=n+1 := by
  let W : FiniteWindow.Window (n+1) n := ⟨1,by omega⟩
  have hclosed : ∀ j, FiniteWindow.Contains W j → FiniteWindow.Contains W (p j) := by
    intro j hj
    have hjne : j ≠ 0 := by intro heq; subst j; change 1 ≤ 0 ∧ _ at hj; omega
    have hpne : p j ≠ 0 := by intro heq; exact hjne (p.injective (heq.trans hzero.symm))
    have hpval : (p j).val ≠ 0 := fun heq => hpne (Fin.ext heq)
    have hpbound := (p j).isLt
    change 1 ≤ (p j).val ∧ (p j).val < 1+n
    omega
  have hnfix : ∀ j, FiniteWindow.Contains W j → p j ≠ j := by
    intro j hj heq
    have hz := hfixed j heq
    subst j
    change 1 ≤ 0 ∧ _ at hj
    omega
  have href := window_unique_adjacent_reflection p W hinv hnc hclosed hnfix hunique
  intro i hi
  have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
  have hiW : FiniteWindow.Contains W i := by
    change 1 ≤ i.val ∧ i.val < 1+n
    have := i.isLt
    omega
  obtain ⟨j,rfl⟩ := (FiniteWindow.contains_iff W i).mp hiW
  rw [href]
  dsimp [FiniteWindow.embed,W]
  have := j.isLt
  omega
