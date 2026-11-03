-- Prove2me | solution 1 for LX.Core.FiniteCuts.fixed_count_two_reflection
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:02:50.975783+00:00
-- url     : https://prove2.me/submissions/d2ec84d6-f71d-448e-8fb2-e4c244955db4

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
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LinearMatchingGeometry
import Definitions.Def_LX_PhysicalModel
import Theorems.Thm_LX_Core_FiniteCuts_two_fixed_matching_reflection

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



















@[simp] theorem permutation_embed (W : Window n b) (p : State b) (i : Fin b) :
    permutation W p (embed W i)=embed W (p i) := p.extendDomain_apply_image (windowEquiv W) i



@[simp] theorem permutation_symm (W : Window n b) (p : State b) :
    (permutation W p).symm=permutation W p.symm := rfl







end LX.Core.FiniteWindow

end

section
namespace LX.Core.FiniteCuts
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}

theorem circular_reflection_of_endpoint_sum [NeZero n] (p : State n)
    (hzero : p 0=0) (hsum : ∀ i : Fin n, i ≠ 0 → i.val+(p i).val=n) :
    ∀ i, p i= -i := by
  intro i
  by_cases hi : i=0
  · subst i
    simpa using hzero
  · have h := congrArg (fun k : ℕ => (k : Fin n)) (hsum i hi)
    simp only [Nat.cast_add, Fin.cast_val_eq_self] at h
    apply eq_neg_iff_add_eq_zero.mpr
    simpa [add_comm] using h



/-- Even-case matching criterion in circular coordinates after choosing a fixed-point cut. -/
theorem two_fixed_circular_reflection [NeZero n] (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (t : Fin n) (ht : 0<t.val)
    (hfixed : ∀ i, p i=i ↔ i=0 ∨ i=t)
    (hnoadj : ∀ i : Fin n, i.val+1 ≠ (p i).val) :
    ∀ i, p i= -i :=
  circular_reflection_of_endpoint_sum p ((hfixed 0).mpr (Or.inl rfl))
    (two_fixed_matching_reflection p hinv hnc t ht hfixed hnoadj)



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

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}

theorem solution [NeZero n] (p : State n)
    (hinv : Function.Involutive p) (hnc : NoncrossingPairs p) (hzero : p 0=0)
    (hcard : (fixedPositions p).card=2)
    (hnoadj : ∀ i : Fin n, i.val+1 ≠ (p i).val) :
    ∀ i, p i= -i := by
  obtain ⟨a,b,hab,hs⟩ := Finset.card_eq_two.mp hcard
  have hmem : (0 : Fin n) ∈ ({a,b} : Finset (Fin n)) := by
    rw [← hs]
    exact (mem_fixedPositions p 0).mpr hzero
  have hzeroab : (0 : Fin n)=a ∨ (0 : Fin n)=b := by simpa using hmem
  rcases hzeroab with ha | hb
  · subst a
    have hb0 : 0<b.val := by
      have hbne : b.val ≠ 0 := fun h => hab (Fin.ext h).symm
      omega
    apply two_fixed_circular_reflection p hinv hnc b hb0
      (fun i => by rw [← mem_fixedPositions,hs]; simp) hnoadj
  · subst b
    have ha0 : 0<a.val := by
      have hane : a.val ≠ 0 := fun h => hab (Fin.ext h)
      omega
    apply two_fixed_circular_reflection p hinv hnc a ha0
      (fun i => by rw [← mem_fixedPositions,hs]; simp [or_comm]) hnoadj
