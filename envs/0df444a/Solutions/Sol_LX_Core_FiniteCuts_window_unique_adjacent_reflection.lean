-- Prove2me | solution 1 for LX.Core.FiniteCuts.window_unique_adjacent_reflection
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:57:33.545785+00:00
-- url     : https://prove2.me/submissions/0eac675d-c117-4d3b-8089-d4e3fa15ebba

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
import Definitions.Def_LX_FiniteWindowRestriction
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LinearMatchingGeometry
import Definitions.Def_LX_PhysicalModel
import Theorems.Thm_LX_Core_FiniteCuts_unique_adjacent_matching_reflection

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













theorem embed_injective (W : Window n b) : Function.Injective (embed W) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [embed] at this
  omega

theorem contains_embed (W : Window n b) (i : Fin b) : Contains W (embed W i) :=
  (windowEquiv W i).property



@[simp] theorem permutation_embed (W : Window n b) (p : State b) (i : Fin b) :
    permutation W p (embed W i)=embed W (p i) := p.extendDomain_apply_image (windowEquiv W) i



@[simp] theorem permutation_symm (W : Window n b) (p : State b) :
    (permutation W p).symm=permutation W p.symm := rfl







end LX.Core.FiniteWindow

end

section
/-! Extract the finite permutation of an invariant physical window. -/
namespace LX.Core.FiniteWindow
variable {n b : ℕ}

theorem invariant_of_inverse_closed (p : State n) (S : Finset (Fin n))
    (hclosed : ∀ i ∈ S, p.symm i ∈ S) : ∀ i, p i ∈ S ↔ i ∈ S := by
  classical
  have himage : S.image p.symm=S := Finset.eq_of_subset_of_card_le
    (Finset.image_subset_iff.mpr hclosed) (by rw [Finset.card_image_of_injective _ p.symm.injective])
  intro i
  constructor
  · intro hi
    simpa using hclosed (p i) hi
  · intro hi
    rw [← himage] at hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
    simpa only [← he,p.apply_symm_apply] using hj



theorem embed_restriction (W : Window n b) (p : State n)
    (hW : ∀ j, Contains W (p j) ↔ Contains W j) (i : Fin b) :
    embed W (restriction W p hW i)=p (embed W i) := by
  change ((windowEquiv W) ((windowEquiv W).symm ((p.subtypePerm hW) ((windowEquiv W) i)))).val= _
  rw [Equiv.apply_symm_apply]
  rfl

theorem exists_restriction_of_inverse_closed (W : Window n b) (p : State n)
    (hclosed : ∀ j, Contains W j → Contains W (p.symm j)) :
    ∃ filling : State b, ∀ i, p.symm (embed W i)=embed W (filling i) := by
  classical
  let S := Finset.univ.filter (Contains W)
  have hS : ∀ j, p j ∈ S ↔ j ∈ S := invariant_of_inverse_closed p S
    (fun j hj => by simpa [S] using hclosed j (by simpa [S] using hj))
  have hW : ∀ j, Contains W (p.symm j) ↔ Contains W j := by
    intro j
    have h := hS (p.symm j)
    simpa [S] using h.symm
  exact ⟨restriction W p.symm hW,fun i => (embed_restriction W p.symm hW i).symm⟩


end LX.Core.FiniteWindow

end

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
variable {n b : ℕ}

/-- The reflection criterion applies to an invariant finite window, even with fixed points outside. -/
theorem solution (p : State n) (W : FiniteWindow.Window n b)
    (hinv : Function.Involutive p) (hnc : NoncrossingPairs p)
    (hclosed : ∀ j, FiniteWindow.Contains W j → FiniteWindow.Contains W (p j))
    (hfixed : ∀ j, FiniteWindow.Contains W j → p j ≠ j)
    (hunique : ∀ a b : Fin n, a.val+1=(p a).val → b.val+1=(p b).val → a=b) :
    ∀ i : Fin b, p (FiniteWindow.embed W i)=FiniteWindow.embed W i.rev := by
  obtain ⟨q,hmatch⟩ := FiniteWindow.exists_restriction_of_inverse_closed W p.symm
    (by simpa only [Equiv.symm_symm] using hclosed)
  simp only [Equiv.symm_symm] at hmatch
  have hinjq := FiniteWindow.embed_injective W
  have hqinv : Function.Involutive q := by
    intro i
    apply hinjq
    rw [← hmatch, ← hmatch, hinv]
  have hqnc : NoncrossingPairs q := by
    intro a b c d hab hbc hcd hac hbd
    have h1 : p (FiniteWindow.embed W a)=FiniteWindow.embed W c := by rw [hmatch,hac]
    have h2 : p (FiniteWindow.embed W b)=FiniteWindow.embed W d := by rw [hmatch,hbd]
    apply hnc (FiniteWindow.embed W a) (FiniteWindow.embed W b)
      (FiniteWindow.embed W c) (FiniteWindow.embed W d) ?_ ?_ ?_ h1 h2
    all_goals dsimp [FiniteWindow.embed]; omega
  have hqfixed : ∀ i, q i ≠ i := by
    intro i heq
    apply hfixed (FiniteWindow.embed W i) (FiniteWindow.contains_embed W i)
    rw [hmatch,heq]
  have hqunique : ∀ a b : Fin b, a.val+1=(q a).val → b.val+1=(q b).val → a=b := by
    intro a b ha hb
    apply hinjq
    apply hunique
    · rw [hmatch]
      dsimp [FiniteWindow.embed]
      omega
    · rw [hmatch]
      dsimp [FiniteWindow.embed]
      omega
  have href := unique_adjacent_matching_reflection q hqinv hqnc hqfixed hqunique
  intro i
  rw [hmatch,href]
