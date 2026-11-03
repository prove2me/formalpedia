-- Prove2me | solution 1 for LX.FiniteDropBudget.fixed_prefix_drop_bound
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:21:33.852203+00:00
-- url     : https://prove2.me/submissions/cdd3ee26-a9bf-4a1a-9a12-3219b3026cce

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
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_FiniteWindowRestriction
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Theorems.Thm_LX_Core_FiniteWindow_inversion_number_window
import Theorems.Thm_LX_Core_FiniteWindow_sum_window_nat
import Theorems.Thm_LX_FiniteDropBudget_three_drops_bound

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
/-! Compatibility aliases for core if-then-else lemmas renamed after Lean 4.33.1.
The source proof bodies use the newer names; these aliases preserve their types.
-/
namespace LX
universe u



theorem ite_eq_right {α : Sort u} {p : Prop} {inst : Decidable p} {a b : α} (h : ¬ p) :
    (if p then a else b) = b := if_neg h

end LX

namespace List
universe u

end List

/-
The following proof is adapted from Mathlib, copyright (c) 2026 Seewoo Lee,
licensed under Apache 2.0. Source revision 56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/Algebra/Order/Floor/BigOperators.lean, lines 28-45.
-/
namespace Int
open scoped BigOperators


end Int

end

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


theorem displacement_embed (W : Window n b) (p : State b) (i : Fin b) :
    _root_.LX.Core.FiniteCuts.displacement (permutation W p) (embed W i)=_root_.LX.Core.FiniteCuts.displacement p i := by
  unfold _root_.LX.Core.FiniteCuts.displacement
  rw [permutation_embed]
  simp [embed]

theorem displacement_outside (W : Window n b) (p : State b) (j : Fin n) (hj : ¬Contains W j) :
    _root_.LX.Core.FiniteCuts.displacement (permutation W p) j=0 := by
  simp [_root_.LX.Core.FiniteCuts.displacement,permutation_outside W p j hj]


end LX.Core.FiniteWindow

end

section
/-! Exact mass and cut-load identities for an embedded finite window. -/
namespace LX.Core.FiniteWindow
open scoped BigOperators
variable {n b : ℕ}

theorem sum_window (W : Window n b) (f : Fin n → ℤ)
    (hzero : ∀ j, ¬Contains W j → f j=0) :
    (∑ j : Fin n, f j)=∑ i : Fin b, f (embed W i) := by
  classical
  let S := Finset.univ.image (embed W)
  have hsub : (∑ j ∈ S, f j)=∑ j : Fin n, f j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hnot
    apply hzero j
    intro h
    obtain ⟨i,rfl⟩ := (contains_iff W j).mp h
    exact hnot (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  rw [← hsub]
  exact Finset.sum_image (fun i _ j _ h => embed_injective W h)

theorem displacement_mass (W : Window n b) (p : State b) :
    (∑ j : Fin n, |_root_.LX.Core.FiniteCuts.displacement (permutation W p) j|)=
      ∑ i : Fin b, |_root_.LX.Core.FiniteCuts.displacement p i| := by
  rw [sum_window W _ (fun j hj => by rw [displacement_outside W p j hj,abs_zero])]
  simp only [displacement_embed]



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
/-! Extract the finite permutation of an invariant physical window. -/
namespace LX.Core.FiniteWindow
variable {n b : ℕ}





theorem embed_restriction (W : Window n b) (p : State n)
    (hW : ∀ j, Contains W (p j) ↔ Contains W j) (i : Fin b) :
    embed W (restriction W p hW i)=p (embed W i) := by
  change ((windowEquiv W) ((windowEquiv W).symm ((p.subtypePerm hW) ((windowEquiv W) i)))).val= _
  rw [Equiv.apply_symm_apply]
  rfl




end LX.Core.FiniteWindow

end

section
namespace LX.FiniteDropBudget
open scoped BigOperators
open LX.Core.FiniteCuts











theorem three_drops_bound_of_pos {n : ℕ} (p : LX.Core.State n) (hn : 0 < n) :
    3*((descendingPositions p).card : ℤ) ≤ (n : ℤ)+
      (∑ i, |_root_.LX.Core.FiniteCuts.displacement p i|)-(inversionNumber p : ℤ)+(backwardUnits p).card-1 := by
  cases n with
  | zero => omega
  | succ k => simpa only [Nat.cast_add,Nat.cast_one] using three_drops_bound p

theorem window_stat_count {n b : ℕ} (W : LX.Core.FiniteWindow.Window n b)
    (p : LX.Core.State b) (P : ℤ → Prop) [DecidablePred P] (hP : ¬P 0) :
    (Finset.univ.filter fun i => P (_root_.LX.Core.FiniteCuts.displacement (LX.Core.FiniteWindow.permutation W p) i)).card=
      (Finset.univ.filter fun i => P (_root_.LX.Core.FiniteCuts.displacement p i)).card := by
  classical
  simp only [Finset.card_filter]
  rw [LX.Core.FiniteWindow.sum_window_nat W _ (by
    intro i hi
    rw [LX.Core.FiniteWindow.displacement_outside W p i hi,ite_eq_right hP])]
  simp only [LX.Core.FiniteWindow.displacement_embed]




end LX.FiniteDropBudget

end

namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
open LX
open LX.FiniteDropBudget
open scoped BigOperators
open LX.Core.FiniteCuts

/-- A fixed initial interval can be removed before applying the drop budget.
All finite statistics are transferred through the actual tail restriction. -/
theorem solution {n : ℕ} (p : LX.Core.State n) (r : ℕ) (hr : r < n)
    (hfix : ∀ i : Fin n,i.val < r → p i=i) :
    3*((descendingPositions p).card : ℤ) ≤ ((n-r : ℕ) : ℤ)+
      (∑ i, |_root_.LX.Core.FiniteCuts.displacement p i|)-(inversionNumber p : ℤ)+(backwardUnits p).card-1 := by
  classical
  let W : LX.Core.FiniteWindow.Window n (n-r) := ⟨r,by omega⟩
  have hW (i : Fin n) : LX.Core.FiniteWindow.Contains W (p i) ↔
      LX.Core.FiniteWindow.Contains W i := by
    change (r ≤ (p i).val ∧ (p i).val < r+(n-r)) ↔
      (r ≤ i.val ∧ i.val < r+(n-r))
    have hi := i.isLt
    have hp := (p i).isLt
    have hsmall : (p i).val < r ↔ i.val < r := by
      constructor
      · intro h
        have he : p i=i := p.injective (hfix (p i) h)
        rwa [he] at h
      · intro h
        rwa [hfix i h]
    omega
  let q := LX.Core.FiniteWindow.restriction W p hW
  have he : LX.Core.FiniteWindow.permutation W q=p := by
    apply Equiv.ext
    intro i
    by_cases hi : LX.Core.FiniteWindow.Contains W i
    · obtain ⟨j,rfl⟩ := (LX.Core.FiniteWindow.contains_iff W i).mp hi
      rw [LX.Core.FiniteWindow.permutation_embed]
      exact LX.Core.FiniteWindow.embed_restriction W p hW j
    · rw [LX.Core.FiniteWindow.permutation_outside W q i hi]
      apply (hfix i _).symm
      have hit := i.isLt
      change ¬(r ≤ i.val ∧ i.val < r+(n-r)) at hi
      omega
  have hdesc := window_stat_count W q (fun z => z < 0) (by omega)
  have hu := window_stat_count W q (fun z => z = -1) (by omega)
  rw [he] at hdesc hu
  have hd (m : ℕ) (s : LX.Core.State m) :
      (Finset.univ.filter fun i => _root_.LX.Core.FiniteCuts.displacement s i < 0)=descendingPositions s := by
    unfold descendingPositions
    apply Finset.filter_congr
    intro i _
    unfold _root_.LX.Core.FiniteCuts.displacement
    omega
  have hb (m : ℕ) (s : LX.Core.State m) :
      (Finset.univ.filter fun i => _root_.LX.Core.FiniteCuts.displacement s i = -1)=backwardUnits s := by
    unfold backwardUnits
    apply Finset.filter_congr
    intro i _
    unfold _root_.LX.Core.FiniteCuts.displacement
    omega
  rw [hd,hd] at hdesc
  rw [hb,hb] at hu
  have hm := LX.Core.FiniteWindow.displacement_mass W q
  have hi := LX.Core.FiniteWindow.inversion_number_window W q
  rw [he] at hm hi
  have hbound := three_drops_bound_of_pos q (by omega : 0 < n-r)
  rwa [← hdesc,← hu,← hm,← hi] at hbound
