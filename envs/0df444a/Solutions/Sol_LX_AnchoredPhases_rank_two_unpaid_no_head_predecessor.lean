-- Prove2me | solution 1 for LX.AnchoredPhases.rank_two_unpaid_no_head_predecessor
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-03T07:51:29.786441+00:00
-- url     : https://prove2.me/submissions/1c484566-6d04-46f9-bd12-d9b775141452

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
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_OddPairedHigherPayment
import Definitions.Def_LX_OddWideCutCount
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SecondExcess
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AnchoredPhases_odd_unpaid_small_head_aligned_bound
import Theorems.Thm_LX_AnchoredPhases_rank_two_unpaid_aligned_minimum_head_geometry
import Theorems.Thm_LX_AnchoredPhases_rank_two_unpaid_head_predecessor_values

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCoordinates
end LX.Core.FiniteCoordinates
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
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.PairCore
end LX.PairCore
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
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]



theorem rank_two_unpaid_aligned_minimum_head (p : State n) (a b : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hhead : height p 0=height p a)
    (hb : HigherAlignedTerminal p (height p a) b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : p 0=1 :=
  (rank_two_unpaid_aligned_minimum_head_geometry p a b hn hh hR hhead hb hunpaid).1





end LX.AnchoredPhases

end

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open Classical
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The predecessor exception is impossible in the remaining rank-two
profile. Both possible head values force the aligned exception, which
in turn would force the incompatible value one. -/
theorem solution (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ¬ HeadPredecessorTerminal p (height p a) := by
  intro hK
  have hp := rank_two_unpaid_head_predecessor_values p a hn hh hmin hR hK hunpaid
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  have hsmall : (-p 0).val ≤ height p a+3 := by
    rcases hp with hp | hp
    · simp only [hp,neg_zero,Fin.val_zero]; omega
    · rw [hp,neg_neg,hv1]; omega
  have hbound := odd_unpaid_small_head_aligned_bound p a hn hh hmin
    (fun t => (hR t).trans (by omega)) hK.1 hsmall hunpaid
  have hnonneg : 0 ≤ secondExcess p a := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hJ : ∃ b,HigherAlignedTerminal p (height p a) b := by
    by_contra hnot
    rw [ite_eq_right hnot] at hbound
    omega
  obtain ⟨b,hb⟩ := hJ
  have hp1 := rank_two_unpaid_aligned_minimum_head p a b hn hh hR hK.1 hb hunpaid
  rcases hp with hp | hp
  · have hv := congrArg Fin.val (hp1.symm.trans hp)
    rw [hv1,Fin.val_zero] at hv
    omega
  · have hone : (1 : Fin n) ≠ 0 := by
      intro he; have hv := congrArg Fin.val he; rw [hv1,Fin.val_zero] at hv; omega
    have hv := congrArg Fin.val (hp1.symm.trans hp)
    rw [hv1,Fin.val_neg,ite_eq_right hone,hv1] at hv
    omega
