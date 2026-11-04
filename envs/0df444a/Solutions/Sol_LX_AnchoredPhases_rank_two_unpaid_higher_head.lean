-- Prove2me | solution 1 for LX.AnchoredPhases.rank_two_unpaid_higher_head
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-03T07:53:08.018207+00:00
-- url     : https://prove2.me/submissions/831eb8bd-e0bd-459e-94be-b57890ff11cf

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
import Definitions.Def_LX_OddWideCutCount
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SecondExcess
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AnchoredPhases_odd_unpaid_second_excess_head_bound
import Theorems.Thm_LX_AnchoredPhases_rank_two_unpaid_head_range
import Theorems.Thm_LX_AnchoredPhases_rank_two_unpaid_minimum_head_no_smaller
import Theorems.Thm_LX_AnchoredPhases_rank_two_unpaid_no_head_predecessor

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
open Classical
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]













theorem odd_unpaid_second_excess_smaller_phase_bound (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    secondExcess p a+1 ≤ ((if HeadPredecessorTerminal p (height p a) then 1 else 0 : ℕ) : ℤ)+
      ((if SmallerHigherAlignedTerminal p (height p a) then 1 else 0 : ℕ) : ℤ) := by
  have hb := odd_unpaid_second_excess_head_bound p a hn hh hmin hunpaid
  split_ifs at hb ⊢ <;> omega









end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open Classical
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem rank_two_unpaid_smaller_aligned_exists (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    SmallerHigherAlignedTerminal p (height p a) := by
  have hK := rank_two_unpaid_no_head_predecessor p a hn hh hmin hR hunpaid
  have hbound := odd_unpaid_second_excess_smaller_phase_bound p a hn hh hmin hunpaid
  have hnonneg : 0 ≤ secondExcess p a := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  by_contra hnot
  rw [ite_eq_right hK,ite_eq_right hnot] at hbound
  omega

/-- No minimum-height head survives the complete odd window count. -/
theorem rank_two_unpaid_head_not_minimum (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : height p a < height p 0 := by
  have hle := hmin 0
  by_contra hnot
  have he : height p 0=height p a := by omega
  exact rank_two_unpaid_minimum_head_no_smaller p a hn hh hR he hunpaid
    (rank_two_unpaid_smaller_aligned_exists p a hn hh hmin hR hunpaid)




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

/-- The head is genuinely an exception in the terminal window: it has
height exactly one above the minimum and a positive small gap. -/
theorem solution (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    height p 0=height p a+1 ∧ 0 < (-p 0).val ∧ (-p 0).val ≤ 3 := by
  have hK := rank_two_unpaid_no_head_predecessor p a hn hh hmin hR hunpaid
  have hbound := odd_unpaid_second_excess_head_bound p a hn hh hmin hunpaid
  have hnonneg : 0 ≤ secondExcess p a := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hT : RelevantTerminalHead p (height p a) := by
    by_contra hnot
    rw [ite_eq_right hK,ite_eq_right hnot] at hbound
    split_ifs at hbound <;> omega
  have hhhead := rank_two_unpaid_head_not_minimum p a hn hh hmin hR hunpaid
  have hhead : height p 0=height p a+1 ∧ 0 < (-p 0).val ∧ (-p 0).val ≤ height p a+3 := by
    rcases hT with hT | hT
    · omega
    · exact hT
  refine ⟨hhead.1,hhead.2.1,?_⟩
  obtain ⟨j,hjlo,hjhi,hj⟩ := rank_two_unpaid_head_range p a hn hh hmin hR hunpaid
  have hjneg : j < 0 := by
    by_contra hnot
    have hjcases : j=0 ∨ j=1 := by omega
    rcases hjcases with h0 | h1
    · have hp0 : p 0=0 := by simpa only [h0,Int.cast_zero] using hj
      simp only [hp0,neg_zero,Fin.val_zero] at hhead
      omega
    · have hp1 : p 0=1 := by simpa only [h1,Int.cast_one] using hj
      have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (show 1<n by omega)]
      have hone : (1 : Fin n) ≠ 0 := by
        intro he; have hv := congrArg Fin.val he; rw [hv1,Fin.val_zero] at hv; omega
      have hneg : (-p 0).val=n-1 := by rw [hp1,Fin.val_neg,ite_eq_right hone,hv1]
      omega
  have hval : ((-j).toNat : ℤ)= -j := Int.toNat_of_nonneg (by omega)
  have hkn : (-j).toNat < n := by omega
  have he : -p 0=((-j).toNat : Fin n) := by
    calc
      -p 0=((-j : ℤ) : Fin n) := by rw [hj,Int.cast_neg]
      _=((((-j).toNat : ℤ)) : Fin n) := congrArg (fun z : ℤ => (z : Fin n)) hval.symm
      _=((-j).toNat : Fin n) := by rw [Int.cast_natCast]
  rw [he,show ((-j).toNat : Fin n).val=(-j).toNat from Nat.mod_eq_of_lt hkn]
  omega
