-- Prove2me | solution 1 for LX.AnchoredPhases.odd_unpaid_three_rank_geometry
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-03T07:53:52.471108+00:00
-- url     : https://prove2.me/submissions/c9f4a934-499e-4ba0-badc-932d4078e658

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
import Definitions.Def_LX_AnchorReserveRigidity
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_MinimumEnergyPhases
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_OddPairedHigherPayment
import Definitions.Def_LX_OddWideCutCount
import Definitions.Def_LX_PairCoreGeometry
import Definitions.Def_LX_PermutationCode
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PrunedLift
import Definitions.Def_LX_SecondExcess
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Theorems.Thm_LX_AnchoredPhases_minimum_count_minus_high_count
import Theorems.Thm_LX_AnchoredPhases_odd_unpaid_four_rank_geometry
import Theorems.Thm_LX_AnchoredPhases_odd_unpaid_second_excess_head_bound
import Theorems.Thm_LX_AnchoredPhases_second_excess_count

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
namespace LX.Core.WordReflection
end LX.Core.WordReflection
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.CycleGeometry
end LX.CycleGeometry
namespace LX.EventGeometry
end LX.EventGeometry
namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
namespace LX.FiniteJoin
end LX.FiniteJoin
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.LiftedScan
end LX.LiftedScan
namespace LX.MatchingGeometry
end LX.MatchingGeometry
namespace LX.PairCore
end LX.PairCore
namespace LX.Small4
end LX.Small4
namespace LX.Small5
end LX.Small5
namespace LX.Small6
end LX.Small6
namespace List
end List

section
/-! Compatibility aliases for core if-then-else lemmas renamed after Lean 4.33.1.
The source proof bodies use the newer names; these aliases preserve their types.
-/
namespace LX
universe u

theorem ite_eq_left {α : Sort u} {p : Prop} {inst : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h

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
/-! Restrict a permutation and its lift to an invariant union of cycles.
Balance of the retained lift is stated separately from invariance. -/
namespace LX.Core.PrunedLift
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem permutation_apply (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (i : Fin n) :
    permutation p S hS i=if i ∈ S then p i else i := rfl

@[simp] theorem permutation_symm_apply (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (i : Fin n) :
    (permutation p S hS).symm i=if i ∈ S then p.symm i else i := rfl

end LX.Core.PrunedLift

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
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]













@[simp] theorem mem_endpoints (events : List (Event n)) (i : Fin n) :
    i ∈ endpoints events ↔ ∃ e ∈ events, i=e.1 ∨ i=e.2 := by
  simp [endpoints]






end LX.Core.ZeroGap

end

section
namespace LX.PairCore
open scoped BigOperators
variable {n : ℕ}







@[simp] theorem permutation_apply (q : State n) (i : Fin n) :
    permutation q i=if q (q i)=i then q i else i := by
  simp [permutation,positions]












end LX.PairCore

namespace LX.AnchoredPhases
variable {n : ℕ} [NeZero n]


end LX.AnchoredPhases

end

section
/-! A constructive enumeration of permutations. Checking one word per code
avoids a quadratic search through a finite set of evaluated words. -/
namespace LX.Core









@[simp] theorem decode_encode {n : ℕ} (p : State n) : decode (encode p) = p := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih => simp only [encode, decode, ih, Prod.mk.eta, Equiv.symm_apply_apply]




end LX.Core

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- At an actual peak, the triangular excess is contained in the same
second-excess sum used by the terminal cut count. -/
theorem rank_peak_second_excess (p : State n) (a r : Fin n) (R : ℕ)
    (hmin : ∀ b,height p a ≤ height p b) (hRpos : 0 < R)
    (hpeak : rankSurplus p a r.val=R) :
    ((R : ℤ)-1)*(R-2) ≤ 2*secondExcess p a := by
  have hb := minimum_count_minus_high_count p a r R hmin hRpos hpeak
  rw [← second_excess_count p a hmin] at hb
  exact hb





end LX.AnchoredPhases

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

theorem odd_unpaid_second_excess_exception_bound (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    secondExcess p a+1 ≤ ((if HeadPredecessorTerminal p (height p a) then 1 else 0 : ℕ) : ℤ)+
      ((if ∃ b,HigherAlignedTerminal p (height p a) b then 1 else 0 : ℕ) : ℤ) := by
  have hb := odd_unpaid_second_excess_smaller_phase_bound p a hn hh hmin hunpaid
  by_cases hs : SmallerHigherAlignedTerminal p (height p a)
  · rw [ite_eq_left hs] at hb
    obtain ⟨b,c,hb',_⟩ := hs
    have hj : ∃ b,HigherAlignedTerminal p (height p a) b := ⟨b,hb'⟩
    simpa only [ite_eq_left hj] using hb
  · rw [ite_eq_right hs] at hb
    split_ifs at hb ⊢ <;> omega

theorem odd_unpaid_second_excess_le_one (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : secondExcess p a ≤ 1 := by
  have hb := odd_unpaid_second_excess_exception_bound p a hn hh hmin hunpaid
  split_ifs at hb <;> omega





end LX.AnchoredPhases

end

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The peak-four branch is impossible. The remaining odd inputs have
either a binary-high profile (peak two), or exactly one rank-three
thresholds. All conditions are extracted from the actual input. -/
theorem solution (hn5 : 5 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ∃ a r : Fin n,∃ R : ℕ,6 < n ∧ GlobalMinimum p a ∧ height p a+1=m ∧
      (∀ b,height p a ≤ height p b) ∧ 2 ≤ R ∧ R ≤ 3 ∧
      rankSurplus p a r.val=R ∧ (∀ t : Fin n,rankSurplus p a t.val ≤ R) ∧
      ((R=2 ∧ secondExcess p a=0) ∨ (R=3 ∧ secondExcess p a=1)) ∧
      (R : ℤ)*(R-2) ≤ anchorReserve p a ∧ anchorReserve p a ≤ (height p a : ℤ) := by
  obtain ⟨a,r,R,hnlarge,ha,hh,hmin,hRlo,hRhi,hpeak,hR,_,hres,hresup⟩ :=
    odd_unpaid_four_rank_geometry hn5 p m hn hunpaid
  have hQ := odd_unpaid_second_excess_le_one p a (by omega) (by omega) hmin hunpaid
  have htri := rank_peak_second_excess p a r R hmin (by omega) hpeak
  have hthree : R ≤ 3 := by
    by_contra hnot
    have hfour : R=4 := by omega
    rw [hfour] at htri
    norm_num at htri
    omega
  refine ⟨a,r,R,hnlarge,ha,hh,hmin,hRlo,hthree,hpeak,hR,?_,hres,hresup⟩
  have hc : R=2 ∨ R=3 := by omega
  rcases hc with hc | hc
  · refine Or.inl ⟨hc,?_⟩
    unfold secondExcess
    apply Finset.sum_eq_zero
    intro t _
    have ht := hR t
    rw [hc] at ht
    omega
  · refine Or.inr ⟨hc,?_⟩
    rw [hc] at htri
    norm_num at htri
    omega
