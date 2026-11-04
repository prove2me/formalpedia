-- Prove2me | solution 1 for LX.AnchoredPhases.odd_unpaid_positive_excess_initial_pair
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-03T07:51:29.74679+00:00
-- url     : https://prove2.me/submissions/cdaca82b-1b24-450d-8257-b118f96af46e

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
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_ClockwiseLiftCount
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_OddPairedHigherPayment
import Definitions.Def_LX_OddWideCutCount
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ReverseDual
import Definitions.Def_LX_ReverseDualPhases
import Definitions.Def_LX_SecondExcess
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection
import Theorems.Thm_LX_AnchoredPhases_odd_unpaid_second_excess_head_bound
import Theorems.Thm_LX_AnchoredPhases_odd_unpaid_small_head_aligned_bound
import Theorems.Thm_LX_Core_WordReflection_mirror_letter_eval

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
/-!
A balanced phase lift of an actual permutation, with subset majorization.
We minimize the nonnegative integer sum of squared displacements over all
balanced lifts and phases. Phase shifts yield majorization directly, without
assuming an affine inversion formula or a pre-existing bounded lift.
-/
namespace LX.Core.AffineLift
open scoped BigOperators







theorem canonical_lift {n : ℕ} (p : State n) :
    IsLift p 0 (fun i => (p.symm i : ℤ) - (i : ℤ)) := by
  constructor
  · rw [Finset.sum_sub_distrib]
    have h := Equiv.sum_comp p.symm (fun i : Fin n => (i : ℤ))
    rw [h]
    simp
  · intro i
    simp [Int.ModEq]




















end LX.Core.AffineLift

end

section
/-! Signed affine crossing data obtained from an actual balanced phase lift.
The row-sum identity is proved from bijectivity of endpoint residues. -/
namespace LX.Core.AffineLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem cast_eq_of_modEq {a b : ℤ} (h : Int.ModEq (n : ℤ) a b) :
    (a : Fin n) = (b : Fin n) := by
  apply Fin.ext
  rw [Fin.val_intCast, Fin.val_intCast]
  exact congrArg Int.toNat h




















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
/-! Displacements of finite permutations define balanced affine lifts.
The canonical finite lift has phase zero. -/
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {b : ℕ}



theorem canonical_lift (p : State b) : AffineLift.IsLift p.symm 0 (_root_.LX.Core.FiniteCuts.displacement p) := by
  unfold _root_.LX.Core.FiniteCuts.displacement
  simpa only [Equiv.symm_symm] using AffineLift.canonical_lift p.symm


end LX.Core.FiniteCuts

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



theorem clockwise_representative_bounds (p : State n) (i : Fin n) :
    (i : ℤ) ≤ clockwiseRepresentative p i ∧ clockwiseRepresentative p i < (i : ℤ)+n := by
  have hi := i.isLt
  have hp := (p i).isLt
  unfold clockwiseRepresentative
  split_ifs <;> omega

theorem clockwise_representative_modEq (p : State n) (i : Fin n) :
    Int.ModEq (n : ℤ) (clockwiseRepresentative p i) (p i : ℤ) := by
  unfold clockwiseRepresentative
  split_ifs <;> simp [Int.ModEq]



theorem clockwise_representative_mass (p : State n) :
    (∑ i : Fin n, (clockwiseRepresentative p i-(i : ℤ))) =
      (n : ℤ)*((descendingPositions p).card : ℤ) := by
  have hp : (∑ i : Fin n, _root_.LX.Core.FiniteCuts.displacement p i)=0 := (canonical_lift p).1
  have hpoint (i : Fin n) : clockwiseRepresentative p i-(i : ℤ) =
      _root_.LX.Core.FiniteCuts.displacement p i+(if (p i).val < i.val then (n : ℤ) else 0) := by
    unfold clockwiseRepresentative _root_.LX.Core.FiniteCuts.displacement
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, hp, zero_add]
  rw [← Finset.sum_filter]
  simp [descendingPositions, mul_comm]




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
open LX.Core.FiniteCuts LX.AffineScan
variable {n : ℕ} [NeZero n]



theorem clockwise_difference_value (q : State n) (i : Fin n) :
    clockwiseRepresentative q i-(i : ℤ)=((q i-i : Fin n) : ℤ) := by
  have hb := clockwise_representative_bounds q i
  have hc := LX.Core.AffineLift.cast_eq_of_modEq (clockwise_representative_modEq q i)
  have hm : ((clockwiseRepresentative q i-(i : ℤ) : ℤ) : Fin n)=q i-i := by
    simp only [Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self,hc]
  have hh := congrArg (fun x : Fin n => (x : ℤ)) hm
  simp only [Fin.val_intCast] at hh
  rw [Int.emod_eq_of_lt (by omega) (by omega),Int.toNat_of_nonneg (by omega)] at hh
  exact hh














end LX.AnchoredPhases

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
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts LX.AffineScan
variable {n : ℕ} [NeZero n]

theorem offset_difference_mass (p : State n) (a : Fin n) :
    (∑ i : Fin n, ((p i-i-(p a-a) : Fin n) : ℤ))=(n : ℤ)*height p a := by
  have hm := clockwise_representative_mass (permutation p a)
  simp_rw [clockwise_difference_value] at hm
  have he (i : Fin n) : permutation p a i-i=p i-i-(p a-a) := by
    change p i+(a-p a)-i=p i-i-(p a-a)
    abel
  simpa only [he,height] using hm


end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]









theorem cyclic_offset_mass (p : State n) (a : Fin n) :
    (∑ i : Fin n, (cyclicOffset p a i : ℤ))=(n : ℤ)*height p a :=
  offset_difference_mass p a


























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







end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open Classical
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]



theorem odd_unpaid_terminal_head_aligned_bound (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 3)
    (hhead : height p 0=height p a)
    (_hg1 : 0 < (-p 0).val) (hg2 : (-p 0).val ≤ height p a+3)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    secondExcess p a+1 ≤
      ((if ∃ b,HigherAlignedTerminal p (height p a) b then 1 else 0 : ℕ) : ℤ) :=
  odd_unpaid_small_head_aligned_bound p a hn hh hmin hR hhead hg2 hunpaid

theorem odd_unpaid_terminal_head_zero_excess (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 3)
    (hhead : height p 0=height p a)
    (hg1 : 0 < (-p 0).val) (hg2 : (-p 0).val ≤ height p a+3)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : secondExcess p a=0 := by
  have hb := odd_unpaid_terminal_head_aligned_bound p a hn hh hmin hR hhead hg1 hg2 hunpaid
  have hnonneg : 0 ≤ secondExcess p a := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  split_ifs at hb <;> omega




end LX.AnchoredPhases

end

section
/-! Reflection in the edge between positions zero and one. It exchanges L/R,
fixes X, and agrees with the word symmetry already used by the lower proof. -/
namespace LX.Core.WordReflection
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



@[simp] theorem reflection_apply (i : Fin n) : reflection i=1-i := rfl

@[simp] theorem reflection_twice (i : Fin n) : reflection (reflection i)=i := by
  simp only [reflection_apply]
  abel

@[simp] theorem reflection_square : (reflection : State n)*reflection=1 := by
  apply Equiv.ext
  intro i
  exact reflection_twice i



end LX.Core.WordReflection

end

section
namespace LX
open LX.Core.WordReflection
variable {n : ℕ} [NeZero n]



 theorem _root_.LX.UploadHelpers.ReverseDual.reflection_inv : (reflection : State n)⁻¹=reflection := by
  apply Equiv.ext
  intro i
  rfl

@[simp] theorem reverseDual_one : reverseDual (1 : State n)=1 := by
  simp [reverseDual]

theorem reverseDual_mul (p q : State n) : reverseDual (p*q)=reverseDual q*reverseDual p := by
  simp only [reverseDual,mul_inv_rev]
  simp only [mul_assoc,← mul_assoc (reflection : State n) reflection,reflection_square,one_mul]

@[simp] theorem reverseDual_twice (p : State n) : reverseDual (reverseDual p)=p := by
  simp only [reverseDual,mul_inv_rev,_root_.LX.UploadHelpers.ReverseDual.reflection_inv,inv_inv]
  simp only [mul_assoc,← mul_assoc (reflection : State n) reflection,reflection_square,one_mul,mul_one]

theorem reverseDual_letter (c : Letter) : reverseDual (eval (n := n) [c])=eval [c] := by
  have he : (eval (n := n) [c])⁻¹=reflection*eval [c]*reflection := by
    simpa only [eval,List.map_cons,List.map_nil,LX.Core.eval_cons,LX.Core.eval_nil,mul_one,
      LX.Core.Letter.eval_inverse] using mirror_letter_eval (n := n) c.toCore
  rw [reverseDual,he]
  simp only [mul_assoc,← mul_assoc (reflection : State n) reflection,reflection_square,one_mul,mul_one]

theorem eval_reverse_dual (w : List Letter) : eval (n := n) w.reverse=reverseDual (eval w) := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [List.reverse_cons,eval_append,ih]
    have he : eval (n := n) (c::w)=eval [c]*eval w := by
      simpa only [List.singleton_append] using eval_append (n := n) [c] w
    rw [he,reverseDual_mul,reverseDual_letter]

theorem reverse_dual_sorting_word (p : State n) (w : List Letter)
    (hw : reverseDual p*eval w=1) : p*eval w.reverse=1 := by
  have he := congrArg reverseDual hw
  rw [reverseDual_mul,reverseDual_twice,reverseDual_one,← eval_reverse_dual] at he
  exact mul_eq_one_comm.mp he



end LX

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.WordReflection
variable {n : ℕ} [NeZero n]



theorem reverse_dual_raw_offset (p : State n) (i : Fin n) :
    reverseDual p (dualPosition p i)-dualPosition p i=p i-i := by
  have he : reverseDual p (dualPosition p i)=reflection i := by
    simp only [reverseDual,dualPosition,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,
      reflection_twice,Equiv.symm_apply_apply]
  rw [he]
  simp only [dualPosition,Equiv.Perm.mul_apply,reflection_apply]
  ring

theorem reverse_dual_cyclic_offset (p : State n) (a i : Fin n) :
    cyclicOffset (reverseDual p) (dualPosition p a) (dualPosition p i)=cyclicOffset p a i := by
  simp only [cyclicOffset,reverse_dual_raw_offset]

theorem reverse_dual_height (p : State n) (a : Fin n) :
    height (reverseDual p) (dualPosition p a)=height p a := by
  have hm := cyclic_offset_mass (reverseDual p) (dualPosition p a)
  rw [← Equiv.sum_comp (dualPosition p) (fun i : Fin n =>
    (cyclicOffset (reverseDual p) (dualPosition p a) i : ℤ))] at hm
  simp only [reverse_dual_cyclic_offset] at hm
  rw [cyclic_offset_mass] at hm
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have he := mul_left_cancel₀ hn hm
  omega

theorem reverse_dual_below_count (p : State n) (a : Fin n) (t : ℕ) :
    belowCount (reverseDual p) (dualPosition p a) t=belowCount p a t := by
  classical
  simp only [belowCount,Finset.card_filter]
  rw [← Equiv.sum_comp (dualPosition p) (fun i : Fin n =>
    if (cyclicOffset (reverseDual p) (dualPosition p a) i).val < t then (1 : ℕ) else 0)]
  simp only [reverse_dual_cyclic_offset]

theorem reverse_dual_rank_surplus (p : State n) (a : Fin n) (t : ℕ) :
    rankSurplus (reverseDual p) (dualPosition p a) t=rankSurplus p a t := by
  simp only [rankSurplus,reverse_dual_below_count]

theorem reverse_dual_second_excess (p : State n) (a : Fin n) :
    secondExcess (reverseDual p) (dualPosition p a)=secondExcess p a := by
  simp only [secondExcess,reverse_dual_rank_surplus]

theorem reverse_dual_minimum_height (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) :
    ∀ b,height (reverseDual p) (dualPosition p a) ≤ height (reverseDual p) b := by
  intro b
  obtain ⟨c,rfl⟩ := (dualPosition p).surjective b
  rw [reverse_dual_height,reverse_dual_height]
  exact hmin c





end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem odd_unpaid_positive_excess_head_fixed (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 3)
    (hpos : 0 < secondExcess p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : p 0=0 := by
  have hb := odd_unpaid_second_excess_exception_bound p a hn hh hmin hunpaid
  have hK : HeadPredecessorTerminal p (height p a) := by
    by_contra hnot
    rw [ite_eq_right hnot] at hb
    split_ifs at hb <;> omega
  obtain ⟨hhead,hg1,hg2⟩ := hK
  by_contra hp0
  have hgp : 0 < (-p 0).val := Fin.pos_iff_ne_zero.mpr (neg_ne_zero.mpr hp0)
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  have hv := Fin.val_add_eq_ite (-p 0) (1 : Fin n)
  have he : -p 0+1=(1 : Fin n)-p 0 := by ring
  rw [he,hv1] at hv
  have hgn := (-p 0).isLt
  have hg : (-p 0).val ≤ height p a+3 := by split_ifs at hv <;> omega
  have hz := odd_unpaid_terminal_head_zero_excess p a hn hh hmin hR hhead hgp hg hunpaid
  omega










end LX.AnchoredPhases

end

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Applying the same count to the reflected inverse fixes both initial
positions whenever a positive second excess remains. -/
theorem solution (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 3)
    (hpos : 0 < secondExcess p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : p 0=0 ∧ p 1=1 := by
  have hp0 := odd_unpaid_positive_excess_head_fixed p a hn hh hmin hR hpos hunpaid
  have hdual : ¬ ∃ w : List Letter,reverseDual p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9 := by
    rintro ⟨w,hw,hprice⟩
    exact hunpaid ⟨w.reverse,reverse_dual_sorting_word p w hw,by simpa using hprice⟩
  have hheight := reverse_dual_height p a
  have hq0 := odd_unpaid_positive_excess_head_fixed (reverseDual p) (dualPosition p a)
    (by omega) (by omega) (reverse_dual_minimum_height p a hmin)
    (fun t => by rw [reverse_dual_rank_surplus]; exact hR t)
    (by rw [reverse_dual_second_excess]; exact hpos) hdual
  have he : (1 : Fin n)-p.symm 1=0 := by
    simpa only [reverseDual,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,
      LX.Core.WordReflection.reflection_apply,sub_zero] using hq0
  have hi : p.symm 1=1 := by linear_combination -he
  refine ⟨hp0,?_⟩
  have hp1 := p.apply_symm_apply 1
  rwa [hi] at hp1
