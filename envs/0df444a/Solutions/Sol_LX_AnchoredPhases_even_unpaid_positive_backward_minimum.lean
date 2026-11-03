-- Prove2me | solution 1 for LX.AnchoredPhases.even_unpaid_positive_backward_minimum
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:59:12.921199+00:00
-- url     : https://prove2.me/submissions/f4b29a59-9cd9-4612-a007-29d3ac417a4a

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
import Definitions.Def_LX_MinimumOffsetCount
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AnchoredPhases_even_minimum_anchor_count
import Theorems.Thm_LX_AnchoredPhases_even_unpaid_rank_at_most_one
import Theorems.Thm_LX_AnchoredPhases_minimum_unpaid_positive_backward
import Theorems.Thm_LX_AnchoredPhases_unpaid_minimum_count_without_head
import Theorems.Thm_LX_AnchoredPhases_unpaid_minimum_offset_count
import Theorems.Thm_LX_AnchoredPhases_zero_surplus_count_le_minimum_offsets

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
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]


theorem raw_offset_mass (p : State n) :
    (∑ i : Fin n,((p i-i : Fin n) : ℤ))=(n : ℤ)*(descendingPositions p).card := by
  have h := clockwise_representative_mass p
  simpa only [clockwise_difference_value] using h


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





theorem cyclic_subtraction_value (u v : Fin n) :
    ((u-v : Fin n) : ℤ)=(u : ℤ)-(v : ℤ)+if u.val < v.val then (n : ℤ) else 0 := by
  have hu := u.isLt
  have hv := v.isLt
  change (((u-v).val : ℕ) : ℤ)=_
  rw [Fin.val_sub]
  by_cases h : u.val < v.val
  · rw [Nat.mod_eq_of_lt (by omega : n-v.val+u.val < n),ite_eq_left h]
    omega
  · have he : n-v.val+u.val=n+(u.val-v.val) := by omega
    rw [he,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega : u.val-v.val < n),ite_eq_right h]
    omega



theorem cyclic_offset_mass (p : State n) (a : Fin n) :
    (∑ i : Fin n, (cyclicOffset p a i : ℤ))=(n : ℤ)*height p a :=
  offset_difference_mass p a


























end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]



theorem mem_minimum_raw_offsets (p : State n) (h : ℕ) (t : Fin n) :
    t ∈ minimumRawOffsets p h ↔ ∃ b : Fin n,height p b=h ∧ p b-b=t := by
  simp only [minimumRawOffsets,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]






end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The height at any threshold, including an unoccupied one, is its
shifted offset mass. -/
theorem shifted_offset_rank_mass (p : State n) (a t : Fin n) :
    (∑ i : Fin n, ((cyclicOffset p a i-t : Fin n) : ℤ))=
      (n : ℤ)*((height p a : ℤ)+rankSurplus p a t.val) := by
  have hc : (∑ i : Fin n,if (cyclicOffset p a i).val < t.val then (n : ℤ) else 0)=
      (n : ℤ)*belowCount p a t.val := by
    rw [← Finset.sum_filter]
    simp [belowCount,mul_comm]
  simp_rw [cyclic_subtraction_value]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,cyclic_offset_mass,hc]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,rankSurplus]
  ring









theorem rank_peak_descending_count (p : State n) (a : Fin n) (R : ℕ)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ R) :
    (descendingPositions p).card ≤ height p a+R := by
  let t : Fin n := -(p a-a)
  have hm := shifted_offset_rank_mass p a t
  have he (i : Fin n) : cyclicOffset p a i-t=p i-i := by dsimp [cyclicOffset,t]; ring
  simp_rw [he] at hm
  rw [raw_offset_mass] at hm
  have hnpos : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hr := hR t
  nlinarith




end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem equal_raw_offset_height (p : State n) (a b : Fin n)
    (he : p a-a=p b-b) : height p a=height p b := by
  have hp : permutation p a=permutation p b := by
    apply Equiv.ext
    intro i
    change p i+(a-p a)=p i+(b-p b)
    linear_combination -he
  simp only [height,hp]



/-- Every remaining even input has its initial position in a minimum
phase. This follows from the sharp count, without a global-energy premise. -/
theorem even_unpaid_head_minimum (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) : height p 0=height p a := by
  by_contra hnot
  have hc := unpaid_minimum_count_without_head p a 0 (by omega) (by omega) hh hmin
    (by simpa using hunpaid) hnot
  have hz := zero_surplus_count_le_minimum_offsets p a hmin
  have hl := even_minimum_anchor_count p a hmin hn
  omega



end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem even_unpaid_minimum_count_exact (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) :
    (minimumRawOffsets p (height p a)).card=height p a+1 := by
  have hu := unpaid_minimum_offset_count p a 0 (by omega) (by omega) hh hmin (by simpa using hunpaid)
  have hz := zero_surplus_count_le_minimum_offsets p a hmin
  have hl := even_minimum_anchor_count p a hmin hn
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

/-- The exact minimum-offset count exhausts all ordinary backward arrows
with positive images. Consequently every such arrow has minimum height. -/
theorem solution (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12)
    (k : Fin n) (hk : k ∈ descendingPositions p) (hpk : p k ≠ 0) :
    height p k=height p a := by
  classical
  by_contra hnot
  let M := minimumRawOffsets p (height p a)
  let D := ((descendingPositions p).erase k).erase (p.symm 0)
  let V := D.image (fun i => p i-i)
  have hcard : M.card=height p a+1 := even_unpaid_minimum_count_exact p a hn hh hmin hunpaid
  have hcover (t : Fin n) (ht : t ∈ M) (ht0 : t ≠ 0) (hth : t ≠ p 0) : t ∈ V := by
    obtain ⟨b,hb,hbt⟩ := (mem_minimum_raw_offsets _ _ _).mp ht
    obtain ⟨i,hi,hpi,hit⟩ := minimum_unpaid_positive_backward p a b 0 (by omega) (by omega)
      hh hmin hb (by simpa using hunpaid) (by rwa [hbt]) (by rwa [hbt])
    have hih : height p i=height p a := (equal_raw_offset_height p i b hit).trans hb
    have hik : i ≠ k := by intro he; rw [he] at hih; exact hnot hih
    have hi0 : i ≠ p.symm 0 := by intro he; apply hpi; rw [he,Equiv.apply_symm_apply]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr ⟨hi0,Finset.mem_erase.mpr ⟨hik,hi⟩⟩,hit.trans hbt⟩
  have hv : V.card ≤ D.card := Finset.card_image_le
  have hd0 : D.card ≤ (descendingPositions p).card-1 := by
    have hc := Finset.card_le_card (Finset.erase_subset (p.symm 0) ((descendingPositions p).erase k))
    rw [Finset.card_erase_of_mem hk] at hc
    exact hc
  have hhead := even_unpaid_head_minimum p a hn hh hmin hunpaid
  by_cases hp0 : p 0=0
  · have heq : permutation p 0=p := by ext i; simp [permutation,hp0]
    change (descendingPositions (permutation p 0)).card=height p a at hhead
    rw [heq] at hhead
    have hs : M ⊆ insert 0 V := by
      intro t ht
      by_cases ht0 : t=0
      · simp [ht0]
      exact Finset.mem_insert_of_mem (hcover t ht ht0 (by rwa [hp0]))
    have hc := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
    omega
  have hj0 : p.symm 0 ≠ 0 := by
    intro he
    have he' := congrArg p he
    simp only [Equiv.apply_symm_apply] at he'
    exact hp0 he'.symm
  have hjd : p.symm 0 ∈ descendingPositions p := by
    rw [mem_descendingPositions,Equiv.apply_symm_apply,Fin.val_zero]
    exact Fin.pos_iff_ne_zero.mpr hj0
  have hjk : p.symm 0 ≠ k := by
    intro he
    apply hpk
    rw [← he,Equiv.apply_symm_apply]
  have hd : D.card=(descendingPositions p).card-2 := by
    dsimp only [D]
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hjk,hjd⟩),Finset.card_erase_of_mem hk]
    omega
  by_cases hz : (0 : Fin n) ∈ M
  · obtain ⟨b,hb,hraw⟩ := (mem_minimum_raw_offsets _ _ _).mp hz
    have hpb : p b=b := sub_eq_zero.mp hraw
    have heq : permutation p b=p := by ext i; simp [permutation,hpb]
    change (descendingPositions (permutation p b)).card=height p a at hb
    rw [heq] at hb
    have hs : M ⊆ V ∪ {0,p 0} := by
      intro t ht
      by_cases ht0 : t=0
      · exact Finset.mem_union_right _ (by simp [ht0])
      by_cases hth : t=p 0
      · exact Finset.mem_union_right _ (by simp [hth])
      exact Finset.mem_union_left _ (hcover t ht ht0 hth)
    have hc := (Finset.card_le_card hs).trans (Finset.card_union_le V {0,p 0})
    have hp := Finset.card_pair_eq_one_or_two (a := (0 : Fin n)) (b := p 0)
    omega
  · have hs : M ⊆ insert (p 0) V := by
      intro t ht
      by_cases hth : t=p 0
      · simp [hth]
      have ht0 : t ≠ 0 := by intro he; exact hz (he ▸ ht)
      exact Finset.mem_insert_of_mem (hcover t ht ht0 hth)
    have hc := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
    have hR := even_unpaid_rank_at_most_one p a hn hh hmin hunpaid
    have hb := rank_peak_descending_count p a 1 hR
    omega
